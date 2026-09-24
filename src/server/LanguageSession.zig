//! What the language listener says to one editor: the Language Server
//! Protocol handler for a connection. See "Development server", "Draft" and
//! "Definition" in CONTEXT.md.
//!
//! A `LanguageSession` keeps the drafts the editor has open and parses them for
//! their syntax errors and for which predicate a position names. Everything
//! it says about a predicate comes from the database and the loaded files,
//! read on the engine task through `Engine.Call`. The session also watches
//! the engine for changes and publishes the load errors of every file.
//!
//! Two tasks share a session: the connection's, which runs the handlers,
//! and the watcher's, which republishes diagnostics after each change.
//! `mutex` guards what they share.

const std = @import("std");
const Io = std.Io;
const lsp = @import("lsp");
const types = lsp.types;
const offsets = lsp.offsets;
const LiveDatalog = @import("LiveDatalog");
const builtin = @import("builtin");
const Engine = @import("Engine.zig");
const StreamTransport = @import("LanguageListener.zig").StreamTransport;

const LanguageSession = @This();
const log = std.log.scoped(.language);

/// Shown as the source of every diagnostic.
const diagnostic_source = "LiveDatalog";

engine: *Engine,
gpa: std.mem.Allocator,
transport: *lsp.Transport,
/// How positions count characters, as agreed in `initialize`.
encoding: offsets.Encoding = .@"utf-16",
/// Diagnostics are published only once the editor says it is ready.
ready: bool = false,

mutex: Io.Mutex = .init,
/// Open documents by URI, as the editor names them. Keys are owned.
documents: std.array_hash_map.String(Document) = .empty,
/// The engine's load errors as of its last change.
load_errors: []const PathError = &.{},
load_errors_arena: std.heap.ArenaAllocator,
/// URIs last published with at least one diagnostic, which must be cleared
/// when they have none. Keys are owned.
published: std.array_hash_map.String(void) = .empty,

/// Told the engine's generation after each change. See `watch`.
changes: Io.Queue(u64),
changes_buffer: [1]u64 = undefined,

const Document = struct {
    /// The draft as the editor holds it now.
    text: []u8,
    version: i32,
    /// The last version of the draft that parsed, and what it parsed to.
    /// Positions are read from it, even when `text` has moved on.
    parsed_text: ?[]u8 = null,
    parsed: ?LiveDatalog.Parsed(LiveDatalog.Program) = null,
    /// Why `text` does not parse, if it does not.
    syntax_error: ?SyntaxError = null,

    const SyntaxError = struct {
        summary: []u8,
        /// Byte offsets into `text`.
        start: usize,
        end: usize,
    };

    fn deinit(self: *Document, gpa: std.mem.Allocator) void {
        gpa.free(self.text);
        self.clearParse(gpa);
        if (self.syntax_error) |syntax_error| gpa.free(syntax_error.summary);
        self.* = undefined;
    }

    fn clearParse(self: *Document, gpa: std.mem.Allocator) void {
        if (self.parsed) |parsed| parsed.deinit();
        if (self.parsed_text) |text| gpa.free(text);
        self.parsed = null;
        self.parsed_text = null;
    }

    /// Parses `text`, keeping the last good parse when it fails.
    fn reparse(self: *Document, gpa: std.mem.Allocator) error{OutOfMemory}!void {
        if (self.syntax_error) |syntax_error| gpa.free(syntax_error.summary);
        self.syntax_error = null;

        var diagnostic: LiveDatalog.Diagnostic = .{};
        const parsed = LiveDatalog.parseProgram(gpa, self.text, &diagnostic) catch |err| {
            if (err == error.OutOfMemory) return error.OutOfMemory;
            const summary = if (diagnostic.expected) |expected|
                try std.fmt.allocPrint(gpa, "{s}, expected {s}", .{ @errorName(err), expected })
            else
                try gpa.dupe(u8, @errorName(err));
            const span = diagnostic.span orelse LiveDatalog.Span{ .start = self.text.len, .end = self.text.len };
            self.syntax_error = .{
                .summary = summary,
                .start = @min(span.start, self.text.len),
                .end = @min(@max(span.end, span.start), self.text.len),
            };
            return;
        };
        errdefer parsed.deinit();
        // The program's names borrow from the text it was parsed from.
        const parsed_text = try gpa.dupe(u8, self.text);
        self.clearParse(gpa);
        self.parsed = parsed;
        self.parsed_text = parsed_text;
    }

    /// The predicate named at `position`, read from the last good parse.
    fn nameAt(self: *const Document, position: types.Position, encoding: offsets.Encoding) ?NameAt {
        const text = self.parsed_text orelse return null;
        const index = offsets.positionToIndex(text, position, encoding);
        const name = self.parsed.?.value.nameAt(index) orelse return null;
        return .{
            .predicate = name.predicate,
            .arity = name.arity,
            .range = offsets.locToRange(text, .{ .start = name.span.start, .end = name.span.end }, encoding),
        };
    }
};

const NameAt = struct {
    predicate: []const u8,
    arity: usize,
    range: types.Range,
};

/// A load error the engine reported for `path`, copied off the engine task.
const PathError = struct {
    path: []const u8,
    load_error: Engine.LoadError,
};

pub fn init(self: *LanguageSession, engine: *Engine, transport: *lsp.Transport) void {
    self.* = .{
        .engine = engine,
        .gpa = engine.gpa,
        .transport = transport,
        .load_errors_arena = .init(engine.gpa),
        .changes = undefined,
    };
    self.changes = .init(&self.changes_buffer);
}

pub fn deinit(self: *LanguageSession) void {
    for (self.documents.keys(), self.documents.values()) |uri, *document| {
        self.gpa.free(uri);
        document.deinit(self.gpa);
    }
    self.documents.deinit(self.gpa);
    for (self.published.keys()) |uri| self.gpa.free(uri);
    self.published.deinit(self.gpa);
    self.load_errors_arena.deinit();
    self.* = undefined;
}

// ---------------------------------------------------------------------------
// Following the engine

/// Asks the engine to tell `changes` about every change. Returns false when
/// it could not, because the engine is stopping or out of memory.
pub fn subscribe(self: *LanguageSession) bool {
    const Subscribe = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = run },
        session: *LanguageSession,
        subscribed: bool = false,

        fn run(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            engine.subscribe(&s.session.changes) catch return;
            s.subscribed = true;
        }
    };
    var subscription: Subscribe = .{ .session = self };
    return subscription.call.perform(self.engine) and subscription.subscribed;
}

pub fn unsubscribe(self: *LanguageSession) void {
    const Unsubscribe = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = run },
        session: *LanguageSession,

        fn run(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            engine.unsubscribe(&s.session.changes);
        }
    };
    var unsubscription: Unsubscribe = .{ .session = self };
    _ = unsubscription.call.perform(self.engine);
}

/// The watcher task: after each change the engine reports, fetches the load
/// errors and republishes every file's diagnostics. Returns once `changes`
/// is closed.
pub fn watch(self: *LanguageSession) Io.Cancelable!void {
    const io = self.engine.io;
    while (true) {
        _ = self.changes.getOne(io) catch |err| switch (err) {
            error.Closed => return,
            error.Canceled => |e| return e,
        };
        self.refreshLoadErrors() catch |err| {
            log.err("cannot read the load errors: {s}", .{@errorName(err)});
            continue;
        };
        try self.mutex.lock(io);
        defer self.mutex.unlock(io);
        self.publishAll() catch |err| switch (err) {
            error.Canceled => |e| return e,
            else => log.err("cannot publish diagnostics: {s}", .{@errorName(err)}),
        };
    }
}

/// Copies the engine's load errors into `load_errors`.
fn refreshLoadErrors(self: *LanguageSession) !void {
    const Snapshot = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = run },
        arena: std.mem.Allocator,
        errors: []PathError = &.{},
        failed: bool = false,

        fn run(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            s.errors = copy(s.arena, engine) catch {
                s.failed = true;
                return;
            };
        }

        fn copy(arena: std.mem.Allocator, engine: *Engine) ![]PathError {
            const copied = try arena.alloc(PathError, engine.errors.count());
            for (copied, engine.errors.keys(), engine.errors.values()) |*to, path, from| {
                to.* = .{ .path = try arena.dupe(u8, path), .load_error = from };
                to.load_error.message = try arena.dupe(u8, from.message);
                to.load_error.summary = try arena.dupe(u8, from.summary);
                if (from.at) |at| to.load_error.at.?.text = try arena.dupe(u8, at.text);
            }
            return copied;
        }
    };
    var arena: std.heap.ArenaAllocator = .init(self.gpa);
    errdefer arena.deinit();
    var snapshot: Snapshot = .{ .arena = arena.allocator() };
    if (!snapshot.call.perform(self.engine)) return error.EngineStopped;
    if (snapshot.failed) return error.OutOfMemory;

    const io = self.engine.io;
    try self.mutex.lock(io);
    defer self.mutex.unlock(io);
    self.load_errors_arena.deinit();
    self.load_errors_arena = arena;
    self.load_errors = snapshot.errors;
}

// ---------------------------------------------------------------------------
// Diagnostics. Callers hold `mutex`, which also keeps two publications for
// one document from overtaking each other.

/// Publishes the diagnostics of every open document and every file with a
/// load error, and clears those of every other document published before.
fn publishAll(self: *LanguageSession) !void {
    if (!self.ready) return;
    var arena_state: std.heap.ArenaAllocator = .init(self.gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var targets: std.array_hash_map.String(void) = .empty;
    for (self.documents.keys()) |uri| try targets.put(arena, uri, {});
    for (self.load_errors) |path_error| {
        if (std.mem.eql(u8, path_error.path, self.engine.root)) continue;
        if (self.documentFor(arena, path_error.path) != null) continue;
        try targets.put(arena, try pathToUri(arena, path_error.path), {});
    }
    for (self.published.keys()) |uri| try targets.put(arena, try arena.dupe(u8, uri), {});
    for (targets.keys()) |uri| try self.publish(arena, uri);
}

/// Publishes the diagnostics of the document at `uri`: its draft's syntax
/// error while it is open, and the load errors of its file. An open draft's
/// syntax stands in for the syntax error its saved file may have.
fn publish(self: *LanguageSession, arena: std.mem.Allocator, uri: []const u8) !void {
    if (!self.ready) return;
    var diagnostics: std.ArrayList(types.Diagnostic) = .empty;
    const document = self.documents.getPtr(uri);
    if (document) |d| if (d.syntax_error) |syntax_error| try diagnostics.append(arena, .{
        .range = offsets.locToRange(d.text, .{ .start = syntax_error.start, .end = syntax_error.end }, self.encoding),
        .severity = .Error,
        .source = diagnostic_source,
        .message = syntax_error.summary,
    });
    if (try uriToPath(arena, uri)) |path| for (self.load_errors) |path_error| {
        if (!std.mem.eql(u8, path_error.path, path)) continue;
        const load_error = path_error.load_error;
        if (document != null and load_error.syntax) continue;
        try diagnostics.append(arena, .{
            .range = if (load_error.at) |at| .{
                .start = .{ .line = at.line, .character = self.columnOf(at.text, at.start) },
                .end = .{ .line = at.line, .character = self.columnOf(at.text, at.end) },
            } else .{ .start = .{ .line = 0, .character = 0 }, .end = .{ .line = 0, .character = 0 } },
            .severity = .Error,
            .source = diagnostic_source,
            .message = load_error.summary,
        });
    };

    try self.transport.writeNotification(
        self.engine.io,
        arena,
        "textDocument/publishDiagnostics",
        types.publish_diagnostics.Params,
        .{
            .uri = uri,
            .version = if (document) |d| d.version else null,
            .diagnostics = diagnostics.items,
        },
        .{ .emit_null_optional_fields = false },
    );

    if (diagnostics.items.len != 0) {
        if (!self.published.contains(uri)) {
            const key = try self.gpa.dupe(u8, uri);
            errdefer self.gpa.free(key);
            try self.published.put(self.gpa, key, {});
        }
    } else if (self.published.fetchSwapRemove(uri)) |removed| {
        self.gpa.free(removed.key);
    }
}

fn columnOf(self: *const LanguageSession, line: []const u8, byte_column: usize) u32 {
    return @intCast(offsets.countCodeUnits(line[0..@min(byte_column, line.len)], self.encoding));
}

/// The URI of the open document for `path`, if one is open.
fn documentFor(self: *const LanguageSession, arena: std.mem.Allocator, path: []const u8) ?[]const u8 {
    for (self.documents.keys()) |uri| {
        const document_path = (uriToPath(arena, uri) catch null) orelse continue;
        if (std.mem.eql(u8, document_path, path)) return uri;
    }
    return null;
}

// ---------------------------------------------------------------------------
// Lifecycle

pub fn initialize(
    self: *LanguageSession,
    _: std.mem.Allocator,
    params: types.InitializeParams,
) types.InitializeResult {
    // Byte offsets need no conversion, so take UTF-8 whenever it is offered.
    if (params.capabilities.general) |general| for (general.positionEncodings orelse &.{}) |encoding| {
        if (encoding == .@"utf-8") self.encoding = .@"utf-8";
    };
    return .{
        .serverInfo = .{ .name = "LiveDatalog" },
        .capabilities = .{
            .positionEncoding = switch (self.encoding) {
                .@"utf-8" => .@"utf-8",
                .@"utf-16" => .@"utf-16",
                .@"utf-32" => .@"utf-32",
            },
            .textDocumentSync = .{ .text_document_sync_options = .{
                .openClose = true,
                .change = .Full,
            } },
            .hoverProvider = .{ .bool = true },
            .definitionProvider = .{ .bool = true },
        },
    };
}

pub fn initialized(self: *LanguageSession, _: std.mem.Allocator, _: types.InitializedParams) !void {
    try self.mutex.lock(self.engine.io);
    self.ready = true;
    self.mutex.unlock(self.engine.io);
    // Have the watcher fetch the load errors and publish them.
    _ = try self.changes.put(self.engine.io, &.{0}, 0);
}

pub fn shutdown(_: *LanguageSession, _: std.mem.Allocator, _: void) ?void {
    return null;
}

pub fn exit(_: *LanguageSession, _: std.mem.Allocator, _: void) void {}

/// The session sends no requests, so any response is unasked for.
pub fn onResponse(_: *LanguageSession, _: std.mem.Allocator, _: lsp.JsonRPCMessage.Response) void {}

// ---------------------------------------------------------------------------
// Drafts

pub fn @"textDocument/didOpen"(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    params: types.TextDocument.DidOpenParams,
) !void {
    const io = self.engine.io;
    try self.mutex.lock(io);
    defer self.mutex.unlock(io);

    const document = params.textDocument;
    const entry = try self.documents.getOrPut(self.gpa, document.uri);
    if (entry.found_existing) {
        entry.value_ptr.deinit(self.gpa);
    } else {
        entry.key_ptr.* = self.gpa.dupe(u8, document.uri) catch |err| {
            self.documents.swapRemoveAt(entry.index);
            return err;
        };
    }
    entry.value_ptr.* = .{ .text = &.{}, .version = document.version };
    entry.value_ptr.text = try self.gpa.dupe(u8, document.text);
    try entry.value_ptr.reparse(self.gpa);
    try self.publish(arena, entry.key_ptr.*);
}

pub fn @"textDocument/didChange"(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    params: types.TextDocument.DidChangeParams,
) !void {
    const io = self.engine.io;
    try self.mutex.lock(io);
    defer self.mutex.unlock(io);

    const document = self.documents.getPtr(params.textDocument.uri) orelse return;
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(self.gpa);
    try text.appendSlice(self.gpa, document.text);
    for (params.contentChanges) |change| switch (change) {
        .text_document_content_change_whole_document => |whole| {
            text.clearRetainingCapacity();
            try text.appendSlice(self.gpa, whole.text);
        },
        .text_document_content_change_partial => |partial| {
            const loc = offsets.rangeToLoc(text.items, partial.range, self.encoding);
            try text.replaceRange(self.gpa, loc.start, loc.end - loc.start, partial.text);
        },
    };
    const new_text = try text.toOwnedSlice(self.gpa);
    self.gpa.free(document.text);
    document.text = new_text;
    document.version = params.textDocument.version;
    try document.reparse(self.gpa);
    try self.publish(arena, params.textDocument.uri);
}

pub fn @"textDocument/didClose"(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    params: types.TextDocument.DidCloseParams,
) !void {
    const io = self.engine.io;
    try self.mutex.lock(io);
    defer self.mutex.unlock(io);

    var removed = self.documents.fetchSwapRemove(params.textDocument.uri) orelse return;
    defer self.gpa.free(removed.key);
    removed.value.deinit(self.gpa);
    // What remains are the saved file's load errors, if any.
    try self.publish(arena, params.textDocument.uri);
}

/// The predicate named at `position` of the open document `uri`.
fn nameAt(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    uri: []const u8,
    position: types.Position,
) !?NameAt {
    const io = self.engine.io;
    try self.mutex.lock(io);
    defer self.mutex.unlock(io);
    const document = self.documents.getPtr(uri) orelse return null;
    var name = document.nameAt(position, self.encoding) orelse return null;
    name.predicate = try arena.dupe(u8, name.predicate);
    return name;
}

// ---------------------------------------------------------------------------
// Hover

pub fn @"textDocument/hover"(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    params: types.Hover.Params,
) !?types.Hover {
    const name = try self.nameAt(arena, params.textDocument.uri, params.position) orelse return null;
    const Describe = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = run },
        arena: std.mem.Allocator,
        name: NameAt,
        text: []const u8 = "",
        failed: bool = false,

        fn run(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            s.text = describe(s.arena, engine, s.name.predicate, s.name.arity) catch {
                s.failed = true;
                return;
            };
        }
    };
    var description: Describe = .{ .arena = arena, .name = name };
    if (!description.call.perform(self.engine)) return error.ServerCancelled;
    if (description.failed) return error.OutOfMemory;
    return .{
        .contents = .{ .markup_content = .{ .kind = .markdown, .value = description.text } },
        .range = name.range,
    };
}

/// What the loaded files and the database say about `predicate`/`arity`, as
/// Markdown: whether its facts are base or derived, how many it holds, its
/// schema, and the files that define it. Runs on the engine task.
fn describe(
    arena: std.mem.Allocator,
    engine: *Engine,
    predicate: []const u8,
    arity: usize,
) ![]const u8 {
    var out: Io.Writer.Allocating = .init(arena);
    const writer = &out.writer;

    var has_facts = false;
    var has_rules = false;
    var schemas: std.ArrayList([]const u8) = .empty;
    var files: std.ArrayList([]const u8) = .empty;
    for (try sortedPaths(arena, engine)) |path| {
        const source = engine.files.getPtr(path).?;
        var defines = false;
        var heads = Heads.init(source.parsed.value, predicate, arity);
        while (heads.next()) |head| {
            defines = true;
            switch (head.kind) {
                .fact => has_facts = true,
                .rule => has_rules = true,
                .schema => {
                    const span = source.parsed.value.spans[head.statement];
                    try schemas.append(arena, source.text[span.start..span.end]);
                },
            }
        }
        if (defines) try files.append(arena, engine.relative(path));
    }

    const counts: ?LiveDatalog.FactCount = engine.db.countFacts(predicate, arity) catch |err| switch (err) {
        error.OutOfMemory => |e| return e,
        else => null,
    };
    const base = has_facts or (if (counts) |c| c.base != 0 else false);
    const kind = if (base and has_rules)
        "base and derived"
    else if (has_rules)
        "derived"
    else if (base)
        "base"
    else if (schemas.items.len != 0)
        "declared"
    else
        "not defined in any loaded file";

    try writer.writeAll("**");
    try writeMarkdownEscaped(writer, predicate);
    try writer.print("**/{d} — {s}", .{ arity, kind });
    if (counts) |c| {
        try writer.print("\n\n{d} base fact{s}", .{ c.base, if (c.base == 1) "" else "s" });
        if (has_rules or c.derived != 0)
            try writer.print(", {d} derived fact{s}", .{ c.derived, if (c.derived == 1) "" else "s" });
    }
    for (schemas.items, 0..) |schema, index| {
        // Identical schemas in several files say the same thing once.
        for (schemas.items[0..index]) |earlier| {
            if (std.mem.eql(u8, earlier, schema)) break;
        } else try writer.print("\n\n```datalog\n{s}\n```", .{schema});
    }
    if (files.items.len != 0) {
        try writer.writeAll("\n\nDefined in ");
        for (files.items, 0..) |file, index| {
            if (index != 0) try writer.writeAll(", ");
            try writer.print("`{s}`", .{file});
        }
    }
    return out.written();
}

fn writeMarkdownEscaped(writer: *Io.Writer, text: []const u8) !void {
    for (text) |c| {
        if (std.mem.findScalar(u8, "\\`*_{}[]<>()#+-.!|", c) != null) try writer.writeByte('\\');
        try writer.writeByte(c);
    }
}

// ---------------------------------------------------------------------------
// Go to definition

pub fn @"textDocument/definition"(
    self: *LanguageSession,
    arena: std.mem.Allocator,
    params: types.Definition.Params,
) !?types.Definition.Result {
    const name = try self.nameAt(arena, params.textDocument.uri, params.position) orelse return null;
    const Define = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = run },
        arena: std.mem.Allocator,
        name: NameAt,
        encoding: offsets.Encoding,
        locations: []const types.Location = &.{},
        failed: bool = false,

        fn run(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            s.locations = definitions(s.arena, engine, s.name.predicate, s.name.arity, s.encoding) catch {
                s.failed = true;
                return;
            };
        }
    };
    var define: Define = .{ .arena = arena, .name = name, .encoding = self.encoding };
    if (!define.call.perform(self.engine)) return error.ServerCancelled;
    if (define.failed) return error.OutOfMemory;
    if (define.locations.len == 0) return null;
    return .{ .definition = .{ .locations = define.locations } };
}

/// Where `predicate`/`arity` is defined in the loaded files: every schema
/// declaring it, else every rule whose head it is, else every fact. The
/// locations point into the files as they were loaded, which may be older
/// than what is on disk. Runs on the engine task.
fn definitions(
    arena: std.mem.Allocator,
    engine: *Engine,
    predicate: []const u8,
    arity: usize,
    encoding: offsets.Encoding,
) ![]const types.Location {
    var by_kind: [3]std.ArrayList(types.Location) = @splat(.empty);
    for (try sortedPaths(arena, engine)) |path| {
        const source = engine.files.getPtr(path).?;
        const uri = try pathToUri(arena, path);
        // Names come in source order, so positions advance through the text.
        var position: types.Position = .{ .line = 0, .character = 0 };
        var index: usize = 0;
        var heads = Heads.init(source.parsed.value, predicate, arity);
        while (heads.next()) |head| {
            const start = offsets.advancePosition(source.text, position, index, head.span.start, encoding);
            const end = offsets.advancePosition(source.text, start, head.span.start, head.span.end, encoding);
            position = end;
            index = head.span.end;
            try by_kind[@intFromEnum(head.kind)].append(arena, .{
                .uri = uri,
                .range = .{ .start = start, .end = end },
            });
        }
    }
    for (by_kind) |locations| if (locations.items.len != 0) return locations.items;
    return &.{};
}

/// The statements of a program that define one predicate: its schemas, and
/// the facts and rules whose head it is.
const Heads = struct {
    program: LiveDatalog.Program,
    predicate: []const u8,
    arity: usize,
    index: usize = 0,

    /// In the order `definitions` prefers them.
    const Kind = enum { schema, rule, fact };

    const Head = struct {
        kind: Kind,
        statement: usize,
        /// The head's predicate name, as written.
        span: LiveDatalog.Span,
    };

    fn init(program: LiveDatalog.Program, predicate: []const u8, arity: usize) Heads {
        return .{ .program = program, .predicate = predicate, .arity = arity };
    }

    fn next(self: *Heads) ?Head {
        const names = self.program.names;
        while (self.index < names.len) {
            const name = names[self.index];
            self.index += 1;
            // The first name of a statement is its head's, or its schema's.
            if (self.index > 1 and names[self.index - 2].statement == name.statement) continue;
            if (name.arity != self.arity or !std.mem.eql(u8, name.predicate, self.predicate)) continue;
            const kind: Kind = switch (self.program.statements[name.statement]) {
                .schema => .schema,
                .rule => .rule,
                .fact => .fact,
                .query, .retraction => continue,
            };
            return .{ .kind = kind, .statement = name.statement, .span = name.span };
        }
        return null;
    }
};

fn sortedPaths(arena: std.mem.Allocator, engine: *Engine) ![]const []const u8 {
    const paths = try arena.dupe([]const u8, engine.files.keys());
    std.mem.sort([]const u8, paths, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lessThan);
    return paths;
}

// ---------------------------------------------------------------------------
// URIs

/// `file://` and `path`, percent-encoded.
pub fn pathToUri(arena: std.mem.Allocator, path: []const u8) ![]const u8 {
    var out: Io.Writer.Allocating = .init(arena);
    try out.writer.writeAll("file://");
    // A Windows path needs a slash before its drive letter.
    if (path.len != 0 and path[0] != '/') try out.writer.writeByte('/');
    for (path) |c| switch (c) {
        'A'...'Z', 'a'...'z', '0'...'9', '-', '.', '_', '~', '/' => try out.writer.writeByte(c),
        '\\' => try out.writer.writeByte('/'),
        else => try out.writer.print("%{X:0>2}", .{c}),
    };
    return out.written();
}

/// The path a `file:` URI names, or null for any other URI.
pub fn uriToPath(arena: std.mem.Allocator, uri: []const u8) !?[]const u8 {
    const prefix = "file://";
    if (!std.ascii.startsWithIgnoreCase(uri, prefix)) return null;
    var rest = uri[prefix.len..];
    // Only local files: an empty authority or `localhost`.
    if (std.ascii.startsWithIgnoreCase(rest, "localhost/")) rest = rest["localhost".len..];
    if (rest.len == 0 or rest[0] != '/') return null;
    const path = std.Uri.percentDecodeInPlace(try arena.dupe(u8, rest));
    // `/C:/...` on Windows.
    if (builtin.os.tag == .windows and path.len > 2 and path[2] == ':') return path[1..];
    return path;
}

// ---------------------------------------------------------------------------
// Tests

const testing = std.testing;

test "file URIs round-trip through paths" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const uri = try pathToUri(arena, "/tmp/my data/a#b.dl");
    try testing.expectEqualStrings("file:///tmp/my%20data/a%23b.dl", uri);
    try testing.expectEqualStrings("/tmp/my data/a#b.dl", (try uriToPath(arena, uri)).?);
    try testing.expectEqualStrings("/x.dl", (try uriToPath(arena, "file://localhost/x.dl")).?);
    try testing.expectEqual(@as(?[]const u8, null), try uriToPath(arena, "untitled:Untitled-1"));
}

test "heads are the first name of each defining statement" {
    const source =
        \\schema path(atom, atom).
        \\path(X, Y) :- edge(X, Y).
        \\path(a, b).
        \\q(X) :- path(X, _).
        \\path(a, X)?
        \\path(1, 2, 3).
    ;
    const parsed = try LiveDatalog.parseProgram(testing.allocator, source, null);
    defer parsed.deinit();
    var heads = Heads.init(parsed.value, "path", 2);
    const expected = [_]Heads.Kind{ .schema, .rule, .fact };
    for (expected, 0..) |kind, statement| {
        const head = heads.next().?;
        try testing.expectEqual(kind, head.kind);
        try testing.expectEqual(statement, head.statement);
        try testing.expectEqualStrings("path", source[head.span.start..head.span.end]);
    }
    try testing.expectEqual(@as(?Heads.Head, null), heads.next());
}

/// A watched directory with a running engine, and a session whose output
/// collects in `out`. The session is driven by calling its handlers.
const TestSession = struct {
    tmp: testing.TmpDir,
    root: []u8,
    engine: Engine,
    engine_task: Io.Future(void),
    out: Io.Writer.Allocating,
    in: Io.Reader,
    transport: StreamTransport,
    session: LanguageSession,
    arena: std.heap.ArenaAllocator,

    /// `files` are pairs of name and text.
    fn init(self: *TestSession, files: []const [2][]const u8) !void {
        self.tmp = testing.tmpDir(.{ .iterate = true });
        errdefer self.tmp.cleanup();
        for (files) |file| try self.tmp.dir.writeFile(testing.io, .{ .sub_path = file[0], .data = file[1] });
        var buffer: [std.fs.max_path_bytes]u8 = undefined;
        const len = try self.tmp.dir.realPath(testing.io, &buffer);
        self.root = try testing.allocator.dupe(u8, buffer[0..len]);
        errdefer testing.allocator.free(self.root);

        self.engine.init(testing.allocator, testing.io, self.root);
        self.engine.reloadAll();
        self.engine_task = try testing.io.concurrent(Engine.run, .{&self.engine});
        self.out = .init(testing.allocator);
        self.in = .fixed("");
        self.transport = .init(&self.in, &self.out.writer);
        self.session.init(&self.engine, &self.transport.transport);
        self.arena = .init(testing.allocator);
    }

    fn deinit(self: *TestSession) void {
        self.arena.deinit();
        self.session.deinit();
        self.out.deinit();
        self.engine.stop();
        self.engine_task.await(testing.io);
        self.engine.deinit();
        testing.allocator.free(self.root);
        self.tmp.cleanup();
        self.* = undefined;
    }

    fn uri(self: *TestSession, name: []const u8) ![]const u8 {
        const arena = self.arena.allocator();
        return pathToUri(arena, try std.fs.path.join(arena, &.{ self.root, name }));
    }

    fn open(self: *TestSession, name: []const u8, text: []const u8) !void {
        try self.session.@"textDocument/didOpen"(self.arena.allocator(), .{ .textDocument = .{
            .uri = try self.uri(name),
            .languageId = .{ .custom_value = "datalog" },
            .version = 1,
            .text = text,
        } });
    }

    fn change(self: *TestSession, name: []const u8, version: i32, text: []const u8) !void {
        try self.session.@"textDocument/didChange"(self.arena.allocator(), .{
            .textDocument = .{ .uri = try self.uri(name), .version = version },
            .contentChanges = &.{.{ .text_document_content_change_whole_document = .{ .text = text } }},
        });
    }

    fn hover(self: *TestSession, name: []const u8, line: u32, character: u32) !?[]const u8 {
        const result = try self.session.@"textDocument/hover"(self.arena.allocator(), .{
            .textDocument = .{ .uri = try self.uri(name) },
            .position = .{ .line = line, .character = character },
        }) orelse return null;
        return result.contents.markup_content.value;
    }

    fn definition(self: *TestSession, name: []const u8, line: u32, character: u32) ![]const types.Location {
        const result = try self.session.@"textDocument/definition"(self.arena.allocator(), .{
            .textDocument = .{ .uri = try self.uri(name) },
            .position = .{ .line = line, .character = character },
        }) orelse return &.{};
        return result.definition.locations;
    }

    /// Takes what the session has written so far.
    fn written(self: *TestSession) ![]const u8 {
        const text = try self.arena.allocator().dupe(u8, self.out.written());
        self.out.clearRetainingCapacity();
        return text;
    }
};

fn expectContains(haystack: []const u8, needle: []const u8) !void {
    if (std.mem.find(u8, haystack, needle) == null) {
        std.debug.print("expected to find\n{s}\nin\n{s}\n", .{ needle, haystack });
        return error.TestExpectedContains;
    }
}

test "hover and definition come from the loaded files" {
    var t: TestSession = undefined;
    try t.init(&.{
        .{ "schema.dl", "schema edge(atom, atom).\n" },
        .{ "edges.dl", "edge(a, b). edge(b, c).\n" },
        .{ "rules.dl", "path(X, Y) :- edge(X, Y).\npath(X, Z) :- edge(X, Y), path(Y, Z).\n" },
    });
    defer t.deinit();
    const arena = t.arena.allocator();
    _ = t.session.initialize(arena, .{ .capabilities = .{} });
    try testing.expectEqual(offsets.Encoding.@"utf-16", t.session.encoding);

    // A draft outside the directory: it only names predicates.
    try t.open("elsewhere/query.dl", "path(a, X)?\n  edge(b, 'c')?\nunknown(1)?\n");

    const path = (try t.hover("elsewhere/query.dl", 0, 2)).?;
    try expectContains(path, "**path**/2 — derived");
    try expectContains(path, "0 base facts, 3 derived facts");
    try expectContains(path, "Defined in `rules.dl`");

    const edge = (try t.hover("elsewhere/query.dl", 1, 6)).?;
    try expectContains(edge, "**edge**/2 — base\n\n2 base facts\n\n```datalog\nschema edge(atom, atom).\n```");
    try expectContains(edge, "Defined in `edges.dl`, `schema.dl`");

    const unknown = (try t.hover("elsewhere/query.dl", 2, 0)).?;
    try expectContains(unknown, "not defined in any loaded file");
    try testing.expectEqual(@as(?[]const u8, null), try t.hover("elsewhere/query.dl", 0, 6));
    try testing.expectEqual(@as(?[]const u8, null), try t.hover("unopened.dl", 0, 0));

    // A schema defines edge; rules define path, in every file they are in.
    const edge_definitions = try t.definition("elsewhere/query.dl", 1, 4);
    try testing.expectEqual(@as(usize, 1), edge_definitions.len);
    try testing.expectEqualStrings(try t.uri("schema.dl"), edge_definitions[0].uri);
    try testing.expectEqual(types.Range{
        .start = .{ .line = 0, .character = 7 },
        .end = .{ .line = 0, .character = 11 },
    }, edge_definitions[0].range);

    const path_definitions = try t.definition("elsewhere/query.dl", 0, 0);
    try testing.expectEqual(@as(usize, 2), path_definitions.len);
    try testing.expectEqual(@as(u32, 0), path_definitions[0].range.start.line);
    try testing.expectEqual(@as(u32, 1), path_definitions[1].range.start.line);
    try testing.expectEqual(@as(usize, 0), (try t.definition("elsewhere/query.dl", 2, 0)).len);
}

test "positions count UTF-16 code units unless UTF-8 is offered" {
    var t: TestSession = undefined;
    try t.init(&.{.{ "facts.dl", "'ü'(1). 'ü'(2).\n" }});
    defer t.deinit();
    const arena = t.arena.allocator();
    try t.open("q.dl", "'ü'(X)?");

    _ = t.session.initialize(arena, .{ .capabilities = .{} });
    var found = try t.definition("q.dl", 0, 0);
    try testing.expectEqual(@as(usize, 2), found.len);
    try testing.expectEqual(@as(u32, 8), found[1].range.start.character);
    try testing.expectEqual(@as(u32, 11), found[1].range.end.character);

    _ = t.session.initialize(arena, .{ .capabilities = .{ .general = .{
        .positionEncodings = &.{ .@"utf-16", .@"utf-8" },
    } } });
    try testing.expectEqual(offsets.Encoding.@"utf-8", t.session.encoding);
    found = try t.definition("q.dl", 0, 0);
    try testing.expectEqual(@as(u32, 9), found[1].range.start.character);
    try testing.expectEqual(@as(u32, 13), found[1].range.end.character);
}

test "drafts report syntax errors and keep their last good parse" {
    var t: TestSession = undefined;
    try t.init(&.{
        .{ "a.dl", "p(a).\n" },
        .{ "b.dl", "q(X) :- p(X), not q(X).\n" },
        .{ "c.dl", "r(\n" },
    });
    defer t.deinit();
    const arena = t.arena.allocator();
    _ = t.session.initialize(arena, .{ .capabilities = .{} });

    // Nothing is published before the editor is ready.
    try t.open("a.dl", "p(a).\n");
    try testing.expectEqualStrings("", try t.written());
    try t.session.initialized(arena, .{});

    try t.session.refreshLoadErrors();
    try t.session.publishAll();
    const all = try t.written();
    try expectContains(all, try std.fmt.allocPrint(arena,
        \\{{"uri":"{s}","diagnostics":[{{"range":{{"start":{{"line":0,"character":0}},
    ++
        \\"end":{{"line":0,"character":23}}}},"severity":1,"source":"LiveDatalog","message":"NotStratified"}}]}}
    , .{try t.uri("b.dl")}));
    try expectContains(all, try std.fmt.allocPrint(arena,
        \\{{"uri":"{s}","diagnostics":[{{"range":{{"start":{{"line":1,"character":0}},
    ++
        \\"end":{{"line":1,"character":0}}}},"severity":1,"source":"LiveDatalog",
    ++
        \\"message":"InvalidSyntax, expected a term"}}]}}
    , .{try t.uri("c.dl")}));
    try expectContains(all, try std.fmt.allocPrint(arena,
        \\{{"uri":"{s}","version":1,"diagnostics":[]}}
    , .{try t.uri("a.dl")}));

    // The draft's syntax error replaces the saved file's.
    try t.open("c.dl", "r(1).\nr(");
    try expectContains(try t.written(), "\"version\":1,\"diagnostics\":[{\"range\":{\"start\":{\"line\":1,");
    try t.change("c.dl", 2, "r(1).\n");
    try expectContains(try t.written(), "\"version\":2,\"diagnostics\":[]");

    // Positions come from the last draft that parsed.
    try t.change("a.dl", 2, "  p(a).\np(");
    try expectContains(try t.written(), "InvalidSyntax");
    try expectContains((try t.hover("a.dl", 0, 0)).?, "**p**/1 — base");
    try testing.expectEqual(@as(?[]const u8, null), try t.hover("a.dl", 0, 3));

    // Closing a draft falls back to the saved file's errors.
    try t.session.@"textDocument/didClose"(arena, .{ .textDocument = .{ .uri = try t.uri("c.dl") } });
    try expectContains(try t.written(), "InvalidSyntax, expected a term");
    try t.session.@"textDocument/didClose"(arena, .{ .textDocument = .{ .uri = try t.uri("a.dl") } });
    try expectContains(try t.written(), "\"diagnostics\":[]");

    // A file fixed on disk is cleared once the engine has loaded it.
    try t.tmp.dir.writeFile(testing.io, .{ .sub_path = "c.dl", .data = "r(1).\n" });
    t.engine.post(.{ .changed = try std.fs.path.join(testing.allocator, &.{ t.root, "c.dl" }) });
    try t.session.refreshLoadErrors();
    try t.session.publishAll();
    const cleared = try t.written();
    const c_cleared = try std.fmt.allocPrint(arena, "{{\"uri\":\"{s}\",\"diagnostics\":[]}}", .{try t.uri("c.dl")});
    try expectContains(cleared, c_cleared);
    try t.session.publishAll();
    // Only b.dl is still published.
    try testing.expectEqual(@as(usize, 1), std.mem.count(u8, try t.written(), "publishDiagnostics"));
}
