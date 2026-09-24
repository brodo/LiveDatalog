//! Owns the Datalog database. Everything that touches it runs on the engine
//! task: file changes from the watcher and requests from TCP clients arrive
//! as `Message`s on one queue and are handled in order.
//!
//! Each file is a contributor to the database, named by its path: a fact is
//! present while at least one loaded file asserts it. A file change is applied
//! incrementally when only facts changed: the file's new facts replace its
//! contribution through `setContribution`, which maintains the derived
//! closure. Anything else — a changed rule, a retraction anywhere, a new or deleted
//! file with rules — rebuilds a fresh database from every file, in path
//! order. Either way a change is all-or-nothing: if it fails, the previous
//! database and file versions stay in effect and the error is reported.

const std = @import("std");
const Io = std.Io;
const LiveDatalog = @import("LiveDatalog");
const input = LiveDatalog.input;
const Source = @import("Source.zig");
const protocol = @import("protocol.zig");

const Engine = @This();
const log = std.log.scoped(.engine);

/// How long to wait for more file events before reloading, so that an
/// editor's burst of writes and renames becomes one reload.
const debounce: Io.Duration = .fromMilliseconds(40);
pub const max_file_size = 64 * 1024 * 1024;

pub const Message = union(enum) {
    /// An absolute path that may have changed, owned by `gpa`.
    changed: []u8,
    /// A client request; the engine writes the response and sets `done`.
    request: *Request,
    /// Work to run where the database may be read; see `Call`.
    call: *Call,
    /// Rescan the directory and rebuild from scratch.
    reload,
};

pub const Request = struct {
    line: []const u8,
    response: Io.Writer.Allocating,
    done: Io.Event = .unset,
};

/// A function run on the engine task, for clients that need more of the
/// engine than a request line can ask for. Calls run in order with requests,
/// after the changes that arrived with them.
pub const Call = struct {
    run: *const fn (call: *Call, engine: *Engine) void,
    done: Io.Event = .unset,
    /// False when the engine stopped before it could run the call.
    ran: bool = false,

    /// Posts the call and waits until the engine has run it. Returns whether
    /// it ran.
    pub fn perform(call: *Call, engine: *Engine) bool {
        engine.post(.{ .call = call });
        // Uncancelable: the engine holds a pointer to `call` until done.
        call.done.waitUncancelable(engine.io);
        return call.ran;
    }
};

/// Why a file, or the directory as a whole, failed to load.
pub const LoadError = struct {
    /// As `.status` shows it: where, what, and the offending line.
    message: []u8,
    /// What went wrong, without where: `InvalidSyntax, expected a term`.
    summary: []u8,
    /// Whether the file failed to parse, rather than to run.
    syntax: bool = false,
    /// Where in the file, when the error points into its text.
    at: ?At = null,

    pub const At = struct {
        /// 0-based number of the line the error points into.
        line: u32,
        /// That line's text, without its newline.
        text: []u8,
        /// The offending bytes, as byte columns into `text`.
        start: usize,
        end: usize,
    };

    fn deinit(self: *LoadError, gpa: std.mem.Allocator) void {
        gpa.free(self.message);
        gpa.free(self.summary);
        if (self.at) |at| gpa.free(at.text);
        self.* = undefined;
    }
};

gpa: std.mem.Allocator,
io: Io,
/// Absolute path of the watched directory, without a trailing separator.
root: []const u8,
queue: Io.Queue(Message),
queue_buffer: [256]Message = undefined,

db: LiveDatalog.Jatalog,
/// Every loaded file by absolute path. Keys are owned. Each path is also the
/// contributor its facts are asserted for.
files: std.array_hash_map.String(Source) = .empty,
/// Incremented whenever the database changes.
generation: u64 = 0,
/// Load errors by path (the root for errors not tied to one file).
errors: std.array_hash_map.String(LoadError) = .empty,
/// Set when bookkeeping could not keep up (out of memory); the engine then
/// reloads everything.
needs_reload: bool = false,
/// Queues told after every change to the files, the database or the load
/// errors. Only the engine task touches this list; see `subscribe`.
subscribers: std.ArrayList(*Io.Queue(u64)) = .empty,

pub fn init(self: *Engine, gpa: std.mem.Allocator, io: Io, root: []const u8) void {
    self.* = .{
        .gpa = gpa,
        .io = io,
        .root = root,
        .queue = undefined,
        .db = .init(gpa),
    };
    self.queue = .init(&self.queue_buffer);
}

pub fn deinit(self: *Engine) void {
    self.clearFiles();
    self.files.deinit(self.gpa);
    for (self.errors.keys(), self.errors.values()) |key, *value| {
        self.gpa.free(key);
        value.deinit(self.gpa);
    }
    self.errors.deinit(self.gpa);
    self.subscribers.deinit(self.gpa);
    self.db.deinit();
    self.* = undefined;
}

/// Posts a message from any thread other than the engine's. Blocks while the
/// queue is full. A message the engine will never see is disposed of.
pub fn post(self: *Engine, message: Message) void {
    self.queue.putOneUncancelable(self.io, message) catch switch (message) {
        .changed => |path| self.gpa.free(path),
        .request => |request| {
            request.response.writer.writeAll("Error: server is shutting down\n\n") catch |err|
                log.err("cannot answer request: {s}", .{@errorName(err)});
            request.done.set(self.io);
        },
        .call => |call| call.done.set(self.io),
        .reload => {},
    };
}

/// Has `queue` told the generation after every change to the files, the
/// database or the load errors, until `unsubscribe`. Only a `Call` may
/// subscribe, since only the engine task touches the list. A full queue is
/// not waited for: its reader has a change to catch up with already.
pub fn subscribe(self: *Engine, queue: *Io.Queue(u64)) error{OutOfMemory}!void {
    try self.subscribers.append(self.gpa, queue);
}

pub fn unsubscribe(self: *Engine, queue: *Io.Queue(u64)) void {
    for (self.subscribers.items, 0..) |subscriber, index| if (subscriber == queue) {
        _ = self.subscribers.swapRemove(index);
        return;
    };
}

fn notify(self: *Engine) void {
    for (self.subscribers.items) |queue| {
        // A closed queue's reader is going away and will unsubscribe.
        _ = queue.put(self.io, &.{self.generation}, 0) catch |err|
            log.debug("cannot notify a subscriber: {s}", .{@errorName(err)});
    }
}

/// Makes `run` return once the queued messages are handled.
pub fn stop(self: *Engine) void {
    self.queue.close(self.io);
}

/// The engine task.
pub fn run(self: *Engine) void {
    var dirty: std.array_hash_map.String(void) = .empty;
    defer {
        for (dirty.keys()) |path| self.gpa.free(path);
        dirty.deinit(self.gpa);
    }
    var requests: std.ArrayList(Message) = .empty;
    defer requests.deinit(self.gpa);

    while (true) {
        const first = self.queue.getOne(self.io) catch return;
        var reload = false;
        self.collect(first, &dirty, &requests, &reload);

        if (dirty.count() != 0 or reload) {
            // Let the burst finish, then take everything that arrived.
            self.io.sleep(debounce, .awake) catch return;
            var batch: [64]Message = undefined;
            while (true) {
                const n = self.queue.get(self.io, &batch, 0) catch 0;
                if (n == 0) break;
                for (batch[0..n]) |message| self.collect(message, &dirty, &requests, &reload);
            }
        }

        var changed = reload or self.needs_reload or dirty.count() != 0;
        if (reload or self.needs_reload) {
            self.reloadAll();
        } else if (dirty.count() != 0) {
            self.applyPaths(dirty.keys());
        }
        for (dirty.keys()) |path| self.gpa.free(path);
        dirty.clearRetainingCapacity();

        // Requests are answered after the changes that arrived with them.
        const generation = self.generation;
        for (requests.items) |message| switch (message) {
            .request => |request| {
                protocol.handle(self, request.line, &request.response.writer) catch |err|
                    log.err("cannot answer request: {s}", .{@errorName(err)});
                request.done.set(self.io);
            },
            .call => |call| {
                call.run(call, self);
                call.ran = true;
                call.done.set(self.io);
            },
            .changed, .reload => unreachable,
        };
        requests.clearRetainingCapacity();
        // A `.reload` request rebuilds too.
        if (self.generation != generation) changed = true;
        if (changed) self.notify();
    }
}

fn collect(
    self: *Engine,
    message: Message,
    dirty: *std.array_hash_map.String(void),
    requests: *std.ArrayList(Message),
    reload: *bool,
) void {
    switch (message) {
        .changed => |path| {
            const entry = dirty.getOrPut(self.gpa, path) catch {
                self.gpa.free(path);
                self.needs_reload = true;
                return;
            };
            if (entry.found_existing) self.gpa.free(path);
        },
        .request => |request| requests.append(self.gpa, message) catch {
            request.response.writer.writeAll("Error: OutOfMemory\n\n") catch |err|
                log.err("cannot answer request: {s}", .{@errorName(err)});
            request.done.set(self.io);
        },
        .call => |call| requests.append(self.gpa, message) catch call.done.set(self.io),
        .reload => reload.* = true,
    }
}

pub fn isDatalogPath(path: []const u8) bool {
    return std.mem.endsWith(u8, path, ".dl");
}

/// Whether `path` lies outside hidden directories (`.git`, `.zig-cache`, ...)
/// and dependency folders, which are neither watched nor loaded.
pub fn isWatchedPath(self: *const Engine, path: []const u8) bool {
    var components = std.mem.tokenizeScalar(u8, self.relative(path), std.fs.path.sep);
    while (components.next()) |name| {
        if (name[0] == '.') return false;
        const skipped = [_][]const u8{ "zig-out", "node_modules", "target" };
        for (skipped) |skip| if (std.mem.eql(u8, name, skip)) return false;
    }
    return true;
}

/// `path` relative to the watched directory, for display.
pub fn relative(self: *const Engine, path: []const u8) []const u8 {
    if (path.len > self.root.len and std.mem.startsWith(u8, path, self.root) and
        path[self.root.len] == std.fs.path.sep)
        return path[self.root.len + 1 ..];
    return path;
}

// ---------------------------------------------------------------------------
// Loading

const Change = struct {
    path: []const u8,
    /// The new version; null when the file is gone.
    new: ?Source,
};

const Changes = std.ArrayList(Change);

fn freeChanges(self: *Engine, changes: *Changes) void {
    for (changes.items) |*item| if (item.new) |*new| new.deinit(self.gpa);
    changes.deinit(self.gpa);
}

/// Re-reads `paths` and applies what changed.
fn applyPaths(self: *Engine, paths: []const []const u8) void {
    var changes: Changes = .empty;
    defer self.freeChanges(&changes);
    self.readChanges(paths, &changes) catch return self.fail(error.OutOfMemory);
    if (changes.items.len == 0) return;

    const incremental = for (changes.items) |*item| {
        const old = self.files.getPtr(item.path);
        const new: ?*const Source = if (item.new) |*new| new else null;
        if (!Source.incrementalWith(old, new)) break false;
        if (new) |n| if (n.has_retraction) break false;
    } else !self.anyRetraction();

    var how: []const u8 = "incrementally";
    if (incremental) {
        self.applyIncremental(changes.items) catch |err| {
            log.debug("incremental update failed ({s}); rebuilding", .{@errorName(err)});
            how = "";
        };
    }
    if (!incremental or how.len == 0) {
        how = "by rebuilding";
        var failed: ?[]const u8 = null;
        self.rebuildWith(changes.items, &failed) catch |err| {
            if (err == error.OutOfMemory) self.fail(err);
            return;
        };
    }
    self.commitFiles(changes.items, how);
}

/// Reads and parses each of `paths` that differs from its loaded version.
/// Files that cannot be read or parsed are reported and left out.
fn readChanges(self: *Engine, paths: []const []const u8, changes: *Changes) error{OutOfMemory}!void {
    for (paths) |path| {
        if (!isDatalogPath(path)) continue;
        const cwd = std.Io.Dir.cwd();
        const text = cwd.readFileAlloc(self.io, path, self.gpa, .limited(max_file_size)) catch |err| switch (err) {
            error.FileNotFound, error.NotDir, error.IsDir => {
                self.clearError(path);
                if (self.files.contains(path)) try changes.append(self.gpa, .{ .path = path, .new = null });
                continue;
            },
            error.OutOfMemory => |e| return e,
            else => {
                self.setError("{s}: {s}", .{ self.relative(path), @errorName(err) }, path);
                continue;
            },
        };
        if (self.files.getPtr(path)) |old| if (std.mem.eql(u8, old.text, text)) {
            self.gpa.free(text);
            continue;
        };
        var parse_error: Source.ParseError = undefined;
        var source = Source.parse(self.gpa, text, &parse_error) catch |err| {
            if (err == error.OutOfMemory) {
                self.gpa.free(text);
                return error.OutOfMemory;
            }
            self.setDiagnosticError(path, text, err, parse_error.diagnostic, .syntax);
            self.gpa.free(text);
            continue;
        };
        changes.append(self.gpa, .{ .path = path, .new = source }) catch |err| {
            source.deinit(self.gpa);
            return err;
        };
    }
}

fn anyRetraction(self: *const Engine) bool {
    for (self.files.values()) |source| if (source.has_retraction) return true;
    return false;
}

/// Replaces the contribution of each file in `changes` with its new facts,
/// or withdraws it when the file is gone. All or nothing: a batch of several
/// files is applied to a copy of the database that replaces it only once
/// every file has been applied, and one file's `setContribution` is atomic
/// on its own.
fn applyIncremental(self: *Engine, changes: []const Change) !void {
    if (changes.len == 1) {
        if (try self.contribute(&self.db, changes[0])) self.generation += 1;
        return;
    }
    var db = try self.db.clone();
    errdefer db.deinit();
    var changed = false;
    for (changes) |item| changed = try self.contribute(&db, item) or changed;
    // Swapped in even when no fact moved, since which file asserts which
    // fact may have.
    self.db.deinit();
    self.db = db;
    if (changed) self.generation += 1;
}

fn contribute(self: *Engine, db: *LiveDatalog.Jatalog, item: Change) !bool {
    const facts: []input.Relation = if (item.new) |*new| try new.collectFacts(self.gpa) else &.{};
    defer self.gpa.free(facts);
    return db.setContribution(item.path, facts);
}

/// Builds a fresh database from every loaded file with `changes` applied and
/// swaps it in. On failure the current database is kept, the error is
/// recorded, and `failed` names the file that caused it, if one did.
fn rebuildWith(self: *Engine, changes: []const Change, failed: *?[]const u8) anyerror!void {
    failed.* = null;
    var paths: std.ArrayList([]const u8) = .empty;
    defer paths.deinit(self.gpa);

    for (self.files.keys()) |path| {
        for (changes) |item| {
            if (std.mem.eql(u8, item.path, path)) break;
        } else try paths.append(self.gpa, path);
    }
    for (changes) |item| if (item.new != null) try paths.append(self.gpa, item.path);
    std.mem.sort([]const u8, paths.items, {}, lessThan);

    var db: LiveDatalog.Jatalog = .init(self.gpa);
    errdefer db.deinit();

    for (paths.items) |path| {
        const source = self.versionOf(changes, path);
        var diagnostic: LiveDatalog.Diagnostic = .{};
        var result = db.executeStatements(source.runnable, &diagnostic, path) catch |err| {
            if (err != error.OutOfMemory) {
                const at = if (diagnostic.statement) |position| source.diagnosticFor(position) else diagnostic;
                self.setDiagnosticError(path, source.text, err, at, .run);
                failed.* = path;
            }
            return err;
        };
        result.deinit();
    }
    // Derive now rather than on the first query, so errors surface here.
    db.materialize() catch |err| {
        if (err == error.OutOfMemory) return err;
        self.setError("materializing: {s}", .{@errorName(err)}, self.root);
        return err;
    };

    self.db.deinit();
    self.db = db;
    self.generation += 1;
}

fn versionOf(self: *Engine, changes: []const Change, path: []const u8) *const Source {
    for (changes) |*item| if (std.mem.eql(u8, item.path, path)) return &item.new.?;
    return self.files.getPtr(path).?;
}

/// Moves the new versions in `changes` into `files`, which the database now
/// reflects.
fn commitFiles(self: *Engine, changes: []Change, how: []const u8) void {
    self.clearError(self.root);
    for (changes) |*item| {
        self.clearError(item.path);
        const verb = if (item.new == null) "removed" else "loaded";
        log.info("{s} {s} {s}", .{ verb, self.relative(item.path), how });

        if (self.files.getIndex(item.path)) |index| {
            self.files.values()[index].deinit(self.gpa);
            if (item.new) |new| {
                self.files.values()[index] = new;
            } else {
                const key = self.files.keys()[index];
                self.files.swapRemoveAt(index);
                self.gpa.free(key);
            }
            item.new = null;
        } else if (item.new) |new| {
            const key = self.gpa.dupe(u8, item.path) catch {
                self.needs_reload = true;
                continue;
            };
            self.files.put(self.gpa, key, new) catch {
                self.gpa.free(key);
                self.needs_reload = true;
                continue;
            };
            item.new = null;
        }
    }
}

/// Rescans the directory and rebuilds from every `.dl` file in it. A file
/// that fails to load is reported and left out, so one broken file does not
/// take the others down with it.
pub fn reloadAll(self: *Engine) void {
    self.needs_reload = false;
    var paths: std.array_hash_map.String(void) = .empty;
    defer {
        for (paths.keys()) |path| self.gpa.free(path);
        paths.deinit(self.gpa);
    }
    self.scan(&paths) catch |err| {
        self.setError("scanning {s}: {s}", .{ self.root, @errorName(err) }, self.root);
        return;
    };
    std.mem.sort([]const u8, paths.keys(), {}, lessThan);

    var changes: Changes = .empty;
    defer self.freeChanges(&changes);
    var error_index = self.errors.count();
    while (error_index > 0) {
        error_index -= 1;
        const path = self.errors.keys()[error_index];
        if (!paths.contains(path)) self.clearError(path);
    }
    // With nothing loaded, every file reads as new.
    self.clearFiles();
    self.readChanges(paths.keys(), &changes) catch return self.fail(error.OutOfMemory);

    while (true) {
        var failed: ?[]const u8 = null;
        if (self.rebuildWith(changes.items, &failed)) |_| break else |err| {
            if (err == error.OutOfMemory) return self.fail(err);
        }
        const culprit = failed orelse {
            // Nothing to leave out: start from an empty database.
            self.db.deinit();
            self.db = .init(self.gpa);
            self.generation += 1;
            for (changes.items) |*item| if (item.new) |*new| {
                new.deinit(self.gpa);
                item.new = null;
            };
            return;
        };
        for (changes.items, 0..) |*item, index| if (item.path.ptr == culprit.ptr) {
            item.new.?.deinit(self.gpa);
            _ = changes.orderedRemove(index);
            break;
        };
    }
    // `commitFiles` would clear the errors of the files left out.
    for (changes.items) |*item| {
        self.clearError(item.path);
        const key = self.gpa.dupe(u8, item.path) catch {
            self.needs_reload = true;
            continue;
        };
        self.files.put(self.gpa, key, item.new.?) catch {
            self.gpa.free(key);
            self.needs_reload = true;
            continue;
        };
        item.new = null;
    }
    self.clearError(self.root);
    log.info("loaded {d} file(s), {d} fact(s)", .{ self.files.count(), self.db.state.facts.len() });
}

/// Adds the path of every watched `.dl` file under the root to `paths`, as
/// owned keys. Reads only what never changes after `init`, so any task may
/// call it.
pub fn scan(self: *Engine, paths: *std.array_hash_map.String(void)) !void {
    var dir = try std.Io.Dir.cwd().openDir(self.io, self.root, .{ .iterate = true });
    defer dir.close(self.io);
    var walker = try dir.walk(self.gpa);
    defer walker.deinit();
    while (try walker.next(self.io)) |entry| {
        if (entry.kind != .file or !isDatalogPath(entry.basename)) continue;
        const path = try std.fs.path.join(self.gpa, &.{ self.root, entry.path });
        if (!self.isWatchedPath(path)) {
            self.gpa.free(path);
            continue;
        }
        const slot = paths.getOrPut(self.gpa, path) catch |err| {
            self.gpa.free(path);
            return err;
        };
        if (slot.found_existing) self.gpa.free(path);
    }
}

fn clearFiles(self: *Engine) void {
    for (self.files.keys(), self.files.values()) |key, *value| {
        value.deinit(self.gpa);
        self.gpa.free(key);
    }
    self.files.clearRetainingCapacity();
}

fn lessThan(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.order(u8, a, b) == .lt;
}

fn fail(self: *Engine, err: anyerror) void {
    self.setError("{s}", .{@errorName(err)}, self.root);
    self.needs_reload = true;
}

fn setDiagnosticError(
    self: *Engine,
    path: []const u8,
    text: []const u8,
    err: anyerror,
    diagnostic: LiveDatalog.Diagnostic,
    kind: enum { syntax, run },
) void {
    var message: Io.Writer.Allocating = .init(self.gpa);
    defer message.deinit();
    protocol.writeDiagnostic(&message.writer, self.relative(path), text, err, diagnostic) catch |write_err|
        log.err("cannot format error: {s}", .{@errorName(write_err)});
    const summary = (if (diagnostic.expected) |expected|
        std.fmt.allocPrint(self.gpa, "{s}, expected {s}", .{ @errorName(err), expected })
    else
        self.gpa.dupe(u8, @errorName(err))) catch return;
    var load_error: LoadError = .{
        .message = self.gpa.dupe(u8, message.written()) catch {
            self.gpa.free(summary);
            return;
        },
        .summary = summary,
        .syntax = kind == .syntax,
    };
    if (diagnostic.span) |span| if (span.start <= text.len) {
        const line_start = if (std.mem.findScalarLast(u8, text[0..span.start], '\n')) |newline| newline + 1 else 0;
        const line_end = std.mem.findScalarPos(u8, text, span.start, '\n') orelse text.len;
        if (self.gpa.dupe(u8, text[line_start..line_end])) |line_text| {
            load_error.at = .{
                .line = @intCast(std.mem.count(u8, text[0..line_start], "\n")),
                .text = line_text,
                .start = span.start - line_start,
                // A span running past the line is cut at its end.
                .end = @max(@min(span.end, line_end), span.start) - line_start,
            };
        } else |_| {}
    };
    self.putError(path, load_error);
}

fn setError(self: *Engine, comptime fmt: []const u8, args: anytype, path: []const u8) void {
    const message = std.fmt.allocPrint(self.gpa, fmt, args) catch return;
    const summary = self.gpa.dupe(u8, message) catch {
        self.gpa.free(message);
        return;
    };
    self.putError(path, .{ .message = message, .summary = summary });
}

/// Records `load_error`, taking ownership of it.
fn putError(self: *Engine, path: []const u8, load_error: LoadError) void {
    var owned = load_error;
    log.warn("{s}", .{owned.message});
    const entry = self.errors.getOrPut(self.gpa, path) catch {
        owned.deinit(self.gpa);
        return;
    };
    if (entry.found_existing) {
        entry.value_ptr.deinit(self.gpa);
    } else {
        entry.key_ptr.* = self.gpa.dupe(u8, path) catch {
            self.errors.swapRemoveAt(entry.index);
            owned.deinit(self.gpa);
            return;
        };
    }
    entry.value_ptr.* = owned;
}

fn clearError(self: *Engine, path: []const u8) void {
    var removed = self.errors.fetchSwapRemove(path) orelse return;
    self.gpa.free(removed.key);
    removed.value.deinit(self.gpa);
}

// ---------------------------------------------------------------------------
// Introspection, for the protocol's commands

pub fn writeStatus(self: *Engine, writer: *Io.Writer) !void {
    try writer.print("directory: {s}\ngeneration: {d}\nfiles: {d}\nfacts: {d}\n", .{
        self.root,
        self.generation,
        self.files.count(),
        self.db.state.facts.len(),
    });
    for (self.errors.values()) |load_error| {
        try writer.writeAll("error: ");
        try protocol.writeIndented(writer, load_error.message);
    }
}

pub fn writeFiles(self: *Engine, writer: *Io.Writer) !void {
    const paths = try self.gpa.dupe([]const u8, self.files.keys());
    defer self.gpa.free(paths);
    std.mem.sort([]const u8, paths, {}, lessThan);
    for (paths) |path| try writer.print("{s}\n", .{self.relative(path)});
}

// ---------------------------------------------------------------------------
// Tests

const testing = std.testing;

const TestDir = struct {
    tmp: testing.TmpDir,
    root: []u8,

    fn init() !TestDir {
        var tmp = testing.tmpDir(.{ .iterate = true });
        errdefer tmp.cleanup();
        var buffer: [std.fs.max_path_bytes]u8 = undefined;
        const len = try tmp.dir.realPath(testing.io, &buffer);
        return .{ .tmp = tmp, .root = try testing.allocator.dupe(u8, buffer[0..len]) };
    }

    fn deinit(self: *TestDir) void {
        testing.allocator.free(self.root);
        self.tmp.cleanup();
        self.* = undefined;
    }

    fn write(self: *TestDir, name: []const u8, data: []const u8) !void {
        try self.tmp.dir.writeFile(testing.io, .{ .sub_path = name, .data = data });
    }

    fn path(self: *TestDir, name: []const u8) ![]u8 {
        return std.fs.path.join(testing.allocator, &.{ self.root, name });
    }
};

fn expectAnswer(engine: *Engine, line: []const u8, expected: []const u8) !void {
    var response: Io.Writer.Allocating = .init(testing.allocator);
    defer response.deinit();
    try protocol.handle(engine, line, &response.writer);
    try testing.expectEqualStrings(expected, response.written());
}

fn touch(engine: *Engine, dir: *TestDir, name: []const u8) !void {
    const path = try dir.path(name);
    defer testing.allocator.free(path);
    engine.applyPaths(&.{path});
}

test "loads a directory and follows fact and rule changes" {
    var dir: TestDir = try .init();
    defer dir.deinit();
    try dir.write("edges.dl", "edge(a, b). edge(b, c).");
    try dir.write("rules.dl", "path(X, Y) :- edge(X, Y).\npath(X, Z) :- edge(X, Y), path(Y, Z).\n");
    try dir.write("ignored.txt", "edge(x, y).");

    var engine: Engine = undefined;
    engine.init(testing.allocator, testing.io, dir.root);
    defer engine.deinit();
    engine.reloadAll();
    try testing.expectEqual(@as(usize, 2), engine.files.count());
    try expectAnswer(&engine, "path(a, X)?", "X: b\nX: c\n\n");

    // Facts only: incremental.
    try dir.write("edges.dl", "edge(a, b). edge(b, d).");
    try touch(&engine, &dir, "edges.dl");
    try expectAnswer(&engine, "path(a, X)?", "X: b\nX: d\n\n");

    // A fact asserted by two files survives removal from one of them.
    try dir.write("more.dl", "edge(b, d).");
    try touch(&engine, &dir, "more.dl");
    try dir.write("edges.dl", "edge(a, b).");
    try touch(&engine, &dir, "edges.dl");
    try expectAnswer(&engine, "path(a, X)?", "X: b\nX: d\n\n");

    // A rule change rebuilds.
    try dir.write("rules.dl", "path(X, Y) :- edge(X, Y).");
    try touch(&engine, &dir, "rules.dl");
    try expectAnswer(&engine, "path(a, X)?", "X: b\n\n");

    // A deleted file takes its facts with it.
    try dir.tmp.dir.deleteFile(testing.io, "more.dl");
    try touch(&engine, &dir, "more.dl");
    try expectAnswer(&engine, "edge(b, X)?", "No.\n\n");
    try testing.expectEqual(@as(usize, 2), engine.files.count());
}

test "a broken file keeps its last good version" {
    var dir: TestDir = try .init();
    defer dir.deinit();
    try dir.write("a.dl", "p(a).");

    var engine: Engine = undefined;
    engine.init(testing.allocator, testing.io, dir.root);
    defer engine.deinit();
    engine.reloadAll();

    try dir.write("a.dl", "p(a). p(");
    try touch(&engine, &dir, "a.dl");
    try testing.expectEqual(@as(usize, 1), engine.errors.count());
    try expectAnswer(&engine, "p(X)?", "X: a\n\n");

    // A semantic error in a rebuild keeps the old database too.
    try dir.write("a.dl", "p(a). q(X) :- p(X), not q(X).");
    try touch(&engine, &dir, "a.dl");
    try testing.expectEqual(@as(usize, 1), engine.errors.count());
    try expectAnswer(&engine, "p(X)?", "X: a\n\n");

    try dir.write("a.dl", "p(b).");
    try touch(&engine, &dir, "a.dl");
    try testing.expectEqual(@as(usize, 0), engine.errors.count());
    try expectAnswer(&engine, "p(X)?", "X: b\n\n");
}

test "a full reload leaves out only the broken files" {
    var dir: TestDir = try .init();
    defer dir.deinit();
    try dir.write("a.dl", "p(a).");
    try dir.write("b.dl", "q(X) :- p(X), not q(X).");
    try dir.write("c.dl", "p(");

    var engine: Engine = undefined;
    engine.init(testing.allocator, testing.io, dir.root);
    defer engine.deinit();
    engine.reloadAll();
    try testing.expectEqual(@as(usize, 1), engine.files.count());
    try testing.expectEqual(@as(usize, 2), engine.errors.count());
    try expectAnswer(&engine, "p(X)?", "X: a\n\n");
}

test "retractions force a rebuild in file order" {
    var dir: TestDir = try .init();
    defer dir.deinit();
    try dir.write("a.dl", "p(a). p(b).");
    try dir.write("b.dl", "p(b)~");

    var engine: Engine = undefined;
    engine.init(testing.allocator, testing.io, dir.root);
    defer engine.deinit();
    engine.reloadAll();
    try expectAnswer(&engine, "p(X)?", "X: a\n\n");

    try dir.write("a.dl", "p(a). p(b). p(c).");
    try touch(&engine, &dir, "a.dl");
    try expectAnswer(&engine, "p(X)?", "X: a\nX: c\n\n");
}

test "a fact two files assert survives deleting one of them" {
    var dir: TestDir = try .init();
    defer dir.deinit();
    try dir.write("a.dl", "p(shared). p(1). p(a).");
    try dir.write("b.dl", "p(shared). p(1.0).");

    var engine: Engine = undefined;
    engine.init(testing.allocator, testing.io, dir.root);
    defer engine.deinit();
    engine.reloadAll();
    try expectAnswer(&engine, "p(X)?", "X: 1\nX: a\nX: shared\n\n");

    try dir.tmp.dir.deleteFile(testing.io, "a.dl");
    try touch(&engine, &dir, "a.dl");
    try testing.expectEqual(@as(usize, 1), engine.files.count());
    try expectAnswer(&engine, "p(X)?", "X: 1\nX: shared\n\n");

    try dir.tmp.dir.deleteFile(testing.io, "b.dl");
    try touch(&engine, &dir, "b.dl");
    try expectAnswer(&engine, "p(X)?", "No.\n\n");
}
