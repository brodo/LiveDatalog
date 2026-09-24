//! What the browser knows about the database, and the two tasks that keep it
//! current: a *fetcher*, which asks the query listener for whatever the
//! window is missing, and a *watcher*, which follows the database's
//! generation on a connection of its own and tells the fetcher when
//! everything it holds is stale. Either one reconnects every second while
//! the server is away, and what was fetched last stays on show meanwhile.
//!
//! The window reads and writes the model with `mutex` held. Nothing here
//! draws, so the window is told about new data through `wake`.

const std = @import("std");
const Io = std.Io;
const Client = @import("Client.zig");

const Model = @This();
const log = std.log.scoped(.browser);

/// Rows fetched per request, and the unit the rows are cached in.
pub const page_size = 1000;
/// How many pages of the open table are kept; the rest are fetched again
/// when they scroll back into view.
const max_pages = 16;
const retry_delay: Io.Duration = .fromSeconds(1);

gpa: std.mem.Allocator,
io: Io,
address: Io.net.IpAddress,
/// Tells the window there is something new to show. Called from the tasks.
wake: *const fn (context: ?*anyopaque) void,
wake_context: ?*anyopaque = null,

/// Guards everything below it.
mutex: Io.Mutex = .init,
/// Whether the fetcher's connection is up.
connected: bool = false,
/// The latest generation the watcher reported.
generation: ?u64 = null,
catalog: Catalog = .{},
/// The table the window asks for, and how it is sorted. Set by the window.
selection: ?Selection = null,
/// The rows the window shows, as a half-open range. Set by the window.
visible: [2]usize = .{ 0, 0 },
/// What was fetched for `selection`, once its schema is in.
table: ?Table = null,
/// Counts the changes to `table`: a new schema or a new page.
table_revision: u64 = 0,

/// Wakes the fetcher. Holds at most one pending wake.
fetch_signal: Io.Queue(u8),
fetch_signal_buffer: [1]u8 = undefined,

pub const Predicate = struct {
    name: []const u8,
    arity: usize,
    kind: []const u8,
    facts: usize,
    typed: bool,
};

pub const LoadError = struct {
    file: []const u8,
    line: usize,
    column: usize,
    summary: []const u8,
    message: []const u8,
};

/// The predicates and load errors of one generation.
pub const Catalog = struct {
    arena: ?std.heap.ArenaAllocator = null,
    generation: ?u64 = null,
    predicates: []const Predicate = &.{},
    errors: []const LoadError = &.{},

    /// Frees the catalog and leaves it empty.
    fn reset(self: *Catalog) void {
        if (self.arena) |*arena| arena.deinit();
        self.* = .{};
    }

    pub fn find(self: *const Catalog, name: []const u8, arity: usize) ?*const Predicate {
        for (self.predicates) |*predicate|
            if (predicate.arity == arity and std.mem.eql(u8, predicate.name, name)) return predicate;
        return null;
    }
};

pub const Sort = struct {
    /// 0-based.
    column: usize,
    descending: bool,
};

pub const Selection = struct {
    /// Owned by `gpa`.
    name: []const u8,
    arity: usize,
    sort: ?Sort = null,

    pub fn eql(self: Selection, other: Selection) bool {
        return self.arity == other.arity and std.mem.eql(u8, self.name, other.name) and
            std.meta.eql(self.sort, other.sort);
    }
};

pub const Column = struct {
    /// Null where the schema names no column, or there is no schema.
    name: ?[]const u8,
    /// Null for an untyped predicate.
    type: ?[]const u8,
};

/// One page of rows, each row one cell per column.
pub const Page = struct {
    arena: std.heap.ArenaAllocator,
    rows: []const []const Client.Cell,
};

/// The open table: the schema of `selection` as of `generation`, and the
/// pages fetched so far.
pub const Table = struct {
    arena: std.heap.ArenaAllocator,
    selection: Selection,
    generation: ?u64,
    columns: []const Column,
    pages: std.AutoArrayHashMapUnmanaged(usize, Page) = .empty,

    fn deinit(self: *Table, gpa: std.mem.Allocator) void {
        for (self.pages.values()) |*page| page.arena.deinit();
        self.pages.deinit(gpa);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Row `row`'s cells, or null while its page is not in.
    pub fn row(self: *const Table, index: usize) ?[]const Client.Cell {
        const page = self.pages.get(index / page_size) orelse return null;
        const offset = index % page_size;
        return if (offset < page.rows.len) page.rows[offset] else null;
    }
};

pub fn init(
    self: *Model,
    gpa: std.mem.Allocator,
    io: Io,
    address: Io.net.IpAddress,
    wake: *const fn (?*anyopaque) void,
    wake_context: ?*anyopaque,
) void {
    self.* = .{
        .gpa = gpa,
        .io = io,
        .address = address,
        .wake = wake,
        .wake_context = wake_context,
        .fetch_signal = undefined,
    };
    self.fetch_signal = .init(&self.fetch_signal_buffer);
}

/// Call once both tasks have returned.
pub fn deinit(self: *Model) void {
    self.catalog.reset();
    if (self.table) |*table| table.deinit(self.gpa);
    if (self.selection) |selection| self.gpa.free(selection.name);
    self.* = undefined;
}

/// Opens the table of `name`/`arity`, sorted by `sort`, or does nothing if
/// it is open already. Call with `mutex` held.
pub fn select(self: *Model, name: []const u8, arity: usize, sort: ?Sort) !void {
    if (self.selection) |current| {
        if (current.eql(.{ .name = name, .arity = arity, .sort = sort })) return;
    }
    const owned = try self.gpa.dupe(u8, name);
    if (self.selection) |current| self.gpa.free(current.name);
    self.selection = .{ .name = owned, .arity = arity, .sort = sort };
    self.visible = .{ 0, 0 };
    self.signalFetch();
}

/// Records which rows the window shows. Call with `mutex` held.
pub fn show(self: *Model, from: usize, to: usize) void {
    if (self.visible[0] == from and self.visible[1] == to) return;
    self.visible = .{ from, to };
    self.signalFetch();
}

fn signalFetch(self: *Model) void {
    // A wake already pending covers this one.
    _ = self.fetch_signal.put(self.io, &.{0}, 0) catch |err|
        log.debug("cannot wake the fetcher: {s}", .{@errorName(err)});
}

// ---------------------------------------------------------------------------
// The watcher

/// Follows the database's generation until canceled.
pub fn runWatcher(self: *Model) Io.Cancelable!void {
    while (true) {
        self.watchOnce() catch |err| switch (err) {
            error.Canceled => |e| return e,
            else => log.debug("watch connection lost: {s}", .{@errorName(err)}),
        };
        try self.io.sleep(retry_delay, .awake);
    }
}

fn watchOnce(self: *Model) !void {
    var client: Client = undefined;
    try client.connect(self.gpa, self.io, self.address);
    defer client.close(self.gpa);
    try client.watch();
    while (true) {
        const generation = try client.nextGeneration();
        try self.mutex.lock(self.io);
        self.generation = generation;
        self.mutex.unlock(self.io);
        self.signalFetch();
    }
}

// ---------------------------------------------------------------------------
// The fetcher

/// Fetches what the window is missing until canceled.
pub fn runFetcher(self: *Model) Io.Cancelable!void {
    while (true) {
        self.fetchOnce() catch |err| switch (err) {
            error.Canceled => |e| return e,
            else => log.debug("query connection lost: {s}", .{@errorName(err)}),
        };
        try self.mutex.lock(self.io);
        self.connected = false;
        self.mutex.unlock(self.io);
        self.wake(self.wake_context);
        try self.io.sleep(retry_delay, .awake);
    }
}

fn fetchOnce(self: *Model) !void {
    var client: Client = undefined;
    try client.connect(self.gpa, self.io, self.address);
    defer client.close(self.gpa);
    try self.mutex.lock(self.io);
    self.connected = true;
    self.mutex.unlock(self.io);
    self.wake(self.wake_context);

    while (true) {
        if (!try self.fetchNext(&client)) {
            // Up to date: wait for the window or the watcher to want more.
            _ = try self.fetch_signal.getOne(self.io);
        }
    }
}

/// What the fetcher should fetch next, decided with the lock held.
const Need = union(enum) {
    nothing,
    catalog: ?u64,
    schema: struct { selection: Selection, generation: ?u64, typed: bool },
    page: struct { selection: Selection, generation: ?u64, page: usize },
};

/// Fetches one missing thing. Returns false when nothing is missing.
fn fetchNext(self: *Model, client: *Client) !bool {
    var arena_state: std.heap.ArenaAllocator = .init(self.gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try self.mutex.lock(self.io);
    const need = self.decide(arena) catch |err| {
        self.mutex.unlock(self.io);
        return err;
    };
    self.mutex.unlock(self.io);

    switch (need) {
        .nothing => return false,
        .catalog => |generation| try self.fetchCatalog(client, generation),
        .schema => |schema| try self.fetchSchema(arena, client, schema.selection, schema.generation, schema.typed),
        .page => |page| try self.fetchPage(arena, client, page.selection, page.generation, page.page),
    }
    self.wake(self.wake_context);
    return true;
}

/// Copies what `Need` carries into `arena`, since the window may replace the
/// selection as soon as the lock is released.
fn decide(self: *Model, arena: std.mem.Allocator) !Need {
    if (self.catalog.arena == null or self.catalog.generation != self.generation)
        return .{ .catalog = self.generation };
    const selection = self.selection orelse return .nothing;
    const copy: Selection = .{
        .name = try arena.dupe(u8, selection.name),
        .arity = selection.arity,
        .sort = selection.sort,
    };
    const table = if (self.table) |*t| t else null;
    if (table == null or !table.?.selection.eql(selection) or table.?.generation != self.catalog.generation) {
        const predicate = self.catalog.find(selection.name, selection.arity);
        return .{ .schema = .{
            .selection = copy,
            .generation = self.catalog.generation,
            .typed = if (predicate) |p| p.typed else false,
        } };
    }
    const total = if (self.catalog.find(selection.name, selection.arity)) |p| p.facts else 0;
    const to = @min(self.visible[1], total);
    if (self.visible[0] >= to) return .nothing;
    for (self.visible[0] / page_size..(to - 1) / page_size + 1) |page| {
        if (!table.?.pages.contains(page))
            return .{ .page = .{ .selection = copy, .generation = table.?.generation, .page = page } };
    }
    return .nothing;
}

fn fetchCatalog(self: *Model, client: *Client, generation: ?u64) !void {
    var catalog: Catalog = .{ .arena = .init(self.gpa), .generation = generation };
    errdefer catalog.reset();
    const arena = catalog.arena.?.allocator();

    const predicates = try (try client.request(arena, ".predicates")).expectTable();
    const name = predicates.column("name") orelse return error.UnexpectedResponse;
    const arity = predicates.column("arity") orelse return error.UnexpectedResponse;
    const kind = predicates.column("kind") orelse return error.UnexpectedResponse;
    const facts = predicates.column("facts") orelse return error.UnexpectedResponse;
    const typed = predicates.column("typed") orelse return error.UnexpectedResponse;
    const listed = try arena.alloc(Predicate, predicates.rows.len);
    for (predicates.rows, listed) |row, *predicate| {
        if (row.len != predicates.header.len) return error.UnexpectedResponse;
        predicate.* = .{
            .name = (try Client.decodeCell(arena, row[name])).text,
            .arity = try std.fmt.parseInt(usize, row[arity], 10),
            .kind = row[kind],
            .facts = try std.fmt.parseInt(usize, row[facts], 10),
            .typed = std.mem.eql(u8, row[typed], "true"),
        };
    }
    catalog.predicates = listed;

    const errors = try (try client.request(arena, ".errors")).expectTable();
    const reported = try arena.alloc(LoadError, errors.rows.len);
    for (errors.rows, reported) |row, *load_error| {
        if (row.len != 5) return error.UnexpectedResponse;
        load_error.* = .{
            .file = (try Client.decodeCell(arena, row[0])).text,
            .line = try std.fmt.parseInt(usize, row[1], 10),
            .column = try std.fmt.parseInt(usize, row[2], 10),
            .summary = (try Client.decodeCell(arena, row[3])).text,
            .message = (try Client.decodeCell(arena, row[4])).text,
        };
    }
    catalog.errors = reported;

    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    self.catalog.reset();
    self.catalog = catalog;
}

fn fetchSchema(
    self: *Model,
    scratch: std.mem.Allocator,
    client: *Client,
    selection: Selection,
    generation: ?u64,
    typed: bool,
) !void {
    var table: Table = .{
        .arena = .init(self.gpa),
        .selection = undefined,
        .generation = generation,
        .columns = &.{},
    };
    errdefer table.arena.deinit();
    const arena = table.arena.allocator();
    table.selection = .{
        .name = try arena.dupe(u8, selection.name),
        .arity = selection.arity,
        .sort = selection.sort,
    };

    const columns = try arena.alloc(Column, selection.arity);
    @memset(columns, .{ .name = null, .type = null });
    if (typed) {
        const line = try std.fmt.allocPrint(scratch, ".schema {s}", .{selection.name});
        const schema = try (try client.request(scratch, line)).expectTable();
        for (schema.rows) |row| {
            if (row.len != 3) return error.UnexpectedResponse;
            const position = try std.fmt.parseInt(usize, row[0], 10);
            if (position == 0 or position > columns.len) continue;
            const name = try Client.decodeCell(arena, row[1]);
            columns[position - 1] = .{
                .name = if (name.kind == .empty) null else try arena.dupe(u8, name.text),
                .type = try arena.dupe(u8, (try Client.decodeCell(arena, row[2])).text),
            };
        }
    }
    table.columns = columns;

    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    if (self.table) |*old| old.deinit(self.gpa);
    self.table = table;
    self.table_revision += 1;
}

fn fetchPage(
    self: *Model,
    scratch: std.mem.Allocator,
    client: *Client,
    selection: Selection,
    generation: ?u64,
    page: usize,
) !void {
    var line: std.ArrayList(u8) = .empty;
    try line.print(scratch, ".rows {s}/{d} {d} {d}", .{
        selection.name,
        selection.arity,
        page * page_size,
        page_size,
    });
    if (selection.sort) |sort|
        try line.print(scratch, " by {d} {s}", .{ sort.column + 1, if (sort.descending) "desc" else "asc" });

    var fetched: Page = .{ .arena = .init(self.gpa), .rows = &.{} };
    errdefer fetched.arena.deinit();
    const arena = fetched.arena.allocator();
    const response = try client.request(arena, line.items);
    const rows = switch (response) {
        .table => |table| table.rows,
        // The predicate went away since the catalog was fetched: show
        // nothing until the next generation says so.
        .failure => &.{},
        .text => return error.UnexpectedResponse,
    };
    const decoded = try arena.alloc([]const Client.Cell, rows.len);
    for (rows, decoded) |row, *cells| {
        const out = try arena.alloc(Client.Cell, selection.arity);
        for (out, 0..) |*cell, index|
            cell.* = if (index < row.len) try Client.decodeCell(arena, row[index]) else .{ .kind = .empty, .text = "" };
        cells.* = out;
    }
    fetched.rows = decoded;

    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    // Dropped if the window moved on while this was fetched.
    const table = if (self.table) |*t| t else return fetched.arena.deinit();
    if (!table.selection.eql(selection) or table.generation != generation) return fetched.arena.deinit();
    if (table.pages.count() >= max_pages) evictFarthest(table, page);
    try table.pages.put(self.gpa, page, fetched);
    self.table_revision += 1;
}

/// Drops the cached page farthest from `page`.
fn evictFarthest(table: *Table, page: usize) void {
    var farthest: usize = 0;
    var distance: usize = 0;
    for (table.pages.keys(), 0..) |key, index| {
        const d = if (key > page) key - page else page - key;
        if (d >= distance) {
            distance = d;
            farthest = index;
        }
    }
    table.pages.values()[farthest].arena.deinit();
    table.pages.swapRemoveAt(farthest);
}

test {
    _ = Client;
}
