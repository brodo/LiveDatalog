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
const Graph = @import("Graph.zig");

const Model = @This();
const log = std.log.scoped(.browser);

/// Rows fetched per request, and the unit the rows are cached in.
pub const page_size = 1000;
/// How many pages of the open table are kept; the rest are fetched again
/// when they scroll back into view.
const max_pages = 16;
const retry_delay: Io.Duration = .fromSeconds(1);
/// The most facts the graph draws; the rest of the chosen predicates' facts
/// are left out, and the window says so.
pub const graph_cap = 5000;

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
/// Counts the changes to `table` and `answer`: a new schema, page or
/// answer.
table_revision: u64 = 0,
/// The query the window shows the answers of instead of a predicate, owned
/// by `gpa`. Set by the window.
query: ?[]const u8 = null,
/// What the server last answered to `query`.
answer: ?Answer = null,
/// Whether the window shows the graph, and so wants its facts. Set by the
/// window.
graph_mode: bool = false,
/// The predicates the graph draws, their names owned by `gpa`. Set by the
/// window through `toggleGraph`, and first from the first catalog.
graph_choice: std.ArrayList(Key) = .empty,
graph_choice_ready: bool = false,
/// Counts the changes to `graph_choice`.
graph_choice_revision: u64 = 0,
/// The facts of the chosen predicates, once fetched.
graph: ?GraphData = null,
/// Counts the changes to `graph`.
graph_revision: u64 = 0,

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

/// A predicate, by name and arity.
pub const Key = struct {
    name: []const u8,
    arity: usize,

    pub fn eql(self: Key, name: []const u8, arity: usize) bool {
        return self.arity == arity and std.mem.eql(u8, self.name, name);
    }
};

/// The facts the graph draws, as of one generation and one choice of
/// predicates.
pub const GraphData = struct {
    arena: std.heap.ArenaAllocator,
    generation: ?u64,
    choice_revision: u64,
    predicates: []const Graph.Predicate = &.{},
    facts: []const Graph.Fact = &.{},
    /// How many facts the chosen predicates hold, drawn or not.
    total: usize = 0,
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

/// What the server answered to one query, as of one generation.
pub const Answer = struct {
    arena: std.heap.ArenaAllocator,
    query: []const u8,
    generation: ?u64,
    /// The query's variables.
    header: []const []const u8 = &.{},
    rows: []const []const Client.Cell = &.{},
    /// Why the server refused the query, when it did.
    failure: ?[]const u8 = null,
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
    if (self.answer) |*answer| answer.arena.deinit();
    if (self.query) |query| self.gpa.free(query);
    for (self.graph_choice.items) |key| self.gpa.free(key.name);
    self.graph_choice.deinit(self.gpa);
    if (self.graph) |*graph| graph.arena.deinit();
    self.* = undefined;
}

/// Shows or hides the graph. Call with `mutex` held.
pub fn showGraph(self: *Model, shown: bool) void {
    self.graph_mode = shown;
    self.signalFetch();
}

/// Whether the graph draws `name`/`arity`. Call with `mutex` held.
pub fn graphChosen(self: *const Model, name: []const u8, arity: usize) bool {
    for (self.graph_choice.items) |key| if (key.eql(name, arity)) return true;
    return false;
}

/// Adds `name`/`arity` to the graph, or takes it out. Call with `mutex` held.
pub fn toggleGraph(self: *Model, name: []const u8, arity: usize) !void {
    const found = for (self.graph_choice.items, 0..) |key, index| {
        if (key.eql(name, arity)) break index;
    } else null;
    if (found) |index| {
        self.gpa.free(self.graph_choice.items[index].name);
        _ = self.graph_choice.orderedRemove(index);
    } else {
        const owned = try self.gpa.dupe(u8, name);
        errdefer self.gpa.free(owned);
        try self.graph_choice.append(self.gpa, .{ .name = owned, .arity = arity });
    }
    self.graph_choice_revision += 1;
    self.signalFetch();
}

/// The graph starts with every binary predicate, if their facts fit under
/// the cap, and with nothing otherwise.
fn chooseFirstGraph(self: *Model) !void {
    self.graph_choice_ready = true;
    var binary_facts: usize = 0;
    for (self.catalog.predicates) |predicate| {
        if (predicate.arity == 2) binary_facts += predicate.facts;
    }
    if (binary_facts > graph_cap) return;
    for (self.catalog.predicates) |predicate| {
        if (predicate.arity == 2 and !self.graphChosen(predicate.name, 2)) try self.toggleGraph(predicate.name, 2);
    }
}

/// Shows the answers to `query` until a predicate is selected again, and
/// asks again whenever the database changes. Call with `mutex` held.
pub fn ask(self: *Model, query: []const u8) !void {
    const owned = try self.gpa.dupe(u8, query);
    if (self.query) |old| self.gpa.free(old);
    self.query = owned;
    self.signalFetch();
}

/// Opens the table of `name`/`arity`, sorted by `sort`, or does nothing if
/// it is open already. Call with `mutex` held.
pub fn select(self: *Model, name: []const u8, arity: usize, sort: ?Sort) !void {
    if (self.query) |query| {
        self.gpa.free(query);
        self.query = null;
    }
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
    graph: struct { choice: []const GraphChoice, generation: ?u64, choice_revision: u64 },
    query: struct { text: []const u8, generation: ?u64 },
    schema: struct { selection: Selection, generation: ?u64, typed: bool },
    page: struct { selection: Selection, generation: ?u64, page: usize },
};

/// A chosen predicate as the fetcher asks for it.
const GraphChoice = struct {
    key: Key,
    facts: usize,
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
        .query => |query| try self.fetchAnswer(client, query.text, query.generation),
        .graph => |graph| try self.fetchGraph(arena, client, graph.choice, graph.generation, graph.choice_revision),
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
    if (self.graph_mode) {
        const current = if (self.graph) |*g|
            g.generation == self.catalog.generation and g.choice_revision == self.graph_choice_revision
        else
            false;
        if (current) return .nothing;
        // Asked for in the catalog's order, which is the order the cap cuts in.
        var choice: std.ArrayList(GraphChoice) = .empty;
        for (self.catalog.predicates) |predicate| {
            if (!self.graphChosen(predicate.name, predicate.arity)) continue;
            try choice.append(arena, .{
                .key = .{ .name = try arena.dupe(u8, predicate.name), .arity = predicate.arity },
                .facts = predicate.facts,
            });
        }
        return .{ .graph = .{
            .choice = choice.items,
            .generation = self.catalog.generation,
            .choice_revision = self.graph_choice_revision,
        } };
    }
    if (self.query) |query| {
        const answer = if (self.answer) |*a| a else null;
        if (answer == null or answer.?.generation != self.catalog.generation or
            !std.mem.eql(u8, answer.?.query, query))
        {
            return .{ .query = .{ .text = try arena.dupe(u8, query), .generation = self.catalog.generation } };
        }
        return .nothing;
    }
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
    if (!self.graph_choice_ready) try self.chooseFirstGraph();
}

fn fetchGraph(
    self: *Model,
    scratch: std.mem.Allocator,
    client: *Client,
    choice: []const GraphChoice,
    generation: ?u64,
    choice_revision: u64,
) !void {
    var data: GraphData = .{ .arena = .init(self.gpa), .generation = generation, .choice_revision = choice_revision };
    errdefer data.arena.deinit();
    const arena = data.arena.allocator();
    var predicates: std.ArrayList(Graph.Predicate) = .empty;
    var facts: std.ArrayList(Graph.Fact) = .empty;

    for (choice) |chosen| {
        data.total += chosen.facts;
        const room = graph_cap - facts.items.len;
        if (chosen.key.arity == 0 or room == 0) continue;
        const line = try std.fmt.allocPrint(scratch, ".rows {s}/{d} 0 {d} origin", .{
            chosen.key.name,
            chosen.key.arity,
            room,
        });
        // A predicate gone since the catalog was fetched is left out.
        const table = (try client.request(arena, line)).expectTable() catch continue;
        if (table.header.len != chosen.key.arity + 1) return error.UnexpectedResponse;
        const index: u32 = @intCast(predicates.items.len);
        try predicates.append(arena, .{
            .name = try arena.dupe(u8, chosen.key.name),
            .arity = chosen.key.arity,
            .columns = table.header[0..chosen.key.arity],
        });
        for (table.rows) |row| {
            if (row.len != table.header.len) return error.UnexpectedResponse;
            const values = try arena.alloc(Client.Cell, chosen.key.arity);
            for (values, row[0..chosen.key.arity]) |*value, text| value.* = try Client.decodeCell(arena, text);
            try facts.append(arena, .{
                .predicate = index,
                .values = values,
                .derived = std.mem.eql(u8, row[chosen.key.arity], "derived"),
            });
        }
    }
    data.predicates = predicates.items;
    data.facts = facts.items;

    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    if (self.graph) |*old| old.arena.deinit();
    self.graph = data;
    self.graph_revision += 1;
}

fn fetchAnswer(self: *Model, client: *Client, query: []const u8, generation: ?u64) !void {
    var answer: Answer = .{ .arena = .init(self.gpa), .query = undefined, .generation = generation };
    errdefer answer.arena.deinit();
    const arena = answer.arena.allocator();
    answer.query = try arena.dupe(u8, query);

    const text = std.mem.trim(u8, query, &std.ascii.whitespace);
    if (text.len != 0 and text[0] == '.') {
        // A command could take the connection over, as `.watch` does.
        answer.failure = "only queries can be run here, not commands";
    } else if (text.len != 0) switch (try client.request(arena, text)) {
        .table => |table| {
            answer.header = table.header;
            const rows = try arena.alloc([]const Client.Cell, table.rows.len);
            for (table.rows, rows) |row, *cells| {
                const out = try arena.alloc(Client.Cell, table.header.len);
                for (out, 0..) |*cell, index| cell.* = if (index < row.len)
                    try Client.decodeCell(arena, row[index])
                else
                    .{ .kind = .empty, .text = "" };
                cells.* = out;
            }
            answer.rows = rows;
        },
        .failure => |failure| answer.failure = try std.fmt.allocPrint(arena, "{s} {s}", .{
            failure.name,
            failure.message,
        }),
        .text => return error.UnexpectedResponse,
    };

    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    if (self.answer) |*old| old.arena.deinit();
    self.answer = answer;
    self.table_revision += 1;
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

const testing = std.testing;

fn ignoreWake(_: ?*anyopaque) void {}

test "canceling the tasks stops them while they wait on the server" {
    const io = testing.io;
    var server = try (try Io.net.IpAddress.parse("127.0.0.1", 0)).listen(io, .{ .reuse_address = true });
    defer server.deinit(io);

    var model: Model = undefined;
    model.init(testing.allocator, io, server.socket.address, ignoreWake, null);
    defer model.deinit();
    var fetcher = try io.concurrent(runFetcher, .{&model});
    var watcher = try io.concurrent(runWatcher, .{&model});

    // Neither connection is ever answered, so the fetcher waits for its
    // catalog and the watcher for its first generation until canceled — as
    // they do when the window closes.
    const first = try server.accept(io);
    defer first.close(io);
    const second = try server.accept(io);
    defer second.close(io);
    try io.sleep(.fromMilliseconds(50), .awake);
    try testing.expectError(error.Canceled, fetcher.cancel(io));
    try testing.expectError(error.Canceled, watcher.cancel(io));
}

/// Answers one connection the way the query listener would, from a script:
/// one binary predicate with two facts, no load errors, generation 1, and
/// two answers to `p(X)?`.
fn fakeListener(io: Io, stream: Io.net.Stream) Io.Cancelable!void {
    defer stream.close(io);
    var read_buffer: [1024]u8 = undefined;
    var write_buffer: [1024]u8 = undefined;
    var reader = stream.reader(io, &read_buffer);
    var writer = stream.writer(io, &write_buffer);
    while (true) {
        const line = (reader.interface.takeDelimiter('\n') catch return) orelse return;
        const response = if (std.mem.eql(u8, line, ".watch"))
            "generation 1\n"
        else if (std.mem.eql(u8, line, ".predicates"))
            "ok table 2\nname\tarity\tkind\tfacts\ttyped\nedge\t2\tmixed\t2\tfalse\nnone\t0\tbase\t1\tfalse\n"
        else if (std.mem.eql(u8, line, ".errors"))
            "ok table 0\nfile\tline\tcolumn\terror\tmessage\n"
        else if (std.mem.eql(u8, line, ".rows edge/2 0 5000 origin"))
            "ok table 2\n1\t2\t$origin\na\t'B c'\tbase\n'B c'\ta\tderived\n"
        else if (std.mem.eql(u8, line, "p(X)?"))
            "ok table 2\nX\n'a b'\n-1\n"
        else
            "error InvalidSyntax at column 3, expected a term\n";
        writer.interface.writeAll(response) catch return;
        writer.interface.flush() catch return;
    }
}

/// Waits until `done` holds of the model, for up to a few seconds.
fn waitFor(model: *Model, done: *const fn (*Model) bool) !void {
    for (0..300) |_| {
        try model.mutex.lock(model.io);
        const finished = done(model);
        model.mutex.unlock(model.io);
        if (finished) return;
        try model.io.sleep(.fromMilliseconds(10), .awake);
    }
    return error.Timeout;
}

test "a query's answers are fetched, and commands never reach the server" {
    const io = testing.io;
    var server = try (try Io.net.IpAddress.parse("127.0.0.1", 0)).listen(io, .{ .reuse_address = true });
    defer server.deinit(io);

    var model: Model = undefined;
    model.init(testing.allocator, io, server.socket.address, ignoreWake, null);
    defer model.deinit();
    var fetcher = try io.concurrent(runFetcher, .{&model});
    defer _ = fetcher.cancel(io) catch {};
    var watcher = try io.concurrent(runWatcher, .{&model});
    defer _ = watcher.cancel(io) catch {};
    var connections: Io.Group = .init;
    defer connections.cancel(io);
    for (0..2) |_| try connections.concurrent(io, fakeListener, .{ io, try server.accept(io) });

    const Answered = struct {
        fn check(m: *Model) bool {
            const answer = m.answer orelse return false;
            return std.mem.eql(u8, answer.query, m.query.?);
        }
    };

    try model.mutex.lock(io);
    try model.ask("p(X)?");
    model.mutex.unlock(io);
    try waitFor(&model, Answered.check);
    const answer = model.answer.?;
    try testing.expectEqual(@as(usize, 1), answer.header.len);
    try testing.expectEqualStrings("X", answer.header[0]);
    try testing.expectEqual(@as(usize, 2), answer.rows.len);
    try testing.expectEqualStrings("a b", answer.rows[0][0].text);
    try testing.expectEqual(Client.Cell.Kind.number, answer.rows[1][0].kind);

    try model.mutex.lock(io);
    try model.ask("p(");
    model.mutex.unlock(io);
    try waitFor(&model, Answered.check);
    try testing.expectEqualStrings("InvalidSyntax at column 3, expected a term", model.answer.?.failure.?);

    try model.mutex.lock(io);
    try model.ask(".watch");
    model.mutex.unlock(io);
    try waitFor(&model, Answered.check);
    try testing.expectEqualStrings("only queries can be run here, not commands", model.answer.?.failure.?);
}

test "the graph starts with the binary predicates and fetches their facts with their origin" {
    const io = testing.io;
    var server = try (try Io.net.IpAddress.parse("127.0.0.1", 0)).listen(io, .{ .reuse_address = true });
    defer server.deinit(io);

    var model: Model = undefined;
    model.init(testing.allocator, io, server.socket.address, ignoreWake, null);
    defer model.deinit();
    var fetcher = try io.concurrent(runFetcher, .{&model});
    defer _ = fetcher.cancel(io) catch {};
    var watcher = try io.concurrent(runWatcher, .{&model});
    defer _ = watcher.cancel(io) catch {};
    var connections: Io.Group = .init;
    defer connections.cancel(io);
    for (0..2) |_| try connections.concurrent(io, fakeListener, .{ io, try server.accept(io) });

    try model.mutex.lock(io);
    model.showGraph(true);
    model.mutex.unlock(io);
    try waitFor(&model, struct {
        fn check(m: *Model) bool {
            return m.graph != null;
        }
    }.check);

    try testing.expect(model.graphChosen("edge", 2));
    try testing.expect(!model.graphChosen("none", 0));
    const data = model.graph.?;
    try testing.expectEqual(@as(usize, 1), data.predicates.len);
    try testing.expectEqual(@as(usize, 2), data.facts.len);
    try testing.expectEqual(@as(usize, 2), data.total);
    try testing.expectEqualStrings("'B c'", data.facts[0].values[1].canonical);
    try testing.expectEqualStrings("B c", data.facts[0].values[1].text);
    try testing.expect(!data.facts[0].derived);
    try testing.expect(data.facts[1].derived);
}

test {
    _ = Client;
    _ = @import("Graph.zig");
}
