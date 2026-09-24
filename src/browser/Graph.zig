//! The browser's graph view as data: which nodes and edges the chosen facts
//! make, and where each node is. See "Graph view" in CONTEXT.md.
//!
//! A value is a node, named by its canonical text. A fact of a binary
//! predicate is an edge from its first value to its second, a fact of a unary
//! predicate a tag on its value, and a fact of three or more arguments a fact
//! node with one wire to each argument. Positions come from a force-directed
//! layout that runs a step per frame until it settles, and survive `sync`, so
//! the picture holds still while the facts change around it.
//!
//! Nothing here draws.

const std = @import("std");
const Client = @import("Client.zig");

const Graph = @This();

/// The distance the layout aims for between neighbors, in world units.
pub const spacing: f32 = 90;
/// The layout stops once no node moves further than this in a step.
const settled_step: f32 = 0.3;

gpa: std.mem.Allocator,
/// Holds every node, edge, label and key; replaced whole by `sync`.
arena: std.heap.ArenaAllocator,
nodes: []Node = &.{},
edges: []Edge = &.{},
/// Node indices by key.
index: std.StringHashMapUnmanaged(u32) = .empty,
/// How far a node may move in the next step; the layout cools as it runs.
temperature: f32 = 0,
prng: std.Random.DefaultPrng = .init(0x1a7e),

pub const Node = struct {
    key: []const u8,
    /// What to show: an atom without its quotes, a fact node's predicate.
    label: []const u8,
    kind: Kind,
    x: f32 = 0,
    y: f32 = 0,
    /// Held where it was dropped rather than moved by the layout.
    pinned: bool = false,
    /// For a value, the unary facts it is the argument of; for a fact node,
    /// the fact.
    facts: []const FactRef = &.{},
    degree: u32 = 0,

    pub const Kind = enum { value, fact };
};

/// A fact as `sync` was given it.
pub const FactRef = struct {
    predicate: u32,
    fact: u32,
};

pub const Edge = struct {
    from: u32,
    to: u32,
    predicate: u32,
    /// The fact the edge stands for, as an index into what `sync` was given.
    fact: u32,
    derived: bool,
    /// A wire from a fact node is labeled with its column.
    label: ?[]const u8 = null,
};

/// One predicate of the facts given to `sync`.
pub const Predicate = struct {
    name: []const u8,
    arity: usize,
    /// One name per column, as the table view heads it.
    columns: []const []const u8,
};

/// One fact given to `sync`.
pub const Fact = struct {
    predicate: u32,
    values: []const Client.Cell,
    derived: bool,
};

pub fn init(gpa: std.mem.Allocator) Graph {
    return .{ .gpa = gpa, .arena = .init(gpa) };
}

pub fn deinit(self: *Graph) void {
    self.arena.deinit();
    self.* = undefined;
}

/// Rebuilds the nodes and edges from `facts`. A node that was already there
/// keeps its position and pin; a new one starts beside a neighbor that has a
/// position, or somewhere near the middle.
pub fn sync(self: *Graph, predicates: []const Predicate, facts: []const Fact) !void {
    var arena_state: std.heap.ArenaAllocator = .init(self.gpa);
    errdefer arena_state.deinit();
    const arena = arena_state.allocator();

    var nodes: std.ArrayList(Node) = .empty;
    var edges: std.ArrayList(Edge) = .empty;
    var index: std.StringHashMapUnmanaged(u32) = .empty;
    var tags: std.ArrayList(std.ArrayList(FactRef)) = .empty;

    for (facts, 0..) |fact, fact_index| {
        const predicate = predicates[fact.predicate];
        const ref: FactRef = .{ .predicate = fact.predicate, .fact = @intCast(fact_index) };
        switch (fact.values.len) {
            0 => {},
            1 => {
                const node = try valueNode(arena, &nodes, &index, &tags, fact.values[0]);
                try tags.items[node].append(arena, ref);
            },
            2 => {
                const from = try valueNode(arena, &nodes, &index, &tags, fact.values[0]);
                const to = try valueNode(arena, &nodes, &index, &tags, fact.values[1]);
                try edges.append(arena, .{
                    .from = from,
                    .to = to,
                    .predicate = fact.predicate,
                    .fact = ref.fact,
                    .derived = fact.derived,
                });
            },
            else => {
                // Named by its predicate and values, so that the same fact
                // keeps its place across syncs.
                var key: std.ArrayList(u8) = .empty;
                try key.print(arena, "\x00{s}/{d}", .{ predicate.name, predicate.arity });
                for (fact.values) |value| try key.print(arena, "\t{s}", .{value.canonical});
                const node: u32 = @intCast(nodes.items.len);
                try nodes.append(arena, .{
                    .key = key.items,
                    .label = try arena.dupe(u8, predicate.name),
                    .kind = .fact,
                    .facts = try arena.dupe(FactRef, &.{ref}),
                });
                try tags.append(arena, .empty);
                try index.put(arena, key.items, node);
                for (fact.values, 0..) |value, position| {
                    const to = try valueNode(arena, &nodes, &index, &tags, value);
                    try edges.append(arena, .{
                        .from = node,
                        .to = to,
                        .predicate = fact.predicate,
                        .fact = ref.fact,
                        .derived = fact.derived,
                        .label = if (position < predicate.columns.len)
                            try arena.dupe(u8, predicate.columns[position])
                        else
                            null,
                    });
                }
            },
        }
    }
    for (nodes.items, tags.items) |*node, node_tags| {
        if (node.kind == .value) node.facts = node_tags.items;
    }
    for (edges.items) |edge| {
        nodes.items[edge.from].degree += 1;
        nodes.items[edge.to].degree += 1;
    }

    // Carry positions over, then place what is new.
    var placed = try arena.alloc(bool, nodes.items.len);
    @memset(placed, false);
    var any_new = false;
    for (nodes.items, 0..) |*node, i| {
        const old = self.index.get(node.key) orelse {
            any_new = true;
            continue;
        };
        node.x = self.nodes[old].x;
        node.y = self.nodes[old].y;
        node.pinned = self.nodes[old].pinned;
        placed[i] = true;
    }
    const random = self.prng.random();
    const radius = spacing * @sqrt(@as(f32, @floatFromInt(@max(nodes.items.len, 1))));
    // Twice over the edges: a node next to one placed in the first pass is
    // placed in the second.
    for (0..2) |_| for (edges.items) |edge| {
        const pair = [2][2]u32{ .{ edge.from, edge.to }, .{ edge.to, edge.from } };
        for (pair) |p| if (!placed[p[0]] and placed[p[1]]) {
            const angle = random.float(f32) * std.math.tau;
            nodes.items[p[0]].x = nodes.items[p[1]].x + @cos(angle) * spacing;
            nodes.items[p[0]].y = nodes.items[p[1]].y + @sin(angle) * spacing;
            placed[p[0]] = true;
        };
    };
    for (nodes.items, placed) |*node, was_placed| if (!was_placed) {
        node.x = (random.float(f32) - 0.5) * radius;
        node.y = (random.float(f32) - 0.5) * radius;
    };

    self.arena.deinit();
    self.arena = arena_state;
    self.nodes = nodes.items;
    self.edges = edges.items;
    self.index = index;
    if (any_new) self.reheat();
}

fn valueNode(
    arena: std.mem.Allocator,
    nodes: *std.ArrayList(Node),
    index: *std.StringHashMapUnmanaged(u32),
    tags: *std.ArrayList(std.ArrayList(FactRef)),
    value: Client.Cell,
) !u32 {
    const slot = try index.getOrPut(arena, value.canonical);
    if (slot.found_existing) return slot.value_ptr.*;
    const node: u32 = @intCast(nodes.items.len);
    const key = try arena.dupe(u8, value.canonical);
    slot.key_ptr.* = key;
    slot.value_ptr.* = node;
    try nodes.append(arena, .{
        .key = key,
        .label = if (value.canonical.ptr == value.text.ptr) key else try arena.dupe(u8, value.text),
        .kind = .value,
    });
    try tags.append(arena, .empty);
    return node;
}

/// Starts the layout moving again, as after a change or a drag.
pub fn reheat(self: *Graph) void {
    self.temperature = spacing;
}

/// Unpins every node and lays the graph out again.
pub fn relayout(self: *Graph) void {
    for (self.nodes) |*node| node.pinned = false;
    self.reheat();
}

pub fn settled(self: *const Graph) bool {
    return self.temperature < settled_step;
}

/// Moves every unpinned node one step along the forces on it: neighbors
/// attract, every node repels those near it, and a weak pull keeps the whole
/// near the origin. Repulsion only reaches a few spacings, which is what
/// keeps a step linear in the number of nodes rather than quadratic.
pub fn step(self: *Graph) !void {
    if (self.settled() or self.nodes.len == 0) return;
    const gpa = self.gpa;
    const count = self.nodes.len;
    const force = try gpa.alloc([2]f32, count);
    defer gpa.free(force);
    @memset(force, .{ 0, 0 });

    // Repulsion, between nodes in neighboring cells of a grid.
    const grid_size = spacing * 2.5;
    const order = try gpa.alloc(u32, count);
    defer gpa.free(order);
    const keys = try gpa.alloc(u64, count);
    defer gpa.free(keys);
    for (self.nodes, keys, order, 0..) |node, *key, *slot, i| {
        key.* = cellKey(@intFromFloat(@floor(node.x / grid_size)), @intFromFloat(@floor(node.y / grid_size)));
        slot.* = @intCast(i);
    }
    std.mem.sort(u32, order, keys, struct {
        fn lessThan(k: []u64, a: u32, b: u32) bool {
            return k[a] < k[b];
        }
    }.lessThan);
    const sorted = try gpa.alloc(u64, count);
    defer gpa.free(sorted);
    for (order, sorted) |node, *key| key.* = keys[node];

    for (self.nodes, 0..) |a, i| {
        const cx: i32 = @intFromFloat(@floor(a.x / grid_size));
        const cy: i32 = @intFromFloat(@floor(a.y / grid_size));
        var dy: i32 = -1;
        while (dy <= 1) : (dy += 1) {
            var dx: i32 = -1;
            while (dx <= 1) : (dx += 1) {
                const key = cellKey(cx + dx, cy + dy);
                var at = std.sort.lowerBound(u64, sorted, key, orderU64);
                while (at < count and sorted[at] == key) : (at += 1) {
                    const j = order[at];
                    if (j == i) continue;
                    const b = self.nodes[j];
                    var ddx = a.x - b.x;
                    var ddy = a.y - b.y;
                    var distance_squared = ddx * ddx + ddy * ddy;
                    if (distance_squared < 0.01) {
                        // On top of each other: push apart in some direction.
                        ddx = @as(f32, @floatFromInt(i % 7)) - 3 + 0.5;
                        ddy = @as(f32, @floatFromInt(j % 5)) - 2 + 0.5;
                        distance_squared = ddx * ddx + ddy * ddy;
                    }
                    const push = spacing * spacing / distance_squared;
                    force[i][0] += ddx * push;
                    force[i][1] += ddy * push;
                }
            }
        }
    }
    // Attraction along edges.
    for (self.edges) |edge| {
        if (edge.from == edge.to) continue;
        const a = self.nodes[edge.from];
        const b = self.nodes[edge.to];
        const ddx = b.x - a.x;
        const ddy = b.y - a.y;
        const distance = @sqrt(ddx * ddx + ddy * ddy) + 0.01;
        const pull = distance / spacing;
        force[edge.from][0] += ddx * pull;
        force[edge.from][1] += ddy * pull;
        force[edge.to][0] -= ddx * pull;
        force[edge.to][1] -= ddy * pull;
    }
    // A weak pull to the middle, so separate pieces do not drift apart.
    var moved: f32 = 0;
    for (self.nodes, force) |*node, *f| {
        f[0] -= node.x * 0.02;
        f[1] -= node.y * 0.02;
        if (node.pinned) continue;
        const length = @sqrt(f[0] * f[0] + f[1] * f[1]);
        if (length < 0.0001) continue;
        const distance = @min(length, self.temperature);
        node.x += f[0] / length * distance;
        node.y += f[1] / length * distance;
        moved = @max(moved, distance);
    }
    self.temperature = @min(self.temperature * 0.97, moved + settled_step);
    if (moved < settled_step) self.temperature = 0;
}

fn cellKey(x: i32, y: i32) u64 {
    return @as(u64, @as(u32, @bitCast(x))) << 32 | @as(u32, @bitCast(y));
}

fn orderU64(context: u64, item: u64) std.math.Order {
    return std.math.order(context, item);
}

/// The node drawn nearest `(x, y)` within `radius`, in world units.
pub fn nodeAt(self: *const Graph, x: f32, y: f32, radius: f32) ?u32 {
    var best: ?u32 = null;
    var best_distance = radius * radius;
    for (self.nodes, 0..) |node, i| {
        const d = (node.x - x) * (node.x - x) + (node.y - y) * (node.y - y);
        if (d <= best_distance) {
            best_distance = d;
            best = @intCast(i);
        }
    }
    return best;
}

/// The edge passing nearest `(x, y)` within `radius`, in world units.
pub fn edgeAt(self: *const Graph, x: f32, y: f32, radius: f32) ?u32 {
    var best: ?u32 = null;
    var best_distance = radius;
    for (self.edges, 0..) |edge, i| {
        if (edge.from == edge.to) continue;
        const a = self.nodes[edge.from];
        const b = self.nodes[edge.to];
        const d = segmentDistance(x, y, a.x, a.y, b.x, b.y);
        if (d <= best_distance) {
            best_distance = d;
            best = @intCast(i);
        }
    }
    return best;
}

fn segmentDistance(px: f32, py: f32, ax: f32, ay: f32, bx: f32, by: f32) f32 {
    const dx = bx - ax;
    const dy = by - ay;
    const length_squared = dx * dx + dy * dy;
    const t = if (length_squared == 0) 0 else std.math.clamp(((px - ax) * dx + (py - ay) * dy) / length_squared, 0, 1);
    const cx = ax + t * dx - px;
    const cy = ay + t * dy - py;
    return @sqrt(cx * cx + cy * cy);
}

// ---------------------------------------------------------------------------
// Tests

const testing = std.testing;

fn cell(canonical: []const u8) Client.Cell {
    return .{ .kind = .atom, .text = canonical, .canonical = canonical };
}

test "binary facts are edges, unary ones tags, and wider ones fact nodes" {
    var graph: Graph = .init(testing.allocator);
    defer graph.deinit();
    const predicates = [_]Predicate{
        .{ .name = "edge", .arity = 2, .columns = &.{ "1", "2" } },
        .{ .name = "person", .arity = 1, .columns = &.{"1"} },
        .{ .name = "born_in", .arity = 3, .columns = &.{ "Id", "City", "Country" } },
    };
    const facts = [_]Fact{
        .{ .predicate = 0, .values = &.{ cell("a"), cell("b") }, .derived = false },
        .{ .predicate = 0, .values = &.{ cell("a"), cell("a") }, .derived = true },
        .{ .predicate = 1, .values = &.{cell("a")}, .derived = false },
        .{ .predicate = 2, .values = &.{ cell("a"), cell("'Paris'"), cell("france") }, .derived = false },
    };
    try graph.sync(&predicates, &facts);

    // a, b, the fact node, 'Paris' and france.
    try testing.expectEqual(@as(usize, 5), graph.nodes.len);
    try testing.expectEqual(@as(usize, 5), graph.edges.len);
    const a = graph.index.get("a").?;
    try testing.expectEqual(@as(usize, 1), graph.nodes[a].facts.len);
    try testing.expect(graph.edges[1].derived);
    try testing.expectEqual(graph.edges[1].from, graph.edges[1].to);
    try testing.expectEqualStrings("City", graph.edges[3].label.?);
    try testing.expectEqual(Node.Kind.fact, graph.nodes[graph.edges[2].from].kind);
}

test "nodes keep their places across a sync, and the layout settles" {
    var graph: Graph = .init(testing.allocator);
    defer graph.deinit();
    const predicates = [_]Predicate{.{ .name = "edge", .arity = 2, .columns = &.{ "1", "2" } }};
    const first = [_]Fact{
        .{ .predicate = 0, .values = &.{ cell("a"), cell("b") }, .derived = false },
        .{ .predicate = 0, .values = &.{ cell("b"), cell("c") }, .derived = false },
    };
    try graph.sync(&predicates, &first);
    var steps: usize = 0;
    while (!graph.settled()) : (steps += 1) {
        try graph.step();
        try testing.expect(steps < 2000);
    }
    const b = graph.nodes[graph.index.get("b").?];
    graph.nodes[graph.index.get("a").?].pinned = true;

    const second = [_]Fact{
        .{ .predicate = 0, .values = &.{ cell("a"), cell("b") }, .derived = false },
        .{ .predicate = 0, .values = &.{ cell("b"), cell("d") }, .derived = false },
    };
    try graph.sync(&predicates, &second);
    const moved = graph.nodes[graph.index.get("b").?];
    try testing.expectEqual(b.x, moved.x);
    try testing.expectEqual(b.y, moved.y);
    try testing.expect(graph.nodes[graph.index.get("a").?].pinned);
    try testing.expectEqual(@as(?u32, null), graph.index.get("c"));
    // The new node starts beside its neighbor and the layout runs again.
    const d = graph.nodes[graph.index.get("d").?];
    try testing.expectApproxEqAbs(spacing, @sqrt((d.x - b.x) * (d.x - b.x) + (d.y - b.y) * (d.y - b.y)), 0.01);
    try testing.expect(!graph.settled());
}

test "hit testing finds the nearest node and edge" {
    var graph: Graph = .init(testing.allocator);
    defer graph.deinit();
    const predicates = [_]Predicate{.{ .name = "edge", .arity = 2, .columns = &.{ "1", "2" } }};
    const facts = [_]Fact{.{ .predicate = 0, .values = &.{ cell("a"), cell("b") }, .derived = false }};
    try graph.sync(&predicates, &facts);
    graph.nodes[0].x = 0;
    graph.nodes[0].y = 0;
    graph.nodes[1].x = 100;
    graph.nodes[1].y = 0;
    try testing.expectEqual(@as(?u32, 1), graph.nodeAt(95, 3, 10));
    try testing.expectEqual(@as(?u32, null), graph.nodeAt(50, 0, 10));
    try testing.expectEqual(@as(?u32, 0), graph.edgeAt(50, 4, 5));
    try testing.expectEqual(@as(?u32, null), graph.edgeAt(50, 20, 5));
}
