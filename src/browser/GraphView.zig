//! Draws a `Graph` on a canvas and lets it be handled: drag a node to move
//! and pin it, drag the background to pan, scroll to zoom, and hover for the
//! whole of a value or a fact.

const std = @import("std");
const dvui = @import("dvui");
const Graph = @import("Graph.zig");
const Model = @import("Model.zig");

const GraphView = @This();

/// The world point at the middle of the canvas.
center_x: f32 = 0,
center_y: f32 = 0,
zoom: f32 = 1,
drag: ?Drag = null,
/// Whether the view has been fitted to the graph since it was first drawn.
fitted: bool = false,

const Drag = union(enum) {
    pan,
    node: u32,
};

/// Node radii and the like, in logical pixels, whatever the zoom.
const value_radius: f32 = 5;
const fact_radius: f32 = 3.5;
const hit_radius: f32 = 9;
/// Labels longer than this many bytes are cut, and shown whole on hover.
const max_label = 24;
/// Below this zoom only hovered nodes and their neighbors are labeled.
const label_zoom: f32 = 0.45;

/// A color for each predicate, the same wherever it is drawn.
pub fn predicateColor(name: []const u8) dvui.Color {
    const palette = [_]dvui.Color{
        .{ .r = 0x1f, .g = 0x77, .b = 0xb4 }, .{ .r = 0xff, .g = 0x7f, .b = 0x0e },
        .{ .r = 0x2c, .g = 0xa0, .b = 0x2c }, .{ .r = 0xd6, .g = 0x27, .b = 0x28 },
        .{ .r = 0x94, .g = 0x67, .b = 0xbd }, .{ .r = 0x8c, .g = 0x56, .b = 0x4b },
        .{ .r = 0xe3, .g = 0x77, .b = 0xc2 }, .{ .r = 0x17, .g = 0xbe, .b = 0xcf },
        .{ .r = 0xbc, .g = 0xbd, .b = 0x22 }, .{ .r = 0x7f, .g = 0x7f, .b = 0x7f },
    };
    return palette[std.hash.Wyhash.hash(7, name) % palette.len];
}

/// Centers the graph on the canvas and zooms to fit it.
pub fn fit(self: *GraphView, graph: *const Graph, width: f32, height: f32) void {
    if (graph.nodes.len == 0) return;
    var min_x = graph.nodes[0].x;
    var max_x = min_x;
    var min_y = graph.nodes[0].y;
    var max_y = min_y;
    for (graph.nodes) |node| {
        min_x = @min(min_x, node.x);
        max_x = @max(max_x, node.x);
        min_y = @min(min_y, node.y);
        max_y = @max(max_y, node.y);
    }
    self.center_x = (min_x + max_x) / 2;
    self.center_y = (min_y + max_y) / 2;
    const margin = Graph.spacing;
    const fits = @min(width / (max_x - min_x + 2 * margin), height / (max_y - min_y + 2 * margin));
    self.zoom = std.math.clamp(fits, 0.05, 2);
}

/// Draws `graph`, whose facts are `data`'s, and handles the mouse over it.
/// `stale` greys it out, as while the server is away.
pub fn draw(self: *GraphView, graph: *Graph, data: *const Model.GraphData, stale: bool) void {
    var canvas = dvui.box(@src(), .{}, .{ .expand = .both, .background = true, .style = .content });
    defer canvas.deinit();
    const rs = canvas.data().contentRectScale();
    const scale = rs.s;
    if (!self.fitted and graph.nodes.len != 0 and rs.r.w > 0) {
        // Fit once the first layout has spread the graph out.
        if (graph.settled()) {
            self.fit(graph, rs.r.w / scale, rs.r.h / scale);
            self.fitted = true;
        }
    }
    const frame: Frame = .{ .view = self, .rs = rs };

    var mouse: ?dvui.Point.Physical = null;
    for (dvui.events()) |*e| {
        if (!dvui.eventMatchSimple(e, canvas.data())) continue;
        const me = switch (e.evt) {
            .mouse => |me| me,
            else => continue,
        };
        switch (me.action) {
            .press => if (me.button.pointer()) {
                e.handle(@src(), canvas.data());
                dvui.captureMouse(canvas.data(), e.num);
                const at = frame.toWorld(me.p);
                self.drag = if (graph.nodeAt(at[0], at[1], hit_radius / self.zoom)) |node| .{ .node = node } else .pan;
            },
            .release => if (me.button.pointer() and dvui.captured(canvas.data().id)) {
                e.handle(@src(), canvas.data());
                dvui.captureMouse(null, e.num);
                self.drag = null;
            },
            .motion => |delta| if (dvui.captured(canvas.data().id)) {
                e.handle(@src(), canvas.data());
                const dx = delta.x / (self.zoom * scale);
                const dy = delta.y / (self.zoom * scale);
                switch (self.drag orelse .pan) {
                    .pan => {
                        self.center_x -= dx;
                        self.center_y -= dy;
                    },
                    .node => |node| if (node < graph.nodes.len) {
                        graph.nodes[node].x += dx;
                        graph.nodes[node].y += dy;
                        graph.nodes[node].pinned = true;
                        // Let the neighbors follow a little.
                        graph.temperature = @max(graph.temperature, Graph.spacing * 0.1);
                    },
                }
            },
            .wheel_y => |amount| {
                e.handle(@src(), canvas.data());
                const before = frame.toWorld(me.p);
                self.zoom = std.math.clamp(self.zoom * std.math.pow(f32, 1.0015, amount), 0.05, 8);
                const after = frame.toWorld(me.p);
                self.center_x += before[0] - after[0];
                self.center_y += before[1] - after[1];
            },
            .position => mouse = me.p,
            else => {},
        }
    }

    if (!graph.settled()) {
        graph.step() catch |err| dvui.logError(@src(), err, "cannot lay the graph out", .{});
        dvui.refresh(null, @src(), canvas.data().id);
    }

    // What the mouse is over, and what that lights up.
    var hovered_node: ?u32 = null;
    var hovered_edge: ?u32 = null;
    if (mouse) |p| {
        const at = frame.toWorld(p);
        hovered_node = graph.nodeAt(at[0], at[1], hit_radius / self.zoom);
        if (hovered_node == null) hovered_edge = graph.edgeAt(at[0], at[1], 4 / self.zoom);
    }
    if (self.drag) |drag| switch (drag) {
        .node => |node| hovered_node = node,
        .pan => {},
    };
    if (hovered_node != null) dvui.cursorSet(.hand);
    const lit: []bool = dvui.currentWindow().arena().alloc(bool, graph.nodes.len) catch &.{};
    @memset(lit, false);
    if (hovered_node) |node| if (node < lit.len) {
        lit[node] = true;
        for (graph.edges) |edge| {
            if (edge.from == node) lit[edge.to] = true;
            if (edge.to == node) lit[edge.from] = true;
        }
    };
    const focused = hovered_node != null;

    const previous_clip = dvui.clip(rs.r);
    defer dvui.clipSet(previous_clip);
    const text_color = dvui.themeGet().text;
    const fade: f32 = if (stale) 0.45 else 1;

    for (graph.edges, 0..) |edge, index| {
        const from = frame.toScreen(graph.nodes[edge.from]);
        const to = frame.toScreen(graph.nodes[edge.to]);
        if (!frame.visible(from, 20 * scale) and !frame.visible(to, 20 * scale)) continue;
        const lit_edge = (if (hovered_edge) |h| h == index else false) or
            (hovered_node != null and (edge.from == hovered_node.? or edge.to == hovered_node.?));
        var color = predicateColor(data.predicates[edge.predicate].name);
        color = color.opacity(fade * (if (focused and !lit_edge) @as(f32, 0.12) else 0.85));
        const thickness: f32 = (if (lit_edge) @as(f32, 2.5) else 1.4) * scale;
        const wire = graph.nodes[edge.from].kind == .fact;
        if (edge.from == edge.to) {
            drawLoop(from, 11 * scale, thickness, color);
            continue;
        }
        const end_gap = (if (graph.nodes[edge.to].kind == .fact) fact_radius else value_radius) * scale + 2 * scale;
        const tip = pullBack(from, to, end_gap);
        drawLine(from, tip, thickness, color, edge.derived, scale);
        if (!wire) drawArrowhead(from, tip, 7 * scale, color);
        if (wire and edge.label != null and self.zoom >= 1 and !digits(edge.label.?)) {
            const middle: dvui.Point.Physical = .{ .x = (from.x + to.x) / 2, .y = (from.y + to.y) / 2 };
            drawText(edge.label.?, middle, scale, color, .small);
        }
    }

    for (graph.nodes, 0..) |node, index| {
        const at = frame.toScreen(node);
        if (!frame.visible(at, 40 * scale)) continue;
        const dim = focused and !(index < lit.len and lit[index]);
        const alpha = fade * (if (dim) @as(f32, 0.2) else 1);
        switch (node.kind) {
            .value => {
                fillCircle(at, value_radius * scale, text_color.opacity(alpha * 0.8));
                if (node.pinned)
                    strokeCircle(at, (value_radius + 2.5) * scale, 1 * scale, text_color.opacity(alpha * 0.6));
            },
            .fact => {
                const color = predicateColor(data.predicates[node.facts[0].predicate].name);
                fillCircle(at, fact_radius * scale, color.opacity(alpha));
            },
        }
        const labeled = self.zoom >= label_zoom or (index < lit.len and lit[index]);
        if (node.kind != .value or !labeled) continue;
        var label_at: dvui.Point.Physical = .{ .x = at.x + (value_radius + 4) * scale, .y = at.y - 8 * scale };
        drawText(truncate(node.label), label_at, scale, text_color.opacity(alpha), .body);
        // The unary facts about the value, as chips under its label.
        label_at.y += 16 * scale;
        for (node.facts) |ref| {
            const name = data.predicates[ref.predicate].name;
            const color = predicateColor(name).opacity(alpha);
            const width = drawChip(name, label_at, scale, color, data.facts[ref.fact].derived);
            label_at.x += width + 3 * scale;
        }
    }

    // What the mouse is over, in full.
    var tip_text: std.ArrayList(u8) = .empty;
    const arena = dvui.currentWindow().arena();
    if (hovered_node) |node| if (node < graph.nodes.len) {
        const n = graph.nodes[node];
        switch (n.kind) {
            .value => writeValue(arena, &tip_text, data, n),
            .fact => writeFact(arena, &tip_text, data, n.facts[0].fact),
        }
    };
    if (hovered_edge) |edge| writeFact(arena, &tip_text, data, graph.edges[edge].fact);
    if (tip_text.items.len != 0 and self.drag == null) {
        const mouse_at = dvui.currentWindow().mouse_pt.toNatural();
        var tip: dvui.FloatingWidget = undefined;
        tip.init(@src(), .{ .mouse_events = false }, .{
            .rect = .{ .x = mouse_at.x + 14, .y = mouse_at.y + 14 },
            .background = true,
            .border = .all(1),
            .corners = .all(4),
            .padding = .all(6),
            .style = .window,
        });
        dvui.labelNoFmt(@src(), tip_text.items, .{}, .{});
        tip.deinit();
    }
}

/// Converts between world and screen for one frame of the canvas.
const Frame = struct {
    view: *const GraphView,
    rs: dvui.RectScale,

    fn toScreen(self: Frame, node: Graph.Node) dvui.Point.Physical {
        const factor = self.view.zoom * self.rs.s;
        return .{
            .x = self.rs.r.x + self.rs.r.w / 2 + (node.x - self.view.center_x) * factor,
            .y = self.rs.r.y + self.rs.r.h / 2 + (node.y - self.view.center_y) * factor,
        };
    }

    fn toWorld(self: Frame, p: dvui.Point.Physical) [2]f32 {
        const factor = self.view.zoom * self.rs.s;
        return .{
            (p.x - self.rs.r.x - self.rs.r.w / 2) / factor + self.view.center_x,
            (p.y - self.rs.r.y - self.rs.r.h / 2) / factor + self.view.center_y,
        };
    }

    /// Whether a point is on the canvas, or within `margin` of it.
    fn visible(self: Frame, p: dvui.Point.Physical, margin: f32) bool {
        const r = self.rs.r;
        return p.x >= r.x - margin and p.x <= r.x + r.w + margin and
            p.y >= r.y - margin and p.y <= r.y + r.h + margin;
    }
};

/// Writes a value in full, then the unary facts about it.
fn writeValue(arena: std.mem.Allocator, out: *std.ArrayList(u8), data: *const Model.GraphData, node: Graph.Node) void {
    out.appendSlice(arena, node.label) catch return;
    for (node.facts) |ref| {
        out.append(arena, '\n') catch return;
        writeFact(arena, out, data, ref.fact);
    }
}

/// Writes a fact as `name(Column: value, ...)`, leaving out positional
/// column names.
fn writeFact(arena: std.mem.Allocator, out: *std.ArrayList(u8), data: *const Model.GraphData, index: u32) void {
    const fact = data.facts[index];
    const predicate = data.predicates[fact.predicate];
    out.print(arena, "{s}(", .{predicate.name}) catch return;
    for (fact.values, 0..) |value, position| {
        if (position != 0) out.appendSlice(arena, ", ") catch return;
        const column = if (position < predicate.columns.len) predicate.columns[position] else "";
        if (column.len != 0 and !digits(column)) out.print(arena, "{s}: ", .{column}) catch return;
        out.appendSlice(arena, value.canonical) catch return;
    }
    out.print(arena, "){s}", .{if (fact.derived) "  (derived)" else ""}) catch return;
}

/// Whether a column name is only a position, as an untyped predicate's are.
fn digits(text: []const u8) bool {
    for (text) |byte| if (!std.ascii.isDigit(byte)) return false;
    return text.len != 0;
}

/// `text` cut to `max_label` bytes at a character boundary, marked as cut.
fn truncate(text: []const u8) []const u8 {
    const line_end = std.mem.findScalar(u8, text, '\n') orelse text.len;
    if (line_end <= max_label and line_end == text.len) return text;
    var end = @min(line_end, max_label);
    while (end > 0 and text[end] & 0xc0 == 0x80) end -= 1;
    return std.fmt.allocPrint(dvui.currentWindow().arena(), "{s}…", .{text[0..end]}) catch text[0..end];
}

fn pullBack(from: dvui.Point.Physical, to: dvui.Point.Physical, gap: f32) dvui.Point.Physical {
    const dx = to.x - from.x;
    const dy = to.y - from.y;
    const length = @sqrt(dx * dx + dy * dy);
    if (length <= gap) return to;
    return .{ .x = to.x - dx / length * gap, .y = to.y - dy / length * gap };
}

/// A line, dashed for a derived fact.
fn drawLine(
    from: dvui.Point.Physical,
    to: dvui.Point.Physical,
    thickness: f32,
    color: dvui.Color,
    dashed: bool,
    scale: f32,
) void {
    if (!dashed) {
        dvui.Path.stroke(.{ .points = &.{ from, to } }, .{ .thickness = thickness, .color = .{ .color = color } });
        return;
    }
    const dx = to.x - from.x;
    const dy = to.y - from.y;
    const length = @sqrt(dx * dx + dy * dy);
    if (length < 0.5) return;
    const dash = 6 * scale;
    var at: f32 = 0;
    while (at < length) : (at += 2 * dash) {
        const end = @min(at + dash, length);
        dvui.Path.stroke(.{ .points = &.{
            .{ .x = from.x + dx * at / length, .y = from.y + dy * at / length },
            .{ .x = from.x + dx * end / length, .y = from.y + dy * end / length },
        } }, .{ .thickness = thickness, .color = .{ .color = color } });
    }
}

fn drawArrowhead(from: dvui.Point.Physical, tip: dvui.Point.Physical, size: f32, color: dvui.Color) void {
    const dx = tip.x - from.x;
    const dy = tip.y - from.y;
    const length = @sqrt(dx * dx + dy * dy);
    if (length < size) return;
    const ux = dx / length;
    const uy = dy / length;
    const base_x = tip.x - ux * size;
    const base_y = tip.y - uy * size;
    dvui.Path.fillConvex(.{ .points = &.{
        tip,
        .{ .x = base_x - uy * size * 0.45, .y = base_y + ux * size * 0.45 },
        .{ .x = base_x + uy * size * 0.45, .y = base_y - ux * size * 0.45 },
    } }, .{ .color = .{ .color = color } });
}

/// A self-loop: a small circle touching the node above it.
fn drawLoop(at: dvui.Point.Physical, radius: f32, thickness: f32, color: dvui.Color) void {
    strokeCircle(.{ .x = at.x, .y = at.y - radius }, radius, thickness, color);
}

fn circlePath(builder: *dvui.Path.Builder, at: dvui.Point.Physical, radius: f32) dvui.Path {
    builder.addArc(at, radius, std.math.tau, 0, true);
    return builder.build();
}

fn fillCircle(at: dvui.Point.Physical, radius: f32, color: dvui.Color) void {
    var builder: dvui.Path.Builder = .init(dvui.currentWindow().lifo());
    defer builder.deinit();
    circlePath(&builder, at, radius).fillConvex(.{ .color = .{ .color = color }, .fade = 1 });
}

fn strokeCircle(at: dvui.Point.Physical, radius: f32, thickness: f32, color: dvui.Color) void {
    var builder: dvui.Path.Builder = .init(dvui.currentWindow().lifo());
    defer builder.deinit();
    circlePath(&builder, at, radius).stroke(.{ .thickness = thickness, .color = .{ .color = color }, .closed = true });
}

const TextStyle = enum { body, small };

fn font(style: TextStyle) dvui.Font {
    const body = (dvui.Options{ .font = .theme(.body) }).fontGet();
    return if (style == .small) body.larger(-2) else body;
}

/// Draws `text` with its top left at `at`.
fn drawText(text: []const u8, at: dvui.Point.Physical, scale: f32, color: dvui.Color, style: TextStyle) void {
    _ = drawTextWidth(text, at, scale, color, style);
}

/// Draws `text` with its top left at `at`. Returns its width, physical.
fn drawTextWidth(text: []const u8, at: dvui.Point.Physical, scale: f32, color: dvui.Color, style: TextStyle) f32 {
    const f = font(style);
    const size = f.textSize(text);
    dvui.renderText(.{
        .font = f,
        .text = text,
        .rs = .{ .r = .{ .x = at.x, .y = at.y, .w = size.w * scale, .h = size.h * scale }, .s = scale },
        .color = color,
    }) catch |err| dvui.logError(@src(), err, "cannot draw a label", .{});
    return size.w * scale;
}

/// A predicate's name on a small colored tab, outlined only for a derived
/// fact. Returns its width, physical.
fn drawChip(name: []const u8, at: dvui.Point.Physical, scale: f32, color: dvui.Color, derived: bool) f32 {
    const f = font(.small);
    const size = f.textSize(name);
    const pad = 3 * scale;
    const rect: dvui.Rect.Physical = .{ .x = at.x, .y = at.y, .w = size.w * scale + 2 * pad, .h = size.h * scale };
    if (derived) {
        rect.stroke(.all(3 * scale), .{ .thickness = 1 * scale, .color = .{ .color = color } });
        _ = drawTextWidth(name, .{ .x = at.x + pad, .y = at.y }, scale, color, .small);
    } else {
        rect.fill(.all(3 * scale), .{ .color = .{ .color = color } });
        _ = drawTextWidth(name, .{ .x = at.x + pad, .y = at.y }, scale, .white, .small);
    }
    return rect.w;
}
