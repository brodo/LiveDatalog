//! LiveDatalogBrowser: a window onto a running development server's
//! database, one predicate at a time, as a table. See "Browser" in
//! CONTEXT.md. It is a client of the query listener like any other, so it
//! cannot change the database.

const std = @import("std");
const Io = std.Io;
const dvui = @import("dvui");
const Model = @import("Model.zig");
const Client = @import("Client.zig");
const Graph = @import("Graph.zig");
const GraphView = @import("GraphView.zig");

const log = std.log.scoped(.browser);

pub const dvui_app: dvui.App = .{
    .config = .{ .options = .{
        .size = .{ .w = 1100, .h = 700 },
        .min_size = .{ .w = 400, .h = 300 },
        .title = "LiveDatalog Browser",
        .org = "LiveDatalog",
    } },
    .frameFn = appFrame,
    .initFn = appInit,
    .deinitFn = appDeinit,
};
pub const main = dvui.App.main;
pub const panic = dvui.App.panic;
pub const std_options: std.Options = .{ .logFn = dvui.App.logFn };

const usage =
    \\Usage: LiveDatalogBrowser [--host ADDRESS] [--port PORT]
    \\
    \\Shows the database of a running LiveDatalogServer as tables.
    \\
    \\  --host ADDRESS    the server's address (default: 127.0.0.1)
    \\  --port PORT       its query port (default: 7070)
    \\
;

var io: Io = undefined;
var model: Model = undefined;
var fetcher: ?Io.Future(Io.Cancelable!void) = null;
var watcher: ?Io.Future(Io.Cancelable!void) = null;
var server_name_buffer: [64]u8 = undefined;
var server_name: []const u8 = "";
var show_errors = false;
/// The `Model.table_revision` the grid's columns were last sized for.
var sized_revision: ?u64 = null;
/// The share of the window's width the predicate list takes. Dragging the
/// sash between it and the table changes it.
var sidebar_ratio: f32 = 0.22;
/// The graph view's nodes and layout, and how it is looked at.
var graph: Graph = undefined;
var graph_view: GraphView = .{};
/// The `Model.graph_revision` the graph was last synced to.
var graph_synced: ?u64 = null;

fn parseAddress(args: []const [:0]const u8) !Io.net.IpAddress {
    var host: []const u8 = "127.0.0.1";
    var port: u16 = 7070;
    var index: usize = 1;
    while (index < args.len) : (index += 1) {
        const arg = args[index];
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) return error.Help;
        const is_host = std.mem.eql(u8, arg, "--host");
        if (!is_host and !std.mem.eql(u8, arg, "--port")) return error.UnknownOption;
        index += 1;
        if (index == args.len) return error.MissingValue;
        if (is_host) {
            host = args[index];
        } else {
            port = std.fmt.parseInt(u16, args[index], 10) catch return error.InvalidPort;
        }
    }
    return Io.net.IpAddress.parse(host, port);
}

fn appInit(win: *dvui.Window) !void {
    const process = dvui.App.main_init.?;
    io = process.io;
    const args = try process.minimal.args.toSlice(process.arena.allocator());
    const address = parseAddress(args) catch |err| {
        std.debug.print("{s}", .{usage});
        if (err != error.Help) std.debug.print("\nerror: {s}\n", .{@errorName(err)});
        return err;
    };
    server_name = std.fmt.bufPrint(&server_name_buffer, "{f}", .{address}) catch "server";

    graph = .init(process.gpa);
    model.init(process.gpa, io, address, wake, win);
    fetcher = try io.concurrent(Model.runFetcher, .{&model});
    watcher = try io.concurrent(Model.runWatcher, .{&model});
}

fn appDeinit(_: *dvui.Window) void {
    inline for (.{ &fetcher, &watcher }) |task| if (task.*) |*future| {
        future.cancel(io) catch |err| switch (err) {
            error.Canceled => {},
        };
    };
    model.deinit();
    graph.deinit();
}

/// Called from the model's tasks when there is something new to show.
fn wake(context: ?*anyopaque) void {
    const win: *dvui.Window = @ptrCast(@alignCast(context.?));
    dvui.refresh(win, @src(), null);
}

fn appFrame() !dvui.App.Result {
    model.mutex.lockUncancelable(io);
    defer model.mutex.unlock(io);

    statusBar();
    if (show_errors) loadErrors();

    var paned = dvui.paned(@src(), .{
        .direction = .horizontal,
        .collapsed_size = 0,
        .split_ratio = &sidebar_ratio,
    }, .{ .expand = .both });
    defer paned.deinit();
    if (paned.showFirst()) try predicateList();
    if (paned.showSecond()) {
        var pane = dvui.box(@src(), .{}, .{ .expand = .both });
        defer pane.deinit();
        try queryBar();
        if (model.graph_mode) {
            try graphPane();
        } else if (model.query != null) {
            answers();
        } else {
            try table();
        }
    }
    return .ok;
}

/// What the text of stale data looks like while the server is away.
fn textOptions() dvui.Options {
    if (model.connected) return .{};
    return .{ .color_text = .{ .color = dvui.themeGet().text.opacity(0.45) } };
}

fn statusBar() void {
    var bar = dvui.box(@src(), .{ .dir = .horizontal }, .{
        .expand = .horizontal,
        .background = true,
        .style = .window,
    });
    defer bar.deinit();

    const state = if (model.connected) "connected" else "disconnected, retrying";
    dvui.label(@src(), "{s} — {s}", .{ server_name, state }, .{
        .style = if (model.connected) null else .err,
        .gravity_y = 0.5,
    });
    if (model.catalog.generation) |generation|
        dvui.label(@src(), "generation {d}", .{generation}, .{ .gravity_y = 0.5 });
    dvui.label(@src(), "{d} predicates", .{model.catalog.predicates.len}, .{ .gravity_y = 0.5 });

    const errors = model.catalog.errors.len;
    if (errors == 0) {
        dvui.label(@src(), "no load errors", .{}, .{ .gravity_y = 0.5 });
        show_errors = false;
        return;
    }
    var label_buffer: [64]u8 = undefined;
    const label = std.fmt.bufPrint(&label_buffer, "{d} load error{s} {s}", .{
        errors,
        if (errors == 1) "" else "s",
        if (show_errors) "▴" else "▾",
    }) catch "load errors";
    if (dvui.button(@src(), label, .{}, .{ .style = .err })) show_errors = !show_errors;
}

fn loadErrors() void {
    var scroll = dvui.scrollArea(@src(), .{}, .{
        .expand = .horizontal,
        .max_size_content = .height(160),
        .background = true,
        .style = .err,
    });
    defer scroll.deinit();
    for (model.catalog.errors, 0..) |load_error, index| {
        dvui.labelNoFmt(@src(), load_error.message, .{}, .{
            .id_extra = index,
            .font = .theme(.mono),
            .expand = .horizontal,
        });
    }
}

fn predicateList() !void {
    var scroll = dvui.scrollArea(@src(), .{}, .{ .expand = .both, .background = true, .style = .window });
    defer scroll.deinit();

    for (model.catalog.predicates, 0..) |predicate, index| {
        if (model.graph_mode) {
            try graphChoice(predicate, index);
            continue;
        }
        const selected = if (model.selection) |s|
            model.query == null and s.arity == predicate.arity and std.mem.eql(u8, s.name, predicate.name)
        else
            false;
        var label_buffer: [256]u8 = undefined;
        const label = std.fmt.bufPrint(&label_buffer, "{s}/{d}   {s} · {d}{s}", .{
            predicate.name,
            predicate.arity,
            predicate.kind,
            predicate.facts,
            if (predicate.typed) " · typed" else "",
        }) catch predicate.name;
        var options = textOptions();
        options.id_extra = index;
        options.expand = .horizontal;
        options.style = if (selected) .highlight else .control;
        if (dvui.button(@src(), label, .{}, options)) try model.select(predicate.name, predicate.arity, null);
    }
}

/// A predicate in the sidebar while the graph shows: whether it is drawn, in
/// the color it is drawn in.
fn graphChoice(predicate: Model.Predicate, index: usize) !void {
    var row = dvui.box(@src(), .{ .dir = .horizontal }, .{ .id_extra = index, .expand = .horizontal });
    defer row.deinit();
    dvui.box(@src(), .{}, .{
        .min_size_content = .{ .w = 10, .h = 10 },
        .gravity_y = 0.5,
        .margin = .{ .x = 4, .w = 2 },
        .background = true,
        .corners = .all(2),
        .color_fill = .{ .color = GraphView.predicateColor(predicate.name) },
    }).deinit();
    var label_buffer: [256]u8 = undefined;
    const label = std.fmt.bufPrint(&label_buffer, "{s}/{d}   {s} · {d}", .{
        predicate.name,
        predicate.arity,
        predicate.kind,
        predicate.facts,
    }) catch predicate.name;
    // A predicate without arguments has nothing to draw.
    if (predicate.arity == 0) return dvui.labelNoFmt(@src(), label, .{}, disabledOptions());
    var chosen = model.graphChosen(predicate.name, predicate.arity);
    if (dvui.checkbox(@src(), &chosen, label, textOptions())) try model.toggleGraph(predicate.name, predicate.arity);
}

fn disabledOptions() dvui.Options {
    return .{ .color_text = .{ .color = dvui.themeGet().text.opacity(0.4) } };
}

/// The chosen predicates' facts as a network. See "Graph view" in CONTEXT.md.
fn graphPane() !void {
    const data = if (model.graph) |*g| g else {
        dvui.label(@src(), "Loading…", .{}, .{ .gravity_x = 0.5, .gravity_y = 0.5 });
        return;
    };
    if (graph_synced != model.graph_revision) {
        try graph.sync(data.predicates, data.facts);
        graph_synced = model.graph_revision;
    }

    {
        var bar = dvui.box(@src(), .{ .dir = .horizontal }, .{ .expand = .horizontal });
        defer bar.deinit();
        dvui.label(@src(), "{d} nodes · {d} edges", .{ graph.nodes.len, graph.edges.len }, .{ .gravity_y = 0.5 });
        if (data.facts.len < data.total) {
            dvui.label(@src(), "showing {d} of {d} facts; at most {d} are drawn", .{
                data.facts.len,
                data.total,
                Model.graph_cap,
            }, .{ .style = .err, .gravity_y = 0.5 });
        }
        if (model.graph_choice.items.len == 0)
            dvui.label(@src(), "Choose predicates on the left to draw them.", .{}, .{ .gravity_y = 0.5 });
        if (dvui.button(@src(), "Re-layout", .{}, .{ .gravity_x = 1 })) {
            graph.relayout();
            graph_view.fitted = false;
        }
        if (dvui.button(@src(), "Fit", .{}, .{ .gravity_x = 1 })) graph_view.fitted = false;
    }
    graph_view.draw(&graph, data, !model.connected);
}

fn table() !void {
    const selection = model.selection orelse {
        dvui.label(@src(), "Choose a predicate on the left.", .{}, .{ .gravity_x = 0.5, .gravity_y = 0.5 });
        return;
    };
    const predicate = model.catalog.find(selection.name, selection.arity) orelse {
        dvui.label(@src(), "{s}/{d} is gone from the database.", .{ selection.name, selection.arity }, .{
            .gravity_x = 0.5,
            .gravity_y = 0.5,
        });
        return;
    };
    const fetched = if (model.table) |*t| (if (t.selection.eql(selection)) t else null) else null;
    const columns: []const Model.Column = if (fetched) |t| t.columns else &.{};
    const total = predicate.facts;

    // A new grid for every predicate, so that sorting and scrolling start over.
    const grid_id = std.hash.Wyhash.hash(selection.arity, selection.name);
    var grid = dvui.grid(@src(), .{
        .scroll_opts = .{ .horizontal = .auto },
        .rows = total,
    }, .{ .expand = .both, .id_extra = @truncate(grid_id) });
    defer grid.deinit();
    // Fit the columns and rows to what is on show whenever new rows arrive.
    // Sizing takes a few frames to settle, which the grid schedules itself.
    if (sized_revision != model.table_revision) {
        grid.autoSize(.both);
        sized_revision = model.table_revision;
    }

    for (0..selection.arity) |column| {
        const header = grid.colHeader(.{ .col = column }, .{ .border = .all(1) });
        defer header.deinit();
        var text_buffer: [256]u8 = undefined;
        const info: Model.Column = if (column < columns.len) columns[column] else .{ .name = null, .type = null };
        const text = if (info.name) |name|
            (if (info.type) |t| std.fmt.bufPrint(&text_buffer, "{s}\n{s}", .{ name, t }) else name)
        else if (info.type) |t|
            std.fmt.bufPrint(&text_buffer, "#{d}\n{s}", .{ column + 1, t })
        else
            std.fmt.bufPrint(&text_buffer, "#{d}", .{column + 1});
        if (header.headerSortable(text catch "?", .{})) |direction| {
            try model.select(selection.name, selection.arity, .{
                .column = column,
                .descending = direction == .descending,
            });
        }
    }

    const first, const last = grid.rowsVisible();
    model.show(first, last);
    for (first..last) |row| {
        const cells = if (fetched) |t| t.row(row) else null;
        for (0..selection.arity) |column| {
            var cell = grid.cell(.{ .col = column, .row = row }, .{ .border = .all(1) });
            defer cell.deinit();
            var options = textOptions();
            const content = cells orelse {
                options.color_text = .{ .color = dvui.themeGet().text.opacity(0.3) };
                dvui.labelNoFmt(@src(), "…", .{}, options);
                continue;
            };
            cellLabel(content[column], options);
        }
    }
}

/// Shows one value in a cell: numbers to the right, lists in a fixed-width
/// font.
fn cellLabel(value: Client.Cell, base: dvui.Options) void {
    var options = base;
    if (value.kind == .number) options.gravity_x = 1;
    if (value.kind == .structure) options.font = .theme(.mono);
    dvui.labelNoFmt(@src(), value.text, .{}, options);
}

/// The longest query the query bar holds.
const max_query = 4096;

/// A line to type a query into. Return or Run shows its answers in place of
/// the open predicate, until a predicate is chosen again.
fn queryBar() !void {
    var bar = dvui.box(@src(), .{ .dir = .horizontal }, .{ .expand = .horizontal });
    defer bar.deinit();

    // Which view the right side shows.
    if (dvui.button(@src(), "Table", .{}, .{ .style = if (model.graph_mode) .control else .highlight }))
        model.showGraph(false);
    if (dvui.button(@src(), "Graph", .{}, .{ .style = if (model.graph_mode) .highlight else .control }))
        model.showGraph(true);

    var query_buffer: [max_query]u8 = undefined;
    var entry = dvui.textEntry(@src(), .{
        .text = .{ .internal = .{ .limit = max_query } },
        .placeholder = "Query, e.g. born(Who, Year), Year < 1800",
    }, .{ .expand = .horizontal, .font = .theme(.mono) });
    const entered = entry.enter_pressed;
    const query = query_buffer[0..entry.getText().len];
    @memcpy(query, entry.getText());
    entry.deinit();

    const run = dvui.button(@src(), "Run", .{}, .{});
    if ((entered or run) and std.mem.trim(u8, query, &std.ascii.whitespace).len != 0) {
        // Answers are rows, not facts, so they show as a table.
        model.showGraph(false);
        try model.ask(query);
    }
}

/// The answers to the query in the query bar, headed by its variables.
fn answers() void {
    const query = model.query.?;
    const answer = if (model.answer) |*a| (if (std.mem.eql(u8, a.query, query)) a else null) else null;
    const centered: dvui.Options = .{ .gravity_x = 0.5, .gravity_y = 0.5 };
    const shown = answer orelse return dvui.label(@src(), "Running…", .{}, centered);
    if (shown.failure) |failure| {
        return dvui.labelNoFmt(@src(), failure, .{}, .{ .style = .err, .gravity_x = 0.5, .gravity_y = 0.5 });
    }
    // A query without variables only holds or does not.
    if (shown.header.len == 0) {
        return dvui.label(@src(), "{s}", .{if (shown.rows.len == 0) "No." else "Yes."}, centered);
    }
    dvui.label(@src(), "{d} answer{s}", .{ shown.rows.len, if (shown.rows.len == 1) "" else "s" }, textOptions());

    var grid = dvui.grid(@src(), .{
        .scroll_opts = .{ .horizontal = .auto },
        .rows = shown.rows.len,
    }, .{ .expand = .both, .id_extra = @truncate(std.hash.Wyhash.hash(0, query)) });
    defer grid.deinit();
    if (sized_revision != model.table_revision) {
        grid.autoSize(.both);
        sized_revision = model.table_revision;
    }
    for (shown.header, 0..) |name, column| {
        const header = grid.colHeader(.{ .col = column }, .{ .border = .all(1) });
        defer header.deinit();
        dvui.labelNoFmt(@src(), name, .{}, .{ .gravity_y = 0.5 });
    }
    const first, const last = grid.rowsVisible();
    for (shown.rows[first..last], first..) |row, index| {
        for (row, 0..) |value, column| {
            var cell = grid.cell(.{ .col = column, .row = index }, .{ .border = .all(1) });
            defer cell.deinit();
            cellLabel(value, textOptions());
        }
    }
}
