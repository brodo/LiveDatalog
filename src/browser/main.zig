//! LiveDatalogBrowser: a window onto a running development server's
//! database, one predicate at a time, as a table. See "Browser" in
//! CONTEXT.md. It is a client of the query listener like any other, so it
//! cannot change the database.

const std = @import("std");
const Io = std.Io;
const dvui = @import("dvui");
const Model = @import("Model.zig");
const Client = @import("Client.zig");

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
    if (paned.showSecond()) try table();
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
        const selected = if (model.selection) |s|
            s.arity == predicate.arity and std.mem.eql(u8, s.name, predicate.name)
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
            const value: Client.Cell = content[column];
            if (value.kind == .number) options.gravity_x = 1;
            if (value.kind == .structure) options.font = .theme(.mono);
            dvui.labelNoFmt(@src(), value.text, .{}, options);
        }
    }
}
