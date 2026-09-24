//! Forwards changes to `.dl` files under the watched directory to the engine.
//!
//! Nightwatch runs its own background thread and calls the handler from it;
//! the handler only filters paths and posts them to the engine's queue.
//! Event kinds are not forwarded: the engine re-reads each path and treats a
//! missing file as deleted, which also copes with editors that save by
//! writing a temporary file and renaming it over the original.

const std = @import("std");
const nightwatch = @import("nightwatch");
const Engine = @import("Engine.zig");

const Watcher = @This();
const log = std.log.scoped(.watcher);

handler: nightwatch.Default.Handler,
engine: *Engine,
watcher: nightwatch.Default,

const vtable: nightwatch.Default.Handler.VTable = .{
    .change = change,
    .rename = rename,
    .should_watch = shouldWatch,
};

/// Starts watching `engine.root`. `self` must not move until `deinit`.
pub fn start(self: *Watcher, engine: *Engine) !void {
    self.handler = .{ .vtable = &vtable };
    self.engine = engine;
    self.watcher = try .init(engine.io, engine.gpa, &self.handler);
    errdefer self.watcher.deinit();
    try self.watcher.watch(engine.root);
}

/// Stops the watcher thread.
pub fn deinit(self: *Watcher) void {
    self.watcher.deinit();
    self.* = undefined;
}

fn change(
    handler: *nightwatch.Default.Handler,
    path: []const u8,
    event: nightwatch.EventType,
    object: nightwatch.ObjectType,
) error{HandlerFailed}!void {
    const self: *Watcher = @fieldParentPtr("handler", handler);
    if (!self.engine.isWatchedPath(path)) return;
    // A directory moved in or out may carry .dl files with it.
    if (object == .dir and event != .modified) return self.engine.post(.reload);
    self.forward(path);
}

fn rename(
    handler: *nightwatch.Default.Handler,
    src: []const u8,
    dst: []const u8,
    object: nightwatch.ObjectType,
) error{HandlerFailed}!void {
    const self: *Watcher = @fieldParentPtr("handler", handler);
    if (object == .dir and (self.engine.isWatchedPath(src) or self.engine.isWatchedPath(dst)))
        return self.engine.post(.reload);
    self.forward(src);
    self.forward(dst);
}

fn forward(self: *Watcher, path: []const u8) void {
    if (!Engine.isDatalogPath(path) or !self.engine.isWatchedPath(path)) return;
    const owned = self.engine.gpa.dupe(u8, path) catch {
        log.err("out of memory; dropping change to {s}", .{path});
        return;
    };
    self.engine.post(.{ .changed = owned });
}

/// Watches only `.dl` files, outside hidden and dependency directories. On
/// kqueue every watched file costs a file descriptor.
fn shouldWatch(handler: *nightwatch.Default.Handler, path: []const u8, object: nightwatch.ObjectType) bool {
    const self: *Watcher = @fieldParentPtr("handler", handler);
    if (!self.engine.isWatchedPath(path)) return false;
    return object != .file or Engine.isDatalogPath(path);
}
