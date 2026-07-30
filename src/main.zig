const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    const args = try init.minimal.args.toSlice(allocator);
    const source = if (args.len > 1)
        try std.Io.Dir.cwd().readFileAlloc(init.io, args[1], allocator, .unlimited)
    else source: {
        var buffer: [4096]u8 = undefined;
        var reader = std.Io.File.stdin().readerStreaming(init.io, &buffer);
        break :source try reader.interface.allocRemaining(allocator, .unlimited);
    };

    var database: LiveDatalog.Jatalog = .init(allocator);
    defer database.deinit();
    var result = try database.execute(source);
    defer result.deinit();

    var output_buffer: [4096]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;
    switch (result) {
        .none => {},
        .changed => |changed| try writer.writeAll(if (changed) "Yes.\n" else "No.\n"),
        .query => |query_result| {
            if (query_result.answers.items.len == 0) {
                try writer.writeAll("No.\n");
            } else if (query_result.answers.items[0].values.count() == 0) {
                try writer.writeAll("Yes.\n");
            } else {
                for (query_result.answers.items) |answer| {
                    for (answer.values.keys(), answer.values.values(), 0..) |variable, value, index| {
                        if (index != 0) try writer.writeAll(", ");
                        try writer.print("{s}: {s}", .{
                            database.strings.resolve(variable),
                            database.strings.resolve(value),
                        });
                    }
                    try writer.writeByte('\n');
                }
            }
        },
    }
    try writer.flush();
}

test {
    _ = LiveDatalog;
}
