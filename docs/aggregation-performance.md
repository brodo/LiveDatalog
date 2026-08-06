# Aggregation performance baseline

Phase 5 records a naive-evaluation baseline for later optimization work. Run
the workload with:

```sh
zig build benchmark-aggregation -Doptimize=ReleaseFast
```

The benchmark constructs a 25-node chain (24 base edges), computes its full
recursive transitive closure (300 `reachable` tuples), and collects every
`[From, To]` pair into one structural `setof` result. After one warm-up, it
runs ten identical summary queries. Each query intentionally rebuilds all
derived facts because persistent or incremental materialization is deferred.

## 2026-07-30 baseline

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.2
- five process-level samples after the benchmark executable was cached
- per-query samples: 6.332, 6.284, 6.297, 6.218, and 6.256 ms
- median: **6.284 ms/query**

This is a comparison baseline, not a cross-machine performance promise. Future
measurements should retain the workload and warm-up behavior, report all five
samples, and compare medians on the same host and toolchain where possible.

## 2026-08-06 after S1 (finite `f64` scalars)

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.0
- five process-level samples after the benchmark executable was cached
- per-query samples: 6.064, 6.026, 6.095, 6.065, and 6.093 ms
- median: **6.065 ms/query**

The workload contains no float literals; the change to bare-literal
classification is not measurable on this benchmark.

## 2026-08-06 after S2 (mixed numeric arithmetic)

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.0
- five process-level samples after the benchmark executable was cached
- per-query samples: 6.305, 6.358, 6.218, 6.113, and 6.252 ms
- median: **6.252 ms/query**

The workload performs no arithmetic; the median is within run-to-run noise of
the 2026-07-30 baseline.

## 2026-08-06 after S3 (typed floats and owned results)

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.0
- five process-level samples after the benchmark executable was cached
- per-query samples: 6.277, 6.093, 6.110, 6.117, and 6.234 ms
- median: **6.117 ms/query**

Project S is complete; the median remains within run-to-run noise of the
2026-07-30 baseline.
