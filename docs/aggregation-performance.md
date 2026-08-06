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

## 2026-08-06 after P1 (relation store and indexes)

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.0
- five process-level samples after the benchmark executable was cached
- per-query samples: 1.984, 1.987, 1.995, 2.022, and 2.010 ms
- median: **1.995 ms/query**

Routing evaluation through the indexed `RelationStore` reduced the median
from 6.117 ms to 1.995 ms per query (about 3.1x) because recursive-closure
joins now probe lazily built bound-position indexes instead of scanning the
full fact list. Queries still rebuild all derived facts; persistent
materialization is deferred to project M.

## 2026-08-06 after P2 (semi-naive evaluation)

- Zig 0.16.0, `ReleaseFast`
- arm64, macOS 26.5.0
- five process-level samples after the benchmark executable was cached
- per-query samples: 0.923, 0.894, 0.891, 0.910, and 0.922 ms
- median: **0.910 ms/query**

Semi-naive delta rounds reduced the median from 1.995 ms to 0.910 ms per
query (about 2.2x, and about 6.9x against the 2026-07-30 naive baseline)
because recursive rules re-join only the facts appended in the previous
round instead of the full closure every round.

## 2026-08-06 repeated-query workload before M1

`zig build benchmark-materialization -Doptimize=ReleaseFast` runs 20
repeated `summary(S)?` queries over a 14-rule program (recursive closure,
negation, aggregates, and structural list recursion) on the same 25-node
chain. Before persistent materialization every query rebuilt the complete
derived closure.

- Zig 0.16.0, `ReleaseFast`, arm64, macOS 26.5.0
- per-query samples: 5.262, 5.333, 5.168, 5.211, and 5.321 ms
- median: **5.262 ms/query**

## 2026-08-06 after M1 (persistent materialization)

Repeated-query workload:

- per-query samples: 21.9, 22.4, 23.4, 23.3, and 23.3 us
- median: **23.3 us/query** (about 226x over the pre-M1 median)

Aggregation workload:

- per-query samples: 53.2, 52.0, 52.1, 51.8, and 52.7 us
- median: **52.1 us/query** (about 17x over the P2 median)

The first query materializes the closure once; later queries reuse it, so
the remaining per-query cost is the staging clone of the database plus
matching and result construction. Updates mark the first dependent stratum
dirty and the next evaluation repairs only the affected strata.
