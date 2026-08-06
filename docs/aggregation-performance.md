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

Since M6 the same executable also runs two update workloads that toggle one
shortcut edge between queries, once with incremental maintenance and once
with a full rebuild after every change. Historical medians below refer to the
first workload, whose protocol is unchanged.

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

## 2026-08-06 after M2 (insertion deltas)

Neither workload uses the batch-update API, so this is a no-regression
check: the repeated-query median stayed at 23.3 us/query (23.0, 23.7, and
23.3 us) and the aggregation median measured 55.5 us/query (56.9, 54.8, and
55.5 us), within noise of the M1 measurement despite the per-entry support
counter added to the relation store.

## 2026-08-06 after M3 (incremental deletion)

Another no-regression check: the aggregation median measured 52.7 us/query
(52.7, 53.4, and 52.7 us) and the repeated-query median 23.1 us/query
(23.8, 23.1, and 23.0 us), both within noise of the earlier measurements.

## 2026-08-06 after M4 (materialized aggregate groups)

Both workloads only query, so this remains a no-regression check: the
aggregation median measured 52.2 us/query (52.2, 51.8, and 53.4 us) and the
repeated-query median 22.5 us/query (22.2, 22.5, and 22.7 us). The M4 work
changes update cost rather than query cost; a dedicated update benchmark
belongs with the M6 maintenance-statistics work.

## 2026-08-06 projected aggregate view updates: M3 versus M5

`zig build benchmark-projected-aggregate -Doptimize=ReleaseFast` applies
update batches to the projected view `v(X, S) :- p(X, Z), setof(Y, r(X, Y),
S)`, where each of 150 keys has 20 `p` derivations and 10 `r` members. The
first pass over the keys grows each group's member set and drops one of its
derivations; the second restores both. Only `applyChanges` is timed, and
every group is verified afterwards.

The same benchmark source was run against the M3 commit (`decdab3`, before
aggregate maintenance existed, where any change under a `setof` rebuilt the
whole stratum) in a git worktree, and against M5.

| Groups | M3 rebuild | M5 maintenance | Winner |
| --- | --- | --- | --- |
| 30 | 1.480 ms/batch | 1.963 ms/batch | M3, 1.33x |
| 75 | 3.960 ms/batch | 4.378 ms/batch | M3, 1.11x |
| 150 | 10.222 ms/batch | 8.797 ms/batch | M5, 1.16x |

- Zig 0.16.0, `ReleaseFast`, arm64, macOS 26.5.0
- 150-group samples, M5: 8.891, 8.797, and 8.759 ms; median **8.797 ms**
- 150-group samples, M3: 10.684, 10.223, and 10.222 ms; median **10.222 ms**
- 30-group samples, M5: 1.963, 1.956, 1.955, 1.965, and 1.976 ms
- 30-group samples, M3: 1.471, 1.472, 1.487, 1.480, and 1.562 ms

Reading the result honestly: incremental aggregate maintenance is not
uniformly faster than rebuilding the stratum. Rebuild cost grows with the
number of groups, while maintenance cost is dominated by fixed per-batch
overhead — most visibly the full closure snapshot `propagateDeletions`
clones so over-deletion can join against pre-deletion state, which happens
once for the batch and again for each maintenance round that removes a head
tuple. Below roughly 100 groups that overhead exceeds the cost of simply
recomputing every group, and rebuild wins; above it, touching one group
instead of all of them wins and the gap keeps widening.

Two follow-ups this measurement suggests, neither done here: avoid the
whole-closure snapshot by letting matching consult the live closure together
with the pending deletions, and skip incremental maintenance in favour of a
stratum rebuild when the number of affected groups approaches the total. The
M6 completion gate is the natural home for both, since it already calls for
insert, delete, and mixed-update benchmarks.

## 2026-08-06 maintenance cost model

Maintaining and recomputing produce the same database, so the engine now
chooses between them per update from measured cost. Work is counted in
candidate facts examined, which is deterministic and machine-independent;
rebuild cost is learned from dirty-stratum rebuilds and maintenance cost
from maintained batches, each path is measured once to bootstrap, and every
sixteenth decision takes the rejected path so both estimates stay fresh.

The `benchmark-maintenance` and `benchmark-projected-aggregate` workloads
now query after every batch, so work a recompute decision defers is paid
inside the measured region instead of escaping it. Their numbers are
therefore not comparable with the earlier records above, which measured
`applyChanges` alone. Both benchmarks run every policy so the model's choice
can be checked against ground truth.

| Workload | automatic | incremental | recompute | model chose |
| --- | --- | --- | --- | --- |
| insert-only | 647763 | 611103 | 887928 | maintain 37/40 |
| delete-only | 429802 | 701098 | 392144 | recompute 36/40 |
| mixed | 485727 | 810201 | 456523 | recompute 37/40 |
| projected, 150 groups | 10283717 | 9738170 | 23123661 | maintain 281/300 |

Times are ns per batch. The model picks the cheaper path on every workload,
including two that disagree with each other, and lands within about 6 to 10
percent of the pinned winner; the remainder is the cost of exploration.
Neither fixed policy is competitive across all four rows, which is the case
for having a model at all.

Two measurement notes. Insert-only recomputation looks expensive here
because recomputing repairs the recursive stratum from scratch, while
delete-only and mixed favour recomputation because delete-and-rederive pays
for a closure snapshot and rederivation checks. And an earlier version of
this model was anchored on the cost of the *initial* full build, which is a
larger operation than the dirty-stratum rebuild an update triggers; it
consequently preferred maintenance everywhere. Only rebuilds that repair an
update are recorded now.

## 2026-08-06 after M6 (maintenance API and update benchmarks)

Query workload, unchanged protocol: 51.4, 52.9, and 55.2 us/query, median
**52.9 us/query**, within noise of M5.

### 25-node baseline, one edge changed between queries

Both workloads add the same sequence of shortcut edges, one per query, and
differ only in how the closure is brought up to date: `applyChanges`
maintains it incrementally, while `addFact` marks the dependent strata dirty
so the following query recomputes them.

| Path | ns/change |
| --- | --- |
| incremental maintenance | 131204, 132987 |
| recomputation on next query | 865983, 857829 |

Incremental maintenance is about **6.5x faster than recomputation** here,
with zero rebuild fallbacks reported. This is the workload shape incremental
maintenance suits: a large recursive closure where one edge changes a
comparatively small part of it.

An earlier version of this comparison had the recomputing workload apply its
change with `retract`, which since became incrementally maintained itself;
the workload then paid for maintenance and threw the result away. Both
workloads now perform the identical change sequence.

### Insert, delete, mixed, and negation workloads

`zig build benchmark-maintenance -Doptimize=ReleaseFast` builds a 40-node
chain plus 40 aggregate groups of 8 members and reports per batch, for each
update category, the time, the delta sizes, the number of aggregate groups
recomputed, the rebuild fallbacks, and memory measured with a counting
allocator.

| Workload | ns/batch | derived | removed | groups | fallbacks | live KiB | peak KiB |
| --- | --- | --- | --- | --- | --- | --- | --- |
| insert-only | 511994 | 81 | 80 | 40 | 0 | 74 | 420 |
| delete-only | 615869 | 68 | 120 | 40 | 0 | 51 | 366 |
| mixed | 710954 | 76 | 120 | 40 | 0 | 57 | 381 |
| negation rebuild | 246286 | 0 | 0 | 0 | 20 | 27 | 408 |

The `negation rebuild` row updates a predicate read under negation, which is
the documented category that cannot be maintained incrementally. It is
*faster* than the incrementally maintained rows, which is consistent with the
projected-aggregate comparison above: on databases of this size the fixed
per-batch overhead of maintenance — chiefly the staged copy of the database
and the closure snapshot taken for over-deletion — exceeds the cost of
recomputing a stratum. Peak memory is dominated by that staging copy in every
category.

Taken together, the three measurements say incremental maintenance wins when
one change touches a small fraction of a large derived relation, and loses to
recomputation when the derived relation is small or the change touches most
of it. Choosing between them automatically needs a cost model, which no phase
of this project specifies.

## 2026-08-06 after M5 (projected views and CReaM counts)

Still query-only, so another no-regression check: the aggregation median
measured 54.1 us/query (54.1, 51.6, and 59.5 us) and the repeated-query
median 23.6 us/query (23.7, 23.6, and 22.9 us). Neither benchmark defines a
projected aggregate view, so the auxiliary views are empty here and add no
query cost.
