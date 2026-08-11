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

## 2026-08-07 cost model work attribution

The model above learned two estimates from one shared work counter without
partitioning what it counted between them. Three corrections, none of which
change what the model decides on the workloads recorded above:

- Maintenance cost was divided by the number of relations a batch *named*
  rather than the number of base facts it *changed*. Re-inserting a fact the
  database already holds and deleting one it does not are no-ops, so a batch
  naming eight of them alongside one real change recorded roughly an eighth
  of the true per-fact cost. Since the estimate halves the weight of history
  on each update, a few such batches were enough to pin the model on
  maintenance. Measured directly: the same single insertion recorded 71 units
  per fact when named alone and 8 when named alongside seven no-op deletions.
- A maintenance attempt that falls back to a rebuild — the path an update
  takes when it reaches negation or an unmaintainable aggregate — charged
  that rebuild to *both* estimates, moving them in opposite directions from
  one event. Rebuild work is now claimed by the rebuild estimate and excluded
  from the enclosing maintenance measurement, so every candidate examined is
  attributed to exactly one estimate.
- An update that changes nothing is no longer counted as a decision. This one
  is not observable through the public API: both callers wrap the decision in
  a transaction that is discarded when nothing changed, so the miscount never
  reached a committed database.

Re-measured on this host after the corrections, the choices are identical to
the table above — maintain 37/40, recompute 36/40, recompute 37/40, maintain
281/300 — and the automatic policy lands 3.7 to 6.0 percent above the pinned
winner rather than 6 to 10. Absolute times are not comparable with that table,
which was recorded on a different host.

The workloads that exercise these paths are not the ones recorded here: each
benchmark batch names one insertion and one deletion of facts that mostly do
exist, so realized and named counts nearly agree, and fallbacks are rare
outside the negation row. The corrections matter for workloads that batch
speculative updates or that repeatedly fall back, neither of which is
currently benchmarked.

## 2026-08-07 after M7 (deletion through seeded structural rules)

Before M7, deleting a fact a seeded structural rule reads sent the whole
stratum to a dirty-stratum rebuild, because over-deletion could not name the
head such a rule derived. It now enumerates that head out of the closure. The
question the phase was required to answer is whether that is worth doing, and
the answer depends entirely on the shape of the deletion, so the benchmark
measures both extremes:

```sh
zig build benchmark-structural-deletion -Doptimize=ReleaseFast
```

The workload is `prefix(H!T, N) :- prefix(T, M), allowed(H), N = M + 1` over a
single 120-element list, which derives one `prefix` fact per suffix plus a
`deep` consequence for each — 361 closure facts in all. The `leaf` shape
deletes `allowed` for the list's outermost element, invalidating exactly the
longest prefix; the `base` shape deletes `prefix([], 0)`, invalidating every
one of them. Deletion and restoration are timed separately, because only the
deletion half runs the code this phase added.

| Shape | Policy | ns/delete | ns/restore | over-deleted | rederived |
| --- | --- | --- | --- | --- | --- |
| leaf | incremental | 183089 | 432754 | 2 | 0 |
| leaf | recompute | 7364337 | 7584120 | 0 | 0 |
| leaf | automatic | 184091 | 1513912 | 2 | 0 |
| base | incremental | 4748110 | 7689291 | 239 | 0 |
| base | recompute | 48221 | 7428912 | 0 | 0 |
| base | automatic | 4679102 | 7577583 | 239 | 0 |

Times are medians of five process-level samples on arm64, macOS 26.5.0, Zig
0.16.0, `ReleaseFast`; counts are per batch. `rederived` is zero because this
program gives no fact a second proof, so the whole cost is over-deletion —
rederivation still runs and still fails once per over-deleted fact.

Incremental deletion is about **40x faster** than the rebuild on the leaf
shape and about **100x slower** on the base shape. Both extremes have the same
cause. Over-deletion through a seeded rule cannot constrain its closure
lookup — the seed argument is only partially fixed, by its tail, and the other
head arguments are computed downstream of it — so each over-deleted fact
rescans the head relation, which is quadratic in the number of facts the
deletion invalidates. On the leaf shape that number is one. On the base shape
it is all of them, and the rebuild it is compared against is unusually cheap
there: with the base case gone the recursion derives nothing, so recomputing
the stratum costs a single empty round. Per delete-and-restore cycle, where
the restore pays for a real rebuild, the loss narrows to about **1.6x**.

Two consequences worth recording. The automatic policy chooses maintenance on
both shapes, which is right on the leaf and wrong on the base: the model holds
one learned rebuild estimate and cannot tell a rebuild that recomputes
everything from one that finds nothing. And the fix for the base shape is not
in this phase — it is a closure index keyed by the seed argument's tail rather
than by whole values at bound positions, which would make over-deletion linear
and is a change to the storage contract for a single consumer.

The other benchmarks are unchanged, as expected: no existing workload
over-deletes a seeded rule's head. `benchmark-maintenance` measured 642794,
712348, 867990 and 339653 ns/batch for the four incremental rows, and the
25-node baseline 133875 ns/change with incremental maintenance against
1101254 with recomputation — all within host variation of the M6 records.

## 2026-08-07 after P3 (join planning)

P3 reorders an already-safe body at evaluation time by how many candidate
facts each goal is expected to examine. Two things are measured: whether the
planned order beats the stored order on the shapes the phase named, and
whether the planning itself costs anything on the workloads that were already
fast.

### The planned order against the stored order

```sh
zig build benchmark-join-planning -Doptimize=ReleaseFast
```

Each workload runs twice on identical databases, once with `.source_order` —
the order admission stores, which is what the engine did before this phase —
and once with `.cost_based`. Both are checked to answer the same rows.

| Workload | Stored order | Planned | Ratio |
| --- | --- | --- | --- |
| sparse join | 145664 | 103702 | 1.40x |
| dense join | 169370 | 160200 | 1.06x |
| recursive closure | 32158 | 32704 | 0.98x |
| empty aggregate | 111483 | 107764 | 1.03x |
| large aggregate groups | 81712 | 80231 | 1.02x |

Medians of five process-level samples, ns/query, arm64, macOS 26.5.0, Zig
0.16.0, `ReleaseFast`.

Only the sparse join moves much, and that is the expected shape: it is the one
where the two orders differ in how many bindings the join produces rather than
only in which index answers it. The other four are cases where the source
order was already the order the planner picks — which is the honest result for
hand-written programs, and the reason the planner is worth more to rule
evaluation, where a body is re-solved once per delta round, than to a query
asked once.

### The existing workloads

| Workload | Before P3 | After P3 | Ratio |
| --- | --- | --- | --- |
| aggregation, 10 queries (ns/query) | 52987 | 52566 | 1.01x |
| aggregation, incremental edge change (ns) | 117495 | 101433 | 1.16x |
| aggregation, recomputed edge change (ns) | 896745 | 637033 | 1.41x |
| materialization, repeated query (ns) | 22462 | 23087 | 0.97x |
| structural leaf, incremental delete (ns) | 170368 | 156956 | 1.09x |
| structural base, incremental delete (ns) | 4673427 | 4620493 | 1.01x |

Medians of five process-level samples on the same host. `benchmark-maintenance`
and `benchmark-projected-aggregate` are within host variation of their M6 and
M5 records; the projected-aggregate workload is about 5% slower, which is
planning overhead on one- and two-goal bodies that planning cannot improve.

Recomputing a stratum is where planning pays: a rebuild re-solves every rule
body once per delta round, so a better order is charged for once and collected
many times.

### What the numbers exposed

Two findings the phase did not set out to make.

The first attempt let the *planner* decide whether to look a goal up through
an index or scan the relation, from its running estimate of how many bindings
would reach the goal. That fed back on itself: a plan that declined to build
an index left the index unbuilt, so the next plan saw no statistic for it and
declined again. It fixed the sparse join and cost 3x on structural deletion
while giving back the whole recursive-closure gain. The decision belongs to
the store, which can see how often a pattern is asked for — `lookup` now
answers the first request for a pattern with the relation and builds the index
on the second — and with that in place the sparse join is 1.40x faster with no
loss anywhere else.

The second is a limit on how much planning can know. Every statement runs on a
clone, and cloning drops the store's caches, so a query's planner sees
relation sizes but never an index statistic, and any index the query uses is
built for that one query. Planning is fully statistic-driven only on the
rule-evaluation path, where the store lives across delta rounds — which is
also where the measured gains are. Making the caches survive `clone` is the
lever for the query path, and it is P1 lifecycle work.

## 2026-08-08 caches that survive a clone

The limitation P3 recorded was that every statement runs on a clone, and
cloning dropped the store's lookup caches. Measured before changing anything,
by counting entries scanned during a cache rebuild:

| Workload | Entries cloned | Membership rebuilt | Buckets rebuilt | Pattern rebuilt |
| --- | --- | --- | --- | --- |
| 10 join queries over a 20,500-fact closure | 205000 | 0 | 203000 | 203000 |
| 10 single-goal queries over the same | 205000 | 0 | 203000 | 0 |
| loading 2000 facts with `addFact` | 1999000 | 1999000 | 0 | 0 |

So a join query made three passes over the closure where one was inherent:
the clone itself, plus a rebuild of the buckets and of the one pattern index
it used. Membership, which a query never probes, was rebuilt in full on every
`addFact` instead.

`RelationStore.clone` now carries the caches that are worth carrying. Buckets
and pattern indexes describe the entry list by position and are keyed by
hashes of interned value identifiers, both of which a clone preserves exactly.
Membership is keyed by facts, so a copy would have to re-key and rehash — which
is what building it costs — and it stays lazy.

Pattern indexes are carried only when dense. Copying an index costs an
allocation per group; rebuilding it costs a hash per entry. Copying every index
unconditionally was measured first, and it cost 19% on the repeated-query
workload — a 666-fact closure holding seven indexes over 360 groups, almost
none of which that query touches. Gating on density turned that into a gain.

Best of ten samples per side, pooled from two independent runs, ns, arm64,
macOS 26.5.0, Zig 0.16.0, `ReleaseFast`:

| Workload | Before | After | Ratio |
| --- | --- | --- | --- |
| join planning, recursive closure | 31816 | 21750 | 1.46x |
| materialization, repeated query | 22475 | 19668 | 1.14x |
| maintenance, insert-only batch | 605415 | 544614 | 1.11x |
| join planning, large groups | 80547 | 73539 | 1.10x |
| join planning, empty aggregate | 102647 | 96493 | 1.06x |
| aggregation, incremental edge change | 100454 | 95370 | 1.05x |
| maintenance, mixed batch | 821093 | 800657 | 1.03x |
| join planning, dense join | 166160 | 164435 | 1.01x |
| maintenance, delete-only batch | 711476 | 702021 | 1.01x |
| aggregation, 10 queries | 52016 | 52512 | 0.99x |
| aggregation, recomputed edge change | 650825 | 658229 | 0.99x |
| join planning, sparse join | 98843 | 106487 | 0.93x |

The sparse join is not a regression from this change, and the reason is worth
recording because the number looks like one. That workload has no rules, so
nothing ever populates a cache on the committed store: instrumenting the
copy shows twenty clones copying zero buckets and zero groups. Guarding the
copy at run time so it provably does nothing did not recover the difference
either, and adding an unrelated never-called function to the same file moved
the figure by the same amount. It is code layout. A benchmark whose inner loop
is a 2001-entry clone is sensitive to it at roughly this magnitude, in both
plan policies at once, which is also why both columns of that row move
together.
