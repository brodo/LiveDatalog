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

## 2026-08-25 after F6 (folded planning and execution)

The first folding measurement, because F6 is the first phase with a public
entry point to measure. `zig build benchmark-folding -Doptimize=ReleaseFast`,
best of three runs, ns, arm64, macOS 26.5.0, Zig 0.16.0.

Both sides answer `r(K, v0)` and are checked to return the same rows before
either timing is believed. The folded side reads a *canonical aggregate view*
of `r` — the relation copied, or the relation grouped by its first column — so
Lemma 6.4.2 makes the reconstruction the relation itself and the comparison is
between two ways of computing one answer rather than between two answers. A
view that remembered less would make the folded side quicker by returning less,
which is not a speedup and is why the workload asserts exactness rather than
assuming it.

| Workload | Plan | Cached plan | Folded run | Direct run |
| --- | --- | --- | --- | --- |
| relation copied, 200 keys × 5 values | 55541 | 19208 | 572629 | 92637 |
| relation grouped, 200 keys × 5 values | 36000 | 8792 | 434837 | 93620 |
| relation grouped, 50 keys × 40 values | 27667 | 3708 | 7494756 | 140585 |

Planning and execution are reported apart because they happen at different
rates. Planning is one `foldQuery`: inverting the view, eliminating the terms
the inversion invents, lowering the result. Cached planning is the same call
once the plan exists — compiling the question and normalizing it to a cache
key, three to five times cheaper than folding it again, and the reason the
cache exists. Execution is one `answerFolded`.

**Folded execution is five to fifty times slower than direct execution here,
and the reason is where the plan is kept rather than what the method does.** A
direct query reuses the materialized closure and only solves goals. A folded
plan's rules are in the plan and not in the database, so every call builds a
copy holding what the catalog admits, installs them there, and derives the
reconstruction from nothing. Nothing about a fold requires that; it is what
`answerFolded` costs today, and it is the obvious thing to fix if folded
execution ever needs to be fast. (F7's first item fixed it on 2026-08-26 for
every call but the first; see the section dated then.)

The 50×40 row is a different effect and a real one. Reading values back out of
a stored list goes through `$member`, which is defined by seeded structural
rules over the lists the database holds — so a 40-element list contributes on
the order of 40² membership facts through its tails, and forty times fewer,
longer lists cost sixteen times more than the same 1000 pairs in short ones.
The copied shape has no lists at all and pays none of it. Grouping is the
cheaper *plan* and the more expensive *execution* at this list length, which is
worth knowing before reading much into the view-selection cost model: it counts
stored tuples, and a stored tuple holding a long list is not the same unit of
work as one holding a pair.

No list functions appear in these workloads, so neither side needed the source
database seeded with lists for structural rules to derive over. That asymmetry
is real where it applies — F5's tests need it and the folded side does not —
and reporting it as a speedup would be reporting a difference in what each side
can answer.

## 2026-08-25 after P4's first item (a hash index beside each value table)

The first of P4's four items: `ValueTable.intern` and `scalar.Store`'s three
interning functions no longer walk their table. Each table keeps an index of
positions beside it — the ordered table is still the source of truth and an
identifier is still an insertion position — so nothing observable changed and
every existing test passes unchanged.

A new `zig build benchmark-interning` runs the workloads P4 counted and reports
`internStats` next to the times. The counts are the measurement; the times say
only what the counts were worth on this machine.

### Comparisons, which are the same number on every machine

| Workload | Scalar comparisons | Value comparisons |
| --- | --- | --- |
| load 2000 facts, 2001 distinct atoms | 4001999 → 10591 | 4001999 → 10112 |
| the same 2000 facts as source statements | 4007998 → 12588 | 4001999 → 10149 |
| materialize a 120-element structural recursion | 1239519 → 15326 | 5194046 → 43603 |

The searches themselves are unchanged — 4000 scalar and 4000 value interns for
the fact loads, 7500 and 22622 for the structural one — so these ratios, 378x,
319x and 119x, are what the index did. The three tables are 2001, 2002 and 244
entries; the structural workload's 5.2M comparisons were 22,622 walks of a
362-entry table.

### Times

ns, best of three runs, each itself the best of five in-process repeats,
arm64, macOS 26.5.2, Zig 0.16.0, `ReleaseFast`. Both sides are the same
benchmark binary with only the two interning implementations exchanged.

| Workload | Scan | Index | Ratio |
| --- | --- | --- | --- |
| 2000 facts in one `applyChanges` batch | 7401667 | 622042 | 11.90x |
| materialize a 120-element structural recursion | 6542708 | 3411584 | 1.92x |
| 2000 facts through `addFact` | 269226583 | 244751542 | 1.10x |
| 2000 facts as source statements | 245837875 | 246067625 | 1.00x |

And the existing benchmarks, best of three runs each, on the rows that moved
beyond their run-to-run band:

| Workload | Before | After | Ratio |
| --- | --- | --- | --- |
| structural deletion, base recompute, restore | 7486485 | 4336966 | 1.73x |
| structural deletion, leaf recompute, delete | 7364918 | 4293768 | 1.72x |
| structural deletion, leaf automatic, restore | 1479072 | 870218 | 1.70x |
| aggregation, recomputed edge change | 633858 | 448216 | 1.41x |
| projected aggregate, recompute policy | 25064752 | 19705505 | 1.27x |
| folding, grouped 50x40, folded run | 7220654 | 6345835 | 1.14x |
| maintenance, delete-only recompute | 400686 | 370618 | 1.08x |

Everything else landed between 0.93x and 1.09x, which is this suite's noise
band — the same band the 2026-08-08 entry found code layout moving benchmarks
through. Nothing regressed outside it.

### The fact load did not move, and the batch says why

P4's measurement gate named two workloads that should move most:
`benchmark-structural-deletion` and a fact load. The first moved by 1.7x on
every rebuilding path. **The fact load did not move at all**, and this is worth
recording rather than explaining away, because the item was justified partly on
it.

The reason is not that the item failed to do what it claimed. The same load
run as one `applyChanges` batch — the same 4000 interns over the same growing
table, with the per-statement copying taken away — is 11.9x faster. Interning
was about 92% of what that workload cost.

What the per-statement load spends its time on is the copying. Loading 2000
facts one statement at a time costs 245 ms; the same 2000 facts in one batch
cost 0.6 ms. The interning P4 measured was real, and 4.0M comparisons of short
atoms is still only a few percent of a workload that clones the database 2000
times.

So P4's inference is the part that was wrong, and it is worth correcting in
place: it compared 4.0M *comparisons* against 1,999,000 *cloned entries* and
concluded that loading facts "spends roughly four times as much in interning as
in the per-statement cloning". Those are not the same unit. A cloned entry is
an allocation and a copy; a comparison is a length check and a few bytes. The
diversion P4 recorded is real and the ranking it drew from it was not.

### What it costs

An index is `4` bytes per slot at a load factor of three quarters, so between
5.3 and 10.7 bytes per table entry, allocated only once a table holds
something. A clone copies it with `memcpy`: slots hold positions rather than
keys, and a copy of a table has the same entries in the same order, so every
slot means in the copy exactly what it meant in the original. That is the
opposite answer from the one `RelationStore.membership` gave to the same
question, and for the reason that entry gave — a map keyed by content has to
rehash, and a map keyed by position does not.

## 2026-08-25 after P4's second item (one transaction per run of assertions)

The second of P4's four items, and the largest one left. The parser opened a
statement transaction per statement, and a transaction clones the database, so
a source file of 2000 facts copied 1,999,000 fact entries between its
statements. A run of consecutive assertions now shares one transaction.

Nothing observable changed, and the counts say so directly: every comparison
count in `benchmark-interning` is identical before and after, on all four
workloads. The item changed how often the database is copied, not what is
interned or in what order.

### Times

ns, best of three runs, each itself the best of five in-process repeats,
arm64, macOS 26.5.2, Zig 0.16.0, `ReleaseFast`.

| Workload | Before | After | Ratio |
| --- | --- | --- | --- |
| 2000 facts as source statements | 248348125 | 924833 | 268.5x |
| 2000 facts in one `applyChanges` batch | 623750 | 611125 | 1.02x |
| 2000 facts through `addFact` | 244292833 | 245824750 | 0.99x |
| materialize a 120-element structural recursion | 3416500 | 3428792 | 1.00x |

The batch is the floor for this workload: it is the same 4000 interns and the
same 2000 insertions with exactly one clone. Loading the facts as source
statements now costs **1.51x that floor**, against 398x before. What remains
is parsing and the single clone.

The three rows that did not move are the three that have no run of statements
to share. `addFact` is the embedder's one-fact call and clones per call by
construction; `applyChanges` already was one transaction; the structural
workload measures `materialize`. Extending the same treatment to consecutive
`addFact` calls would mean an embedder-visible transaction, which is what
`applyChanges` already is, so it was not done.

The other benchmarks — structural deletion, folding, join planning,
aggregation, projected aggregates, maintenance, materialization — landed inside
their run-to-run band on every row, with every derived-fact, closure, group and
policy count identical. The test suite is unchanged at about twelve seconds.

### What the guarantee cost

A statement still either commits completely or leaves the database exactly as
it was. Inside a shared transaction that is arranged in three parts.

Interning is the one thing a statement cannot undo where it happens: it goes on
across many calls while parsing, long before the statement knows whether it
will succeed. So `Database.savepoint` records the three interning tables'
lengths and `Database.rollback` truncates them back. Identifiers are insertion
positions, so truncating restores them exactly; the hash index beside each
table is rebuilt in place over the entries that remain, which is why P4's first
item had to land before this one could. Neither half allocates — the failure
being undone is usually an allocation that failed.

Everything else a statement does, it does in one operation that either lands or
does not, and the two that did not are now atomic: `addFactExpr` takes its
insertion back out if marking the closure dirty fails, and `addRuleClauses`
takes its rule back out on every failure below the append rather than on two of
them, and spends the rule identifier only once the rule is certain to stay.
`rollback` asserts the fact store and the rule set are where it left them,
which is what keeps that contract from being quietly broken later.

A run whose *first* statement fails has staged nothing and is discarded rather
than committed. Committing it would leave the database equal to itself but not
identical: the lazily built caches it came away with would be the copy's rather
than its own. The existing "source persistent statements roll back every
allocation failure point" test measures exactly that, in bytes, and it is what
caught this.

The comparison counts go back with the rollback too, so a rolled-back statement
still takes its own share of what interning cost with it — which is what they
meant when every statement had a staging copy of its own.

## 2026-08-26 after P4's third item (a flat pattern index)

The third of P4's four items. A pattern index kept one `ArrayList` per group,
which forced two empirical rules: `clonePatterns` carried an index across a
clone only when its groups averaged four entries or more, because copying cost
an allocation per group; and `lookup` deferred building one to the second
request for a pattern, because building cost an allocation per distinct key.
The index is now one flat `[]u32` with the groups laid out end to end, an
insertion-ordered group list beside it, and an `intern_index.Index` of
positions in that list — the same shape, for the same reason, that P4's first
item gave the value tables. A copy is three `memcpy`s whatever the shape.

**One rule is retired and one survived**, and both outcomes are measured below.
Nothing observable changed: every derived-fact, closure, group, policy and
comparison count in every benchmark is identical, which is also what says plan
choice did not move.

### What the density gate is worth, before and after

The controlled experiment, run today on this machine: `min_group_size` set to
zero — carry every index — under each layout, against the same layout with the
gate in place. `benchmark-materialization`, 20 repeated queries over 14 rules
on a 25-node chain, whose 666-fact closure holds seven indexes.

| Layout | Gate in place | Gate removed | Cost of removing it |
| --- | --- | --- | --- |
| one `ArrayList` per group | 19968 | 29387 | 1.51x |
| flat `[]u32` | — | 19454 | none |

That is the item. The gate existed because copying every index cost half again
as much as the lookups it saved; under the flat layout copying every index
costs nothing measurable and the copy is a hair faster than the gated original
while doing strictly more work. P3's follow-up recorded the same experiment at
19% when it installed the gate; it is 51% today on the same workload.

### What the deferred build is worth, still

Reconsidered on the same evidence and **kept**. Building on the first request
instead of the second, everything else unchanged:

| Workload | Second request | First request | Ratio |
| --- | --- | --- | --- |
| `benchmark-join-planning` sparse join, planned | 110870 | 144227 | 0.77x |
| `benchmark-materialization` per query | 19454 | 20368 | 0.96x |

Nothing else moved. The sparse join is exactly the shape the rule is about: one
goal binds a single value and the goal after it is looked up *once*, on a
staging copy the query discards. Two asks is a cheap proxy for a third, because
the goal inside a join is looked up once per binding the goal outside it
produced — a lookup that happens twice is about to happen four hundred times.
So the rule stayed, and with it F6's decision not to cost index availability:
index availability is still a function of query history, and plan choice is
unchanged on every workload.

### Times

ns, best of three paired runs alternating between the two trees, arm64,
macOS 26.5.2, Zig 0.16.0, `ReleaseFast`.

| Workload | Before | After | Ratio |
| --- | --- | --- | --- |
| join planning, sparse, planned | 108781 | 110870 | 0.98x |
| join planning, sparse, stored order | 159283 | 148179 | 1.07x |
| join planning, dense, planned | 166741 | 153456 | 1.09x |
| join planning, recursive close, planned | 20762 | 22158 | 0.94x |
| join planning, empty aggregate, planned | 96252 | 96895 | 0.99x |
| join planning, large groups, planned | 74347 | 75293 | 0.99x |
| materialization, per query | 19968 | 19454 | 1.03x |
| structural deletion, leaf incremental | 155270 | 157368 | 0.99x |
| structural deletion, base incremental | 4730916 | 4698031 | 1.01x |
| interning, 2000 facts as source statements | 921042 | 923083 | 1.00x |
| interning, materialize 120 deep | 3402375 | 3244625 | 1.05x |
| folding, `grouped 50x40`, folded run | 6328050 | 6316902 | 1.00x |
| aggregation, incremental maintenance | 944250 | 949541 | 0.99x |
| projected aggregate, incremental | 11414698 | 10926988 | 1.04x |

**Every row is inside the run-to-run band.** The measurement gate names
`benchmark-structural-deletion` and a fact-loading workload as the two that
should move most; **neither moved**, and that is recorded here rather than
dressed up. Both are dominated by work a pattern index is not part of —
cloning fact terms, unifying candidates, rebuilding a closure — and the
allocations this item removes were never their cost. What the item bought is
the retired rule above and the memory below.

### Memory

`benchmark-maintenance`, live and peak KiB per batch. These are deterministic:
identical across all three runs of each variant. The third column is the old
layout with the density gate removed, which is what carrying every index used
to cost.

| Batch | Before live/peak | After live/peak | Old layout, no gate |
| --- | --- | --- | --- |
| insert-only automatic | 53 / 408 | 50 / 405 | 53 / 416 |
| insert-only incremental | 53 / 408 | 50 / 405 | 53 / 416 |
| insert-only recompute | 44 / 242 | 43 / 240 | 44 / 244 |
| delete-only automatic | 12 / 335 | 3 / 337 | 12 / 348 |
| delete-only incremental | 30 / 361 | 23 / 352 | 30 / 375 |
| delete-only recompute | 12 / 177 | 3 / 165 | 12 / 184 |
| mixed automatic | 14 / 342 | 5 / 337 | 14 / 357 |
| mixed incremental | 35 / 372 | 28 / 360 | 35 / 399 |
| mixed recompute | 14 / 177 | 5 / 165 | 14 / 185 |
| negation rebuild automatic | 27 / 417 | 20 / 399 | 27 / 420 |
| negation rebuild incremental | 27 / 419 | 20 / 400 | 27 / 423 |
| negation rebuild recompute | 27 / 205 | 20 / 197 | 27 / 210 |

Live bytes fall **4x** on the delete-only and mixed rows — 12 KiB to 3, 14 to
5 — and 7 KiB on every other row that holds indexes. Peak falls up to 6.8%
(177 to 165). The direction is the whole point: under the old layout, carrying
every index *raised* peak on every row; under the flat layout, carrying every
index *lowers* it. A group used to cost a heap allocation, its rounding, an
`ArrayList` header and a hash-map entry; it now costs 24 bytes in an array.

### What absorbs an insert

P4 named `noteInserted` as the obstacle to a flat layout — "a layout that
cannot absorb an insert needs either an overflow list or a rebuild policy" —
and since the batching item landed that path is hotter than it was, because a
run of consecutive assertions maintains one store's caches incrementally
instead of rebuilding them from a fresh clone per statement. This layout needs
neither an overflow list nor a rebuild policy, because it *can* absorb an
insert: a group reserves room past its end and takes the insert in place, and
when the room runs out the group is copied to the end of the array with twice
as much, exactly as an `ArrayList` grows, leaving its old slots behind.

That bounds the array without compaction. A group at capacity `c` has ever
occupied `2c - 1` slots and holds more than `c / 2`, so the array stays under
four times the entries it holds however long it is grown, and equals them
exactly when it is built rather than grown. The `parsed, 2000 facts` row of
`benchmark-interning`, which is what the batching item bought and what this
item had to leave alone, is 923083 ns against 921042 before.

## 2026-08-26 after F7's first item (folded execution that reuses its work)

The F6 section above says folded execution is five to fifty times slower than
direct, and that the reason is where the plan is kept rather than what the
method does: a folded plan's rules live in the plan and not in the database, so
`answerFolded` built a copy holding what the catalog admits, installed them
there, and derived the reconstruction from nothing on every call. **It no
longer does that on every call.** The reconstruction is kept in the plan cache
entry beside the plan that built it, and a repeated `answerFolded` finds the
closure already derived and only solves goals.

`benchmark-folding` therefore reports two execution columns instead of one,
because they are now two different things. *First* is the answer after the
database changed, which still derives. *Repeated* is the answer with nothing
changed in between. Beside each, candidate facts examined — the cost model's
unit, the same number on every machine, and the only column here that says
*why* a call got cheaper.

The change applied between first calls is one fact under the name the plan
reads, put in and taken back out on alternate rounds. It holds a value the
question never asks for, so the answer does not move; it alternates rather than
adding a fresh fact each round because twenty new keys is a 40% larger
extension on `grouped 50x40`, and a first-call time taken over twenty of those
would be reporting the workload growing under it.

Median of five runs, ns per call.

| Workload | First | Repeated | Direct | First cand. | Repeated cand. | Direct cand. |
| --- | --- | --- | --- | --- | --- | --- |
| relation copied, 200 keys × 5 values | 587795 | 30714 | 81156 | 3003 | 201 | 1001 |
| relation grouped, 200 keys × 5 values | 471276 | 31225 | 80906 | 6788 | 201 | 1001 |
| relation grouped, 50 keys × 40 values | 6806016 | 7435 | 109595 | 71805 | 51 | 2001 |

**Repeated folded execution is 0.38x, 0.39x and 0.07x of direct**, where before
this item every folded call was 7.4x, 5.6x and 65x. Against the same call
before the change, on the same benchmark shape, it is 18.6x, 14.6x and 923x
cheaper. The 923x is not a typo and it is not a smaller derivation: on
`grouped 50x40` the derivation was 99% of the call, and what the repeated call
skips is all of it.

**The candidate counts say the reconstruction was reused and not made
smaller.** The first call still examines 3003, 6788 and 71805 candidates —
F6's 3003, 6759 and 71706, plus the handful of structural seeds the change
fact's own value contributes through its tails. Reducing that number is a
separate item and is untouched. What the repeated call examines is 201, 201 and
51: the query's own candidates and nothing else.

**The first call did not get slower**, measured like for like: the engine as it
stood before the item, running the same benchmark with the same change
interleaved, gives medians of 571710, 456045 and 6860997 against 587795, 471276
and 6806016 — +2.8%, +3.3% and −0.8%. That is inside the band this machine
shows for one unchanged binary: the same build's medians moved 5%, 14% and 66%
between two batches an hour apart. `benchmark-maintenance`,
`benchmark-structural-deletion` and `benchmark-interning` are unmoved, and
their comparison counts are identical to the digit.

### A direct query never keeps a pattern index

The repeated folded call examines 201 candidates where the direct call examines
1001, for the same question over the same 1000 pairs, on every one of twenty
iterations. That gap is not folding being clever. P1 builds a pattern index on
the *second* request for a pattern, because a single probe cannot repay a pass
over the relation — and a folded plan now has a store that lives long enough to
make a second request, while `Jatalog.query` clones the database into a staging
copy and drops it, so the first request is never remembered and **a direct
query re-scans however often it is asked**.

The staging copy is not a mistake: it is what keeps a query's interning out of
the database, and the 1001 is the honest cost of the read path as it stands.
But it means part of the margin in the table above is the direct side paying
for an index it never gets to use, and it is a measured reason to weigh the
index-on-second-request rule again on the read path rather than only on the
maintenance path where P4 measured it.

### What this did not touch

The first column is what a folded question costs on a database that changes
between every call, and 588µs, 471µs and 6.8ms is still what that is. Two
separate items remain: maintaining a kept reconstruction from the source
database's change stream rather than rebuilding it, which is the difference
between "as fast as direct on a static database" and "as fast as direct on a
changing one"; and the reconstruction's own candidate count, which F6 traced to
list length. Neither was taken here, because three levers moving at once on a
65x gap would make a regression impossible to attribute.
