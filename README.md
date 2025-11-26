# Reactivity in Back-ends: A Practical Guide

**Target audience:** Back-end developers curious about reactive systems

## What is reactivity?

Think of reactivity like **spreadsheet formulas for your back-end**. When you update a cell in Excel, all dependent formulas recalculate automatically. Reactive back-ends work the same way: when your data changes, all derived views update automatically and push fresh data to clients—without you manually tracking what needs to refresh.

## Why should you care?

Traditional back-ends require you to manually:
- Track which data depends on what (dependency graphs)
- Figure out what to invalidate when something changes
- Wire up notification logic to tell clients about updates
- Handle edge cases where clients see stale data

**Reactive back-ends eliminate this boilerplate.** You define your data and relationships once; the runtime handles propagation automatically.

## This Example: A Minimal Reactive Service

This repo demonstrates SkipRuntime—a reactive engine with ReScript bindings—through a simple working example.

### What it does

We build a tiny service with:
- **Input collection:** A key-value store (`input`) that starts with `foo → "bar"`
- **Reactive resource:** An `echo` view that automatically mirrors whatever's in `input`
- **Two APIs:**
  - **HTTP** for reading data and making updates
  - **SSE (Server-Sent Events)** for streaming live updates to clients

### The magic moment

1. Read `echo` → get `{foo: "bar"}`
2. Update `input` → set `foo → "baz"` and add `bar → "qux"`
3. Read `echo` again → automatically get `{foo: "baz", bar: "qux"}`
4. Subscribe via SSE and watch updates arrive in real-time as they happen (no polling): the runtime pushes the updated entries to you without another request.

**No manual invalidation code. No cache busting. No diffing logic.** The runtime tracks dependencies and pushes updates automatically.

## Running the live demo (LiveClient)

```bash
npm install
npm run build
node examples/LiveClient.res.js
```

**Expected output:**
```
server: starting wasm service on ports 18080/18081…
server: service started
live client: initial getAll [ [ 'foo', [ 'bar' ] ] ]
live client: after update getAll [ [ 'bar', [ 'qux' ] ], [ 'foo', [ 'baz' ] ] ]
live client: subscribing to http://127.0.0.1:18081/v1/streams/...
live client: SSE chunk event: init
id: …
data: [["bar",["qux"]],["foo",["baz"]],["sse",["ping"]]]
server: service closed
```

Notice: We never wrote code to update `echo`. It happened automatically when `input` changed.

## How reactivity works here

1. **Define relationships once:** "Echo mirrors input"
2. **Runtime tracks dependencies:** Skip knows `echo` depends on `input`
3. **Write triggers propagation:** Update `input` → runtime recomputes `echo` → clients get fresh data
4. **Subscribe for live updates:** Open an SSE stream and receive updates as they happen, no polling needed

The Skip runtime handles all the plumbing—dependency tracking, incremental recomputation, and streaming. You just declare what depends on what.

## Requirements

- Works on current Node via wasm (no native runtime here; native is Linux-only). Runtime recommends Node >=22.6 <23 for native builds, but the wasm path has worked on newer Node in practice.
- Two available ports (defaults: 18080 for HTTP, 18081 for SSE).
- `npm install` to grab Skip packages.

## Tests
- `npm test` builds and runs the live client (`examples/LiveClient.res.js`) on ports 18080/18081.

## Reactive combinators

Skip’s service graphs are built from composable operators on collections. The most important one in this repo is `reduce`.

Conceptually, its type is:

- `reduce : collection<k, v> -> reducer<v, a> -> collection<k, a>`

On the Skip side (see `bindings/SkipruntimeCore.res:80` and `bindings/SkipruntimeCore.res:332`), that’s exposed as:

- `EagerCollection.reduce : (~params=?, collection<'k, 'v>, reducer<'v, 'a>) -> collection<'k, 'a>`
- where a reducer is built as `Reducer.make(~initial, ~add, ~remove=?)`

A reducer is a small state machine:

- `initial(params) : option<'a>` – produce the starting accumulator (or `None` to say “no value yet”)
- `add(acc, value, params) : 'a` – incorporate a newly-seen value into the accumulator
- `remove(acc, value, params) : option<'a>` – forget a value; returning `None` tells the engine “I can’t update incrementally for this change, please recompute from scratch for this key.”

`EagerCollection.reduce` maintains one accumulator per key. For each key `k`, the runtime:

- Starts from `initial` (or a recomputed value).
- When dependencies change, computes the *old* multiset of contributing values and the *new* multiset.
- Calls `remove` once for each value that used to contribute under `k` (the `old` slice).
- If all `remove` calls return `Some(acc')`, calls `add` once for each value that now contributes under `k` (the `new` slice).
- If any `remove` returns `None`, discards the accumulator and recomputes it from scratch via `initial` + `add` over all current values for `k`.

The contract for `reduce` is:

- **Purity:** `initial`, `add`, and `remove` must be pure and depend only on their arguments.
- **Correctness under change:** For any key, starting from a valid accumulator for some multiset of values and applying the runtime’s sequence of `remove`/`add` calls (or the full recompute path when `remove` returns `None`) must yield the same result as recomputing from scratch over the current values.

This contract lets the runtime maintain derived collections incrementally: when inputs change, only affected keys are updated, and for each key the engine updates the stored accumulator using your `remove`/`add` implementation or falls back to a full recompute if you signal that incremental updates are too hard.

## LiveHarness (advanced demo)

After LiveClient, `examples/LiveHarness.res` + `LiveHarnessService.*` show these combinators in action on a slightly richer service.

The service exposes:

- An input collection `numbers : string -> number`, initially `[a→1, b→2, c→3, d→4, e→5, f→6, g→7, h→8, i→9, j→10]`.
- A derived collection `doubled`, built with a mapper that multiplies each number by 2.
- Two derived sums over `numbers`, both keyed under `"total"`:
  - `sumNaive`, using a reducer that opts out of incremental removal.
  - `sumInc`, using a reducer that fully obeys the incremental contract.

In `LiveHarnessService.*`:

- `DoubleMapper` implements `doubled`.
- `TotalMapperNaive` / `SumReducerNaive` implement `sumNaive`.
- `TotalMapperInc` / `SumReducerInc` implement `sumInc`.

The tricky part for this instance is the reducer contract on removal:

- For `sumNaive`, `add` does `acc + value`, but `remove` always returns `null`. Via the reducer bridge, that maps to `None` at the engine level, so the first `remove` for a key causes the engine to bail out of incremental mode and recompute that key from scratch using `initial` + `add` over all current values.
- For `sumInc`, `add` still does `acc + value`, but `remove` does `acc - value`. That satisfies the incremental contract for a sum (the accumulator always equals the sum of the current values), so the engine can stay on the purely incremental path: it applies all `remove` calls for the `old` slice and then all `add` calls for the `new` slice, without ever triggering a full recompute.

The harness in `examples/LiveHarness.res` runs two phases and counts how many times the mappers and reducers run. Counters are exported via `resetRunStats` / `getRunStats` and logged from ReScript.

**Naive phase (`sumNaive`):**

- Start from `numbers = [a→1, b→2, c→3, d→4, e→5, f→6, g→7, h→8, i→9, j→10]`.
- Snapshot `numbers`, `doubled`, and `sumNaive`:
  - `numbers = [a→1, b→2, …, j→10]`
  - `doubled = [a→2, b→4, …, j→20]`
  - `sumNaive = [total→55]`
  - Counters: `totalNaiveMapperRuns = 10`, `sumNaiveAddRuns = 10`, `sumNaiveRemoveRuns = 0`.
- Change `numbers["c"]` from `3` to `5`, then snapshot again:
  - `numbers = [a→1, b→2, c→5, d→4, e→5, f→6, g→7, h→8, i→9, j→10]`
  - `doubled = [a→2, b→4, c→10, d→8, …, j→20]`
  - `sumNaive = [total→57]`
  - Counters: `totalNaiveMapperRuns = 11`, `sumNaiveAddRuns = 20`, `sumNaiveRemoveRuns = 1`.

Here the deltas are the story:

- `sumNaiveAddRuns` goes from `10` to `20` (+10) even though we only changed one entry (`c: 3→5`). Those extra 10 calls come from the engine’s full recompute path: it calls `add` once for each current value `[1, 2, 5, 4, 5, 6, 7, 8, 9, 10]` under `"total"`.
- `sumNaiveRemoveRuns` goes from `0` to `1` (+1), matching the first old value `1` that caused `remove` to return `null` and short-circuit incremental updates.

Because `remove` returns `null`, the runtime calls it once on the first old value, sees `None`, and then recomputes the accumulator from scratch by rerunning `initial` + `add` over all current contributing values for `"total"`. That's why we see 1 remove triggering a full recompute with 10 new adds, rather than a sequence of removes and then adds for each value in the old/new slices.

**Incremental phase (`sumInc`):**

- Reset counters, keep `numbers = [a→1, b→2, c→5, d→4, e→5, f→6, g→7, h→8, i→9, j→10]`.
- Snapshot `numbers`, `doubled`, and `sumInc`:
  - `numbers = [a→1, b→2, c→5, d→4, …, j→10]`
  - `doubled = [a→2, b→4, c→10, d→8, …, j→20]`
  - `sumInc = [total→57]`
  - Counters: `totalIncMapperRuns = 10`, `sumIncAddRuns = 10`, `sumIncRemoveRuns = 0`.
- Change `numbers["d"]` from `4` to `7`, then snapshot again:
  - `numbers = [a→1, b→2, c→5, d→7, e→5, f→6, g→7, h→8, i→9, j→10]`
  - `doubled = [a→2, b→4, c→10, d→14, …, j→20]`
  - `sumInc = [total→60]`
  - Counters: `totalIncMapperRuns = 11`, `sumIncAddRuns = 20`, `sumIncRemoveRuns = 10`.

Here the contrast between naive and incremental is visible:

- `TotalMapperInc` runs only once per key, so its counter increases from 10 to 11 when `d` changes.
- `SumReducerInc` updates its accumulator using `add(acc, v) = acc + v` and `remove(acc, v) = acc − v`. For the second update, the engine calls `remove` 10 times (for the old slice of 10 values) and `add` 10 times (for the new slice of 10 values), and all of those calls are applied incrementally to the existing accumulator—there is no full recompute, but the work still scales with the size of the `"total"` slice.

Why do both sums still see all the values in their `old`/`new` slices? At the sum layer, the parent collection is the mapped `numbers.map(TotalMapper*)`, which has a single key `"total"` whose values are the concatenation of all contributions from `a` through `j`. When any upstream key changes, the parent’s `"total"` entry is rebuilt as a full list, so the reducer always sees the entire previous slice (e.g. `[1, 2, 5, 4, 5, 6, 7, 8, 9, 10]`) and the entire new slice (e.g. `[1, 2, 5, 7, 5, 6, 7, 8, 9, 10]`) for that key. Reactivity here is *per collection and per key*: only the `"total"` key in the sum resource is updated when `numbers` changes, but within that key the engine still processes all values in the old/new slices rather than a minimal per-value diff.

### Incremental sums and “Δ-only” work

You might reasonably ask:

> I want a sum whose engine cost per update is proportional to the size of the change (Δ), not to the total number of values contributing to the sum. Is that possible at all?

With the current reducer API, there are two answers:

- Inside a single `reduce` today, **no**: the engine always passes you the entire previous slice and the entire new slice for each dirty `(source, key)`. You cannot tell it “only this one value changed, just call `add(7)`.”
- You can reduce per-update work by changing the graph shape: first maintain per-key sums, then sum those per-key sums. Each change then touches:
  - the per-key sum for the changed key (truly O(1) at this stage); and
  - the top-level sum of per-key sums (still O(n) due to how slices work, see below).

Below is the concrete reasoning and a pattern you can actually use.

#### 1. Why a single `reduce` isn’t “Δ-only” today

At the engine level, for any reducer (including TS reducers), updates go through a helper like `BaseTypes.Reducer.update`:

- The engine maintains a per-key accumulator in a small array `state`.
- For a given dirty `(source, key)` it provides:
  - `state`: the previous accumulator for that key.
  - `old`: the full array of values this arrow previously contributed for that `(source, key)`.
  - `new`: the full array of values it now contributes.
- It then runs:
  - `remove(acc, v)` once for each `v` in `old`, updating `acc` each time.
  - If any `remove` returns `None`, it bails out and asks the reducer to recompute from scratch via `initial` + `add` over all current values for the key.
  - Otherwise it runs `add(acc, v)` once for each `v` in `new`.

Crucially:

- `old` is *everything* this `(source, key)` used to write, not just the changed elements.
- `new` is *everything* it writes now, not just the changed elements.

There is no hook (from JS/TS) to say “these are the individual elements added/removed for this key”; the engine always loops `for (x in old) remove(...)` then `for (x in new) add(...)`.

So per dirty `(source, key)`, the engine’s work is Θ(`old.length + new.length`), regardless of how clever your `remove` is. That is already incremental at the graph level (only dirty keys/sources are touched), but not Δ-only at the per-key value level.

Given that, you cannot get a true Δ-only sum (only touching changed values) inside a single `reduce` call today.

#### 2. How to get an “incremental total sum” anyway: change the graph

What you can do instead is:

- Avoid a one-shot `numbers.map(…) -> "total"` + `reduce(Sum)` that collapses everything under one key—this necessarily makes the slice for `"total"` large and every change hits that whole slice.
- Do it in two stages:
  1. Maintain per-key sums on the `numbers` collection.
  2. Maintain a sum of those per-key sums.

Then changing `numbers["d"]` only:

- recomputes the reducer for key `"d"` in stage 1 (cost proportional to the number of values under `"d"`), and
- updates the stage-2 "sum of sums"—but the engine still processes all per-key sums in the old/new slices for `"total"` (see detailed breakdown below).

In TypeScript terms:

**Stage 1: per-key sum**

- A reducer that maintains `sum(values for this key)`:
  - `initial = 0`
  - `add(acc, value) = acc + value`
  - `remove(acc, value) = acc − value`

Applied directly to `numbers` as:

- `perKeySums = collections.numbers.reduce(PerKeySum)`

This yields a collection:

- `"a" → 1, "b" → 2, "c" → 5, …`

Changing only `numbers["d"]` touches only the reducer for key `"d"` in this collection.

**Stage 2: total sum of per-key sums**

- A mapper that collapses per-key sums under `"total"`:
  - `ToTotalMapper.mapEntry(key, values)` reads the per-key sum and emits `["total", sumForKey]`.
- Another incremental sum reducer over those per-key sums (same `add`/`remove` contract as `sumInc`).

Applied as:

- `totalSum = perKeySums.map(ToTotalMapper).reduce(SumReducerInc)`

Now when only `"d"` changes in `numbers`:

- Stage 1 (`numbers.reduce(PerKeySum)`):
  - only `"d"` is dirty, so only the accumulator for `"d"` is touched (in the harness we see one `PerKeySumReducer.remove` and one `PerKeySumReducer.add` when `numbers["d"]` changes).
- Stage 2 (`perKeySums.map(ToTotalMapper).reduce(SumReducerInc)`):
  - only parent key `"d"` in `perKeySums` is dirty,
  - `ToTotalMapper` produces an updated value for `"total"` (the per-key sum for `"d"`),
  - for that `(source, "total")`, the engine still sees the full old and new slices of per-key sums (size equal to the number of keys; 10 in this harness run), so it does a `remove` for each old value and an `add` for each new value.

Total engine work at stage 2 for that change is Θ(size of the `"total"` slice), but only the `"total"` key in the top-level sum is touched, and stage 1 work remains Δ-only at the per-key level.

#### 3. What this means for the total example here

The sums in this repo deliberately take the simpler “collapse everything under `"total"` in one step” shape:

- `collections.numbers.map(TotalMapper*).reduce(SumReducer*)`

where `TotalMapper*` maps every input key to the same child key `"total"`. For any change in `numbers`:

- the mapped collection’s `"total"` key is dirty, and
- at the sum layer, for key `"total"`:
  - `old` is the entire previous list of contributions from the mapped collection, and
  - `new` is the entire new list.

So the sum reducer must walk all of `old` and `new`; there is no smaller slice available for that key. This is still reactive and incremental at the graph level (only the `"total"` key in the sum resource is recomputed), but not Δ-only at the per-value level.

These measurements are evidence of reactivity:

- Derived resources (`doubled`, `sumNaive`, `sumInc`) always match the current `numbers` snapshot without you writing manual update logic.
- Only keys reachable from changed inputs are updated; both sums are driven by the same `old`/`new` value sets for `"total"`, but `sumNaive` immediately forces a full recompute (one `remove`, then fresh `add` calls for all current values), while `sumInc` stays incremental (all `remove` calls over the old slice, then `add` calls over the new slice), which is what the counters make visible in this demo.

Run: `npm run build && node examples/LiveHarness.res.js` (uses ports 18080/18081).

## What else is in the repo
- **Bindings**: `bindings/Skipruntime*.res` plus `bindings/SkipruntimeCoreHelpers.mjs` (class constructors, enums, SSE helper).
- **`examples/Example.res`**: Tiny binding smoke (LoadStatus, error ctor, mapper/reducer wiring) without starting the runtime.
- **`examples/NotifierExample.res`**: Demonstrates notifier callbacks receiving collection updates and watermarks without wiring a full service.
- **`examples/LiveHarness.res` + `LiveHarnessService.*`**: Mapper/reducer-driven service showing reactive snapshots over `numbers`, `doubled`, two sums (`sumNaive`, `sumInc`), and a two-stage sum (`perKeySums` + `sumOfPerKeySums`), with run counters that contrast naive vs incremental recomputation. This is the "next step" after LiveClient if you want to see derived resources recompute on updates.
- **`examples/LiveService.*`**: The minimal reactive service definition used by `LiveClient.res` (typed in TS, emitted as JS). Service files are TS for class-heavy definitions and type checks; compiled JS is used at runtime.

## The bottom line

Reactive back-ends let you **declare what should happen**, not **how to make it happen**. You avoid manually wiring update logic, and clients never see stale data. This example shows the concept end-to-end in ~80 lines of actual service and client code.
