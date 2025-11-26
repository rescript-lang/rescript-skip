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

- An input collection `numbers : string -> number`, initially `["a"→1, "b"→2]`.
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

- Start from `numbers = [a→1, b→2]`.
- Snapshot `numbers`, `doubled`, and `sumNaive`:
  - `numbers = [a→1, b→2]`
  - `doubled = [a→2, b→4]`
  - `sumNaive = [total→3]`
  - Counters: `totalNaiveMapperRuns = 2`, `sumNaiveAddRuns = 2`, `sumNaiveRemoveRuns = 0`.
- Add a new entry `c→5` to `numbers`, then snapshot again:
  - `numbers = [a→1, b→2, c→5]`
  - `doubled = [a→2, b→4, c→10]`
  - `sumNaive = [total→8]`
  - Counters: `totalNaiveMapperRuns = 3`, `sumNaiveAddRuns = 5`, `sumNaiveRemoveRuns = 1`.

Here the deltas are the story:

- `sumNaiveAddRuns` goes from `2` to `5` (+3) even though we only added one new value (`c→5`). Those extra 3 calls come from the engine’s full recompute path: it calls `add` once for each current value `[1, 2, 5]` under `"total"`.
- `sumNaiveRemoveRuns` goes from `0` to `1` (+1), matching the first old value `1` that caused `remove` to return `null` and short-circuit incremental updates.

Because `remove` returns `null`, the runtime calls it once on the first old value, sees `None`, and then recomputes the accumulator from scratch by rerunning `initial` + `add` over all current contributing values for `"total"`. That’s why we see 1 remove and 3 new adds, rather than a sequence of removes and then adds for each value in the old/new slices.

**Incremental phase (`sumInc`):**

- Reset counters, keep `numbers = [a→1, b→2, c→5]`.
- Snapshot `numbers`, `doubled`, and `sumInc`:
  - `numbers = [a→1, b→2, c→5]`
  - `doubled = [a→2, b→4, c→10]`
  - `sumInc = [total→8]`
  - Counters: `totalIncMapperRuns = 3`, `sumIncAddRuns = 3`, `sumIncRemoveRuns = 0`.
- Add a new entry `d→7`, then snapshot again:
  - `numbers = [a→1, b→2, c→5, d→7]`
  - `doubled = [a→2, b→4, c→10, d→14]`
  - `sumInc = [total→15]`
  - Counters: `totalIncMapperRuns = 4`, `sumIncAddRuns = 7`, `sumIncRemoveRuns = 3`.

Here the contrast between naive and incremental is visible:

- `TotalMapperInc` runs only once per key, so its counter increases from 3 to 4 when `d` is added.
- `SumReducerInc` updates its accumulator using `add(acc, v) = acc + v` and `remove(acc, v) = acc − v`. For the second update, the engine calls `remove` three times (for the old slice) and `add` four times (for the new slice), and all of those calls are applied incrementally to the existing accumulator—there is no full recompute.

Why do both sums still see all the values in their `old`/`new` slices? At the sum layer, the parent collection is the mapped `numbers.map(TotalMapper*)`, which has a single key `"total"` whose values are the concatenation of all contributions from `a`, `b`, `c`, `d`. When any upstream key changes, the parent’s `"total"` entry is rebuilt as a full list, so the reducer always sees the entire previous slice (e.g. `[1, 2, 5]`) and the entire new slice (e.g. `[1, 2, 5, 7]`) for that key. Reactivity here is *per collection and per key*: only the `"total"` key in the sum resource is updated when `numbers` changes, but within that key the engine still processes all values in the old/new slices rather than a minimal per-value diff.

These measurements are evidence of reactivity:

- Derived resources (`doubled`, `sumNaive`, `sumInc`) always match the current `numbers` snapshot without you writing manual update logic.
- Only keys reachable from changed inputs are updated; both sums are driven by the same `old`/`new` value sets for `"total"`, but `sumNaive` immediately forces a full recompute (one `remove`, then fresh `add` calls for all current values), while `sumInc` stays incremental (all `remove` calls over the old slice, then `add` calls over the new slice), which is what the counters make visible in this demo.

Run: `npm run build && node examples/LiveHarness.res.js` (uses ports 18080/18081).

## What else is in the repo
- **Bindings**: `bindings/Skipruntime*.res` plus `bindings/SkipruntimeCoreHelpers.mjs` (class constructors, enums, SSE helper).
- **`examples/Example.res`**: Tiny binding smoke (LoadStatus, error ctor, mapper/reducer wiring) without starting the runtime.
- **`examples/NotifierExample.res`**: Demonstrates notifier callbacks receiving collection updates and watermarks without wiring a full service.
- **`examples/LiveHarness.res` + `LiveHarnessService.*`**: Mapper/reducer-driven service showing reactive snapshots over `numbers`, `doubled`, and two sums (`sumNaive`, `sumInc`), with run counters that contrast naive vs incremental recomputation without the SSE flow. This is the “next step” after LiveClient if you want to see derived resources recompute on updates.
- **`examples/LiveService.*`**: The minimal reactive service definition used by `LiveClient.res` (typed in TS, emitted as JS). Service files are TS for class-heavy definitions and type checks; compiled JS is used at runtime.

## The bottom line

Reactive back-ends let you **declare what should happen**, not **how to make it happen**. You avoid manually wiring update logic, and clients never see stale data. This example shows the concept end-to-end in ~80 lines of actual service and client code.
