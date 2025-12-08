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

On the Skip side (see `bindings/SkipruntimeCore.res`), that's exposed as:

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

## LiveHarness (reducer semantics demo)

After LiveClient, `examples/LiveHarness.res` + `LiveHarnessService.*` illustrate how `reduce` works.

The service exposes:

- **`numbers`**: input collection `string → number`, initially `[a→1, b→2, …, j→10]`.
- **`doubled`**: each number multiplied by 2 (demonstrates `map`).
- **`sum`**: total of all numbers under key `"total"` (demonstrates `reduce`).

### How the sum works

In `LiveHarnessService.ts`:

```typescript
class SumReducer implements Reducer<number, number> {
  initial = 0;
  add(acc, value)    { return acc + value; }
  remove(acc, value) { return acc - value; }
}
```

The `sum` resource is built as `numbers.map(TotalMapper).reduce(SumReducer)`, where `TotalMapper` emits every value under the single key `"total"`.

### What happens on update

When `numbers["c"]` changes from `3` to `5`:

1. **Mapper runs once** for the changed key `"c"`.
2. **Reducer sees full slices** for key `"total"`:
   - `old` = all 10 previous values `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]`
   - `new` = all 10 current values `[1, 2, 5, 4, 5, 6, 7, 8, 9, 10]`
3. **Engine calls** `remove` 10 times, then `add` 10 times.

The sum is correct (55 → 57), but the reducer processes O(n) values per update—not just the changed value.

### Why O(n)?

Skip's reactivity is *per collection and per key*. When any upstream key changes, the reducer for `"total"` sees the entire old and new contribution lists for that key. There's no finer-grained "just this value changed" signal at the reducer level.

### Client-side O(1) alternative

For truly O(1) aggregates, subscribe to the reactive collection via SSE and maintain the aggregate client-side:

```rescript
// Subscribe to SSE stream for numbers collection
let streamUrl = await Client.getStreamUrl(opts, broker, "numbers")
ClientSum.subscribe(streamUrl)

// In ClientSum module: O(1) update when SSE delivers changes
let applyUpdate = (key, newValue) => {
  let oldValue = state.numbers->Dict.get(key)->Option.getOr(0.)
  state.total = state.total -. oldValue +. newValue
  state.numbers->Dict.set(key, newValue)
}
```

The harness includes a `ClientSum` module that subscribes to `numbers` via SSE. When the server pushes updates, the client applies them in O(1) time—no polling, no re-fetching the whole collection.

Run:

```bash
npm run build && node examples/LiveHarness.res.js
```

## What else is in the repo

### Bindings (`bindings/`)
- **`SkipruntimeCore.res`**: Core types, collections (`EagerCollection`, `LazyCollection`), operators (`map`, `reduce`, `mapReduce`, `slice`, `take`, `merge`), `Mapper`/`Reducer`/`LazyCompute` factories, notifiers, service instances.
- **`SkipruntimeHelpers.res`**: HTTP broker (`SkipServiceBroker`), built-in reducers (`Sum`, `Min`, `Max`, `Count`), external service helpers (`PolledExternalService`, `SkipExternalService`), leader-follower topology (`asLeader`, `asFollower`).
- **`SkipruntimeServer.res`**: `runService` to start HTTP/SSE servers.
- **`SkipruntimeCoreHelpers.mjs`**: JS helpers for class constructors, enums, and SSE utilities (`subscribeSSE` for streaming).
- **`Fixpoint.res`/`SkipruntimeFixpoint.res`**: Managed fixpoint API for iterative graph algorithms (reachability, shortest paths, etc.).

### Examples (`examples/`)
- **`LiveClient.res`**: Main demo—starts a service, reads/updates via HTTP, subscribes via SSE.
- **`LiveHarness.res` + `LiveHarnessService.ts`**: Demonstrates `map` and `reduce` semantics. Includes `ClientSum`, a client-side O(1) accumulator that subscribes to SSE.
- **`Example.res`**: Binding smoke test—`LoadStatus`, errors, mapper/reducer wiring—without starting the runtime.
- **`NotifierExample.res`**: Demonstrates notifier callbacks receiving collection updates and watermarks.
- **`LiveService.ts`**: Minimal service definition for `LiveClient` (echo resource mirroring input).
- **`DCEExample.res`**: Dead code elimination using the managed fixpoint API—demonstrates incremental graph reachability.
- **`FixpointTest.res`**: Unit tests for the fixpoint API.
- **`JsonOrderingHarness.res` + `JsonOrderingService.ts`**: Tests Skip's JSON key ordering semantics (type ordering, no key collisions).
- **`BoolKVHarness.res` + `BoolKVService.ts`**: Tests boolean key handling.

### Research & Analysis
- **`skip_local_reactive_expressivity.tex`**: Main paper—proves expressive equivalence between Skip's combinators and relational algebra with aggregates. Identifies `filterNotMatchingOn` as the single missing operator needed for RA completeness.
- **`EXAMPLES_PRIMITIVES_ANALYSIS.md`**: Detailed analysis of 48 reactive service examples, classifying each by what primitives it needs (structural, reducer, compute node).
- **`examples_all.tex`** + category files: LaTeX catalogue of the 48 examples organized by pattern (per-key aggregates, windowed views, graph metrics, etc.).
- **`dce_reactive_view.tex`**: Case study on reactive dead code elimination.
- **`incremental_fixpoint_notes.tex`**: Notes on incremental fixpoint computation.
- **`reduce.tex`**: Notes on reducer semantics and well-formedness.
- **`REACTIVE_CALCULUS_NOTES.md`**, **`PLAN.md`**: Working notes and planning documents.

### Lean Formalisation (`lean-formalisation/`)
- **`ReactiveRel.lean`**: Main formalisation—defines combinator and RA expression types, their semantics, compilation functions in both directions, and soundness/completeness proofs.
- **`DCE.lean`** + `DCE/`: Formalisation of reactive dead code elimination with two-layer architecture (aggregation + graph algorithm).
- **`IncrementalFixpoint.lean`**, **`Reduce.lean`**: Additional formalisations for fixpoint and reducer properties.
- **`README.md`**: Documentation for the Lean proofs.

### Research Prompts (`research/`)
Deep research prompts and results covering: Skip ecosystem, streaming analytics, FRP/UI patterns, incremental databases, and coverage analysis.

## The bottom line

Reactive back-ends let you **declare what should happen**, not **how to make it happen**. You avoid manually wiring update logic, and clients never see stale data. This example shows the concept end-to-end in ~80 lines of actual service and client code.
