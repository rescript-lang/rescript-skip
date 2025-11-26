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

## What else is in the repo
- **Bindings**: `bindings/Skipruntime*.res` plus `bindings/SkipruntimeCoreHelpers.mjs` (class constructors, enums, SSE helper).
- **`examples/Example.res`**: Tiny binding smoke (LoadStatus, error ctor, mapper/reducer wiring) without starting the runtime.
- **`examples/NotifierExample.res`**: Demonstrates notifier callbacks receiving collection updates and watermarks without wiring a full service.
- **`examples/LiveService.mjs`**: The minimal reactive service definition used by `LiveClient.res`.

## The bottom line

Reactive back-ends let you **declare what should happen**, not **how to make it happen**. You avoid manually wiring update logic, and clients never see stale data. This example shows the concept end-to-end in ~80 lines of actual service and client code.
