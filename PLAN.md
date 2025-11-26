# Plan: ReScript bindings for `@skipruntime/core`

Goal: Add idiomatic ReScript bindings and minimal tests around `@skipruntime/core` so consumers can use Skip runtime APIs from ReScript.

Status legend: `[ ]` = pending, `[~]` = in progress, `[x]` = done.

## Tasks (ordered)
1) Foundation (done)
   - [x] Map API surface and design bindings/layout.
   - [x] JS helper shim for class constructors/enums.
   - [x] Core type bindings (Json/Nullable/Entry/CollectionUpdate/LoadStatus/errors).
   - [x] Collection/Context/Service bindings with a high-level “Natural” layer.
2) Runtime bootstrap (done)
   - [x] Bind `runService` (default platform wasm) from `@skipruntime/server` and helper types from `@skipruntime/helpers`; note engine constraint (Node 22.x target).
3) Live service example (done)
   - [x] Tiny `SkipService` (`LiveService.mjs`) + runnable client (`LiveClient.res`) starting via wasm, exercising `getAll`/`update` via `SkipServiceBroker`, plus SSE subscription logging.
   - Run: `npm run build && node examples/LiveClient.res.js` (requires port binding).
4) Tests/examples (in progress)
   - [~] Add ReScript tests/examples covering mapper/reducer wiring, subscription callbacks, option conversions, enum mapping, and the live service flow (SSE included in LiveClient).
   - Verify: `rescript build && node <example>`; note commands for contributors.
5) Documentation pass (pending)
   - [ ] Update plan/README with usage, wasm vs native notes, engine expectations; run format/lint. Mention repo/package name (`rescript-skip`) and that compiler artifacts are intentionally checked in. Call out `npm test` runs the live client on ports 18080/18081.
   - Rule: add bindings to `bindings/`, keep examples free of ad-hoc externals.

## Inventory (Skip runtime 0.0.19)
- Packages in use: `@skipruntime/core` (bindings target), plus `@skipruntime/helpers`, `@skipruntime/server`, `@skipruntime/wasm` for examples/runtime. (Native dep removed.)
- Core exports: `dist/src/index.js`, `internal.js`, `binding.js`, `json.js`, `std.js` (+ `*-internal.js` variants).
- Public API (from `src/api.ts`): `Mapper`, `Reducer`, `LazyCompute`, `LazyCollection`, `EagerCollection`, `Context`, `Values`, `Entry` = `[K, V[]]`, `CollectionUpdate`, `Resource`, `ExternalService`, `NamedCollections`, `InitialData`, `SkipService`, `Watermark`, `Json/JsonObject/Nullable/DepSafe/Opaque`.
- Errors (`src/errors.ts`): `SkipError`, `SkipUnknownCollectionError`, `SkipUnknownResourceError`, `SkipRESTError`, `SkipFetchError`, `SkipClassNameError`, `SkipNonUniqueValueError`, `SkipResourceInstanceInUseError`.
- Runtime classes/enums (from `src/index.ts`): `LoadStatus`; `ServiceDefinition` (resource builders, createGraph, subscribe/unsubscribe externals, shutdown, derive); `ServiceInstance` (instantiateResource, getAll/getArray, subscribe/unsubscribe, update, reload, close, closeResourceStreams); `ServiceInstanceFactory`; `ToBinding` bridge; internal `EagerCollectionImpl/LazyCollectionImpl/CollectionWriter/ContextImpl/ValuesImpl`.
- Binding surface (`src/binding.ts`): `Notifier` shape, `ResourceBuilder`, `Checker`, `Handle` opaque type, `FromBinding` with collection ops, mapper/reducer/lazycompute/notifier creation, runtime update/fork/reload, context helpers, external service creation.

## Binding design (draft)
- Layout: primary ReScript module `SkipruntimeCore.res` + helper `.mjs` for top-level class constructors and enum/option helpers. Keep externals module-scoped (`@module("@skipruntime/core")` for direct exports; helper module for constructed classes).
- Types: expose `type json = JSON.t`; use `option` for nullable values; keep `Opaque`/`SubscriptionId`/`Watermark` as abstract types (`type subscriptionId` = string but abstracted in interface). Errors bound as `@new` constructors returning `JsExn.t`.
- Collections: model `eager<'k,'v>`/`lazy<'k,'v>` as opaque types with functions (`getArray`, `getUnique`, `map`, `mapReduce`, `reduce`, `merge`, `slice`, `slices`, `take`, `size`). Split overloads into distinct names; use labeled args for defaults (`~ifNone`, `~ifMany`).
- User classes: build mapper/reducer/lazyCompute/notifier/changeManager via JS helper that returns top-level classes with the required methods while capturing ReScript callbacks. ReScript side exposes factory functions taking record of callbacks -> JS constructor.
- Context/Service: bind `ServiceDefinition`, `ServiceInstanceFactory`, `ServiceInstance` methods; expose promise-returning functions (`Promise.t<'a>`), options for nullable params, and helper to subscribe (notifier construction hidden).
- Enums: map `LoadStatus` to a ReScript variant via helper (`["Incompatible","Changed","Same"]` mapping).
- Verification approach: every module addition must pass `rescript build`; add tiny node-run example(s) to exercise mapper/reducer wiring, subscription callbacks, and enum mapping.

## Progress notes
- Repo/package renamed to `rescript-skip`; ReScript 12 config remains.
- Bindings and helpers live under `bindings/`; examples under `examples/`. Compiler artifacts (`.res.js`) are intentionally checked in for clarity.
- Extended bindings cover collections, context, service definition/instance factory + lifecycle, and a “Natural” wrapper layer; `rescript build` passes after type alignment to `CollectionUpdate`/`Watermark`/`DepSafe`.
- Live example (`examples/LiveClient.res`) exercises mapper/reducer wiring, `getAll`/`update`, and SSE flow; `npm test` builds and runs this live client (ports 18080/18081). `Example.res` is a binding-only smoke check.
- Future: add explicit tests for notifier/subscription callbacks and improve example robustness (shutdown on errors, SSE timeout/status handling), then refresh README/plan with current commands and naming.
