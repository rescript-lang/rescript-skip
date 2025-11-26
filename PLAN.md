# Plan: ReScript bindings for `@skipruntime/core`

Goal: Idiomatic ReScript bindings for Skip runtime APIs.

## Status: Complete ✓

1. **Core bindings** — Types, collections, context, service lifecycle in `bindings/SkipruntimeCore.res`
2. **Server bindings** — `runService` wrapper in `bindings/SkipruntimeServer.res`
3. **Helper bindings** — Broker API in `bindings/SkipruntimeHelpers.res`
4. **JS helpers** — Class constructors, SSE streaming in `bindings/SkipruntimeCoreHelpers.mjs`
5. **Examples** — `LiveClient.res` (minimal), `LiveHarness.res` (reducer semantics + SSE subscription)

## Quick start

```bash
npm install
npm run build
npm test  # runs LiveClient on ports 18080/18081
```

See README.md for full documentation.
