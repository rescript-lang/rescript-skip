# Plan: ReScript bindings for `@skipruntime/core`

Goal: Idiomatic ReScript bindings for Skip runtime APIs.

## Status: Complete ✓

1. **Core bindings** — Types, collections, context, service lifecycle in `bindings/SkipruntimeCore.res`
2. **Server bindings** — `runService` wrapper in `bindings/SkipruntimeServer.res`
3. **Helper bindings** — Broker API + built-in reducers in `bindings/SkipruntimeHelpers.res`
4. **JS helpers** — Class constructors, SSE streaming in `bindings/SkipruntimeCoreHelpers.mjs`
5. **Examples** — `LiveClient.res` (minimal), `LiveHarness.res` (reducer semantics + SSE subscription)

## External service helpers (now bound)

From `@skipruntime/helpers`, for distributed/federated architectures:

- **PolledExternalService** — Poll external HTTP endpoints into reactive collections
- **SkipExternalService** — Connect to remote Skip services via SSE
- **asLeader / asFollower** — Leader-follower replication patterns

## Quick start

```bash
npm install
npm run build
npm test  # runs LiveClient on ports 18080/18081
```

See README.md for full documentation.
