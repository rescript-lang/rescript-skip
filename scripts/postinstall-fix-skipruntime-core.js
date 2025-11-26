#!/usr/bin/env node

// Patch @skipruntime/core so that JS/TS reducers can signal
// engine-level "no accumulator" by returning null/undefined from `remove`.
//
// This rewrites `SkipRuntime_Reducer__remove` to:
// - Call the JS reducer.
// - If it returns null/undefined, return `null` to the Skip engine.
// - Otherwise, export the JSON value as before.

import fs from "node:fs";
import path from "node:path";
import url from "node:url";

const here = path.dirname(new URL(import.meta.url).pathname);
const target = path.join(
  here,
  "..",
  "node_modules",
  "@skipruntime",
  "core",
  "dist",
  "src",
  "index.js",
);

if (!fs.existsSync(target)) {
  // Nothing to patch (e.g., dev without dependencies installed).
  process.exit(0);
}

const originalSnippet = `
    SkipRuntime_Reducer__remove(skreducer, skacc, skvalue) {
        const skjson = this.getJsonConverter();
        const reducer = this.handles.get(skreducer);
        return skjson.exportJSON(reducer.object.remove(skjson.importJSON(skacc), skjson.importJSON(skvalue)));
    }`;

const patchedSnippet = `
    SkipRuntime_Reducer__remove(skreducer, skacc, skvalue) {
        const skjson = this.getJsonConverter();
        const reducer = this.handles.get(skreducer);
        const result = reducer.object.remove(
            skjson.importJSON(skacc),
            skjson.importJSON(skvalue),
        );
        if (result === null || result === undefined) {
            // Signal "no accumulator" to the Skip engine so it can take
            // the fallback path (full recompute via init).
            return null;
        }
        return skjson.exportJSON(result);
    }`;

const code = fs.readFileSync(target, "utf8");

// Idempotent: if already patched, do nothing.
if (code.includes("const result = reducer.object.remove(")) {
  process.exit(0);
}

if (!code.includes(originalSnippet)) {
  console.warn(
    "[postinstall-fix-skipruntime-core] SkipRuntime_Reducer__remove shape has changed; no patch applied.",
  );
  process.exit(0);
}

const updated = code.replace(originalSnippet, patchedSnippet);
fs.writeFileSync(target, updated, "utf8");

console.log(
  "[postinstall-fix-skipruntime-core] Patched SkipRuntime_Reducer__remove to treat null/undefined as engine-level None.",
);

