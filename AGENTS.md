This repo uses ReScript `.res` files alongside TypeScript and other sources.

Style and syntax guidelines:

- For ReScript array literals, always use the JavaScript/TypeScript-style syntax `[...]` (for example, `[1, 2, 3]`), **not** the Reason/OCaml-style `[| ... |]`.
- When adding or editing ReScript code, follow the existing style in nearby modules unless explicitly overridden here.
- Prefer the stdlib names actually available in this codebase: use `min` instead of `Int.min`, `List.toArray` instead of `Array.of_list`, and build arrays with loops or lists (then `List.toArray`) instead of `Array.init`.
- When discarding a value, pipe to `ignore` (e.g. `expr->ignore`) rather than using `let _ = expr`.
