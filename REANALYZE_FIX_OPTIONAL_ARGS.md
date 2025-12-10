# Fix: Optional Args Analysis Should Only Consider Live Callers

## Problem

The optional args analysis in reanalyze currently counts ALL call sites when determining which optional arguments are unused or always-used. It should only count call sites from **live** callers.

**Current behavior:**
```
function foo(~optArg=?) { ... }

// dead code:
let deadCaller = () => foo(~optArg=1)  // This call is counted! ❌

// live code:
let liveCaller = () => foo()  // This call is also counted ✓
```

Result: `~optArg` is reported as "sometimes used" even though the only usage is from dead code.

**Expected behavior:**
Only calls from live code should count. If `deadCaller` is dead, its call to `foo(~optArg=1)` should be ignored.

## Root Cause

In `CrossFileItems.ml`, `compute_optional_args_state` processes ALL calls without checking caller liveness:

```ocaml
let compute_optional_args_state (t : t) ~decls : OptionalArgsState.t =
  (* ... *)
  t.optional_arg_calls
  |> List.iter (fun {pos_to; arg_names; arg_names_maybe} ->
         (* No liveness check here! All calls are processed *)
         let current = get_state pos_to in
         let updated = OptionalArgs.apply_call ~argNames:arg_names ... in
         set_state pos_to updated);
```

This runs **before** liveness analysis, so caller liveness is unknown at this point.

## Solution

Move optional args state computation to **after** liveness is computed, and filter by caller liveness.

### Option A: Post-process in `solveDead`

After liveness is computed, recompute optional args state filtering by live callers:

```ocaml
let compute_optional_args_state_live ~cross_file ~decls ~is_live : OptionalArgsState.t =
  let state = OptionalArgsState.create () in
  (* ... *)
  cross_file.optional_arg_calls
  |> List.iter (fun {pos_from; pos_to; arg_names; arg_names_maybe} ->
         (* Only process if caller is live *)
         if is_live pos_from then (
           let current = get_state pos_to in
           let updated = OptionalArgs.apply_call ~argNames:arg_names ... in
           set_state pos_to updated));
  (* ... *)
  state
```

### Option B: Track caller position in optional_arg_calls

Currently `optional_arg_calls` may not store the caller position. Ensure it's stored:

```ocaml
type optional_arg_call = {
  pos_from: Lexing.position;  (* caller position - needed for liveness check *)
  pos_to: Lexing.position;
  arg_names: string list;
  arg_names_maybe: string list;
}
```

## Files to Modify

1. **`CrossFileItems.ml`** / **`CrossFileItems.mli`**:
   - Add `pos_from` to `optional_arg_call` record if not present
   - Add new function `compute_optional_args_state_live` that takes an `is_live` predicate
   - Or modify existing function to accept liveness info

2. **`DeadOptionalArgs.ml`**:
   - Update `addReferences` to store caller position

3. **`DeadCommon.ml`** / **`Reanalyze.ml`**:
   - Call `compute_optional_args_state` after liveness is computed
   - Pass liveness predicate based on `resolvedDead` field

## Testing

After the fix:

```rescript
// dead_caller.res (file with no external refs)
let deadHelper = () => formatDate(~format="ISO")  // Should NOT count

// live_caller.res 
@live
let main = () => formatDate()  // Should count

// Result: ~format should be reported as "never used" (only dead code uses it)
```

## References

- `~/GitHub/rescript/analysis/reanalyze/src/CrossFileItems.ml` - current implementation
- `~/GitHub/rescript/analysis/reanalyze/src/DeadCommon.ml` - liveness solver
- `~/GitHub/rescript/analysis/reanalyze/src/DeadOptionalArgs.ml` - optional args checks


