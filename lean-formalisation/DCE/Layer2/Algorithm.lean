/-
  Layer2/Algorithm.lean
  Algorithm framework for incremental DCE.
  Contains: IncrAlg, IncrAlgInv, RefcountAlg structures and running deltas.
-/
import DCE.Layer2.Spec

open Multiset
open Reduce

namespace Reduce

section Algorithm
variable {Node : Type} [DecidableEq Node]

/-
An abstract incremental algorithm maintains a refcount state in sync with the
aggregated graph. We model it as a step function and a correctness property:
after applying a fragment delta (add/remove), the produced `RefState` equals `refSpec`
of the updated graph.
-/
structure IncrAlg (Node : Type) [DecidableEq Node] where
  step : GraphState Node → Frag Node → Bool → RefState Node
  correct :
    ∀ g f add?,
      step g f add? =
        refSpec (if add? then GraphState.addFrag g f else GraphState.removeFrag g f)

/-- An incremental algorithm paired with a proof that its state satisfies the spec. -/
structure IncrAlgInv (Node : Type) [DecidableEq Node] where
  step : GraphState Node → Frag Node → Bool → RefState Node
  preserves :
    ∀ g f add?, refInvariant (stepGraph g f add?) (step g f add?)

/-- A refcount-maintaining step that can depend on prior refstate. -/
structure RefcountAlg (Node : Type) [DecidableEq Node] where
  step : GraphState Node → RefState Node → Frag Node → Bool → RefState Node
  preserves :
    ∀ g rs f add?, refInvariant g rs →
      refInvariant (stepGraph g f add?) (step g rs f add?)

/-- A delta is a fragment plus a Boolean indicating add (`true`) or remove (`false`). -/
abbrev FragDelta (Node : Type) := Frag Node × Bool

/-- Advance both the aggregated graph and the refcount state by one delta. -/
def stepPair (A : IncrAlgInv Node)
    (grs : GraphState Node × RefState Node) (d : FragDelta Node) :
    GraphState Node × RefState Node :=
  let g := grs.fst
  let f := d.fst
  let add? := d.snd
  let g' := stepGraph g f add?
  let rs' := A.step g f add?
  (g', rs')

/-- Run an incremental algorithm over a list of deltas, starting from an arbitrary state. -/
def runDeltasAux (A : IncrAlgInv Node)
    (grs₀ : GraphState Node × RefState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  ds.foldl (stepPair (Node:=Node) A) grs₀

lemma runDeltasAux_invariant
    (A : IncrAlgInv Node) (ds : List (FragDelta Node))
    {g : GraphState Node} {rs : RefState Node}
    (h : refInvariant g rs) :
    refInvariant (runDeltasAux (Node:=Node) A (g, rs) ds).fst
                 (runDeltasAux (Node:=Node) A (g, rs) ds).snd := by
  induction ds generalizing g rs with
  | nil =>
      simpa [runDeltasAux] using h
  | cons d ds ih =>
      rcases d with ⟨f, add?⟩
      have hstep := A.preserves (g:=g) (f:=f) (add?:=add?)
      simpa [runDeltasAux, stepPair] using
        (ih (g:=stepGraph g f add?) (rs:=A.step g f add?) hstep)

/-- Run an incremental algorithm over a list of deltas, threading graph and refstate. -/
noncomputable def runDeltas (A : IncrAlgInv Node)
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  runDeltasAux (Node:=Node) A (g₀, refSpec g₀) ds

lemma runDeltas_invariant
    (A : IncrAlgInv Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    refInvariant (runDeltas (Node:=Node) A g₀ ds).fst (runDeltas (Node:=Node) A g₀ ds).snd := by
  have h0 : refInvariant g₀ (refSpec g₀) := refSpec_invariant (g:=g₀)
  simpa [runDeltas] using
    (runDeltasAux_invariant (Node:=Node) A ds (g:=g₀) (rs:=refSpec g₀) h0)

/-- Trivial refcount algorithm: ignores prior refstate and recomputes. -/
noncomputable def refcountRecomputeAlg (Node : Type) [DecidableEq Node] : RefcountAlg Node where
  step g _ f add? := refcountRecomputeStep g f add?
  preserves g _ f add? _ := refcountRecompute_step_inv (g:=g) (f:=f) (add?:=add?)

/-- Advance both the aggregated graph and refcount state using a `RefcountAlg`. -/
def stepPairRef (A : RefcountAlg Node)
    (grs : GraphState Node × RefState Node) (d : FragDelta Node) :
    GraphState Node × RefState Node :=
  let g := grs.fst
  let rs := grs.snd
  let f := d.fst
  let add? := d.snd
  let g' := stepGraph g f add?
  let rs' := A.step g rs f add?
  (g', rs')

/-- Run a refcount algorithm over a list of deltas, starting from an initial refstate. -/
def runRefcountAux (A : RefcountAlg Node)
    (grs₀ : GraphState Node × RefState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  ds.foldl (stepPairRef (Node:=Node) A) grs₀

lemma runRefcountAux_invariant
    (A : RefcountAlg Node) (ds : List (FragDelta Node))
    {g : GraphState Node} {rs : RefState Node}
    (h : refInvariant g rs) :
    refInvariant (runRefcountAux (Node:=Node) A (g, rs) ds).fst
                 (runRefcountAux (Node:=Node) A (g, rs) ds).snd := by
  induction ds generalizing g rs with
  | nil =>
      simpa [runRefcountAux] using h
  | cons d ds ih =>
      rcases d with ⟨f, add?⟩
      have hstep := A.preserves (g:=g) (rs:=rs) (f:=f) (add?:=add?) h
      simpa [runRefcountAux, stepPairRef] using
        ih (g:=stepGraph g f add?) (rs:=A.step g rs f add?) hstep

/-- Run a refcount algorithm over deltas, starting from the spec state. -/
noncomputable def runRefcount (A : RefcountAlg Node)
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  runRefcountAux (Node:=Node) A (g₀, refSpec g₀) ds

lemma runRefcount_invariant
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    refInvariant (runRefcount (Node:=Node) A g₀ ds).fst
                 (runRefcount (Node:=Node) A g₀ ds).snd := by
  have h0 : refInvariant g₀ (refSpec g₀) := refSpec_invariant (g:=g₀)
  simpa [runRefcount] using
    runRefcountAux_invariant (Node:=Node) A ds (g:=g₀) (rs:=refSpec g₀) h0

/-- Any refcount algorithm that preserves the invariant produces states equal to the spec. -/
lemma runRefcount_matches_spec
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    let res := runRefcount (Node:=Node) A g₀ ds
    res.snd.live = liveSet res.fst ∧ res.snd.refcount = refcountSpec res.fst := by
  -- from the invariant obtained by `runRefcount_invariant`
  have h := runRefcount_invariant (Node:=Node) A g₀ ds
  dsimp [refInvariant] at h
  simpa using h

/-- Bundle a concrete refcount step together with its preservation proof. -/
def refcountAlgOfStep
    (step : GraphState Node → RefState Node → Frag Node → Bool → RefState Node)
    (preserves :
      ∀ g rs f add?, refInvariant g rs →
        refInvariant (stepGraph g f add?) (step g rs f add?)) :
    RefcountAlg Node :=
  { step := step, preserves := preserves }

/-- Correctness of any concrete refcount step once bundled as `refcountAlgOfStep`. -/
lemma runRefcount_of_step_matches_spec
    (step : GraphState Node → RefState Node → Frag Node → Bool → RefState Node)
    (preserves :
      ∀ g rs f add?, refInvariant g rs →
        refInvariant (stepGraph g f add?) (step g rs f add?))
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    let res :=
      runRefcount (Node:=Node) (refcountAlgOfStep (Node:=Node) step preserves) g₀ ds
    res.snd.live = liveSet res.fst ∧ res.snd.refcount = refcountSpec res.fst := by
  simpa [refcountAlgOfStep] using
    runRefcount_matches_spec
      (A:=refcountAlgOfStep (Node:=Node) step preserves) (g₀:=g₀) ds

end Algorithm

end Reduce



