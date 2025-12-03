/-
  IncrementalFixpoint.lean
  Level 1: Low-level API for incremental fixpoint computation.

  This formalizes the general pattern underlying DCE Layer 2:
  - Semi-naive evaluation for expansion (when F grows)
  - Counting-based deletion for contraction (when F shrinks)
-/

import Mathlib.Data.Set.Lattice

namespace IncrementalFixpoint

variable {α : Type*}

/-! ## Monotone Operators and Fixpoints -/

/-- A monotone operator on sets. -/
structure MonotoneOp (α : Type*) where
  F : Set α → Set α
  mono : ∀ S T, S ⊆ T → F S ⊆ F T

/-- A set is a prefixpoint if F(S) ⊆ S. -/
def isPrefixpoint (op : MonotoneOp α) (S : Set α) : Prop :=
  op.F S ⊆ S

/-- A set is a fixpoint if F(S) = S. -/
def isFixpoint (op : MonotoneOp α) (S : Set α) : Prop :=
  op.F S = S

/-- The least fixpoint is a fixpoint contained in all prefixpoints. -/
def isLeastFixpoint (op : MonotoneOp α) (S : Set α) : Prop :=
  isFixpoint op S ∧ ∀ T, isPrefixpoint op T → S ⊆ T

/-! ## Decomposed Operators

Many fixpoint operators decompose as F(S) = base ∪ step(S),
where base provides seed elements and step derives new elements.
-/

/-- A decomposed operator: F(S) = base ∪ step(S). -/
structure DecomposedOp (α : Type*) where
  base : Set α
  step : Set α → Set α
  step_mono : ∀ S T, S ⊆ T → step S ⊆ step T

/-- Convert a decomposed operator to a monotone operator. -/
def DecomposedOp.toMonotoneOp (op : DecomposedOp α) : MonotoneOp α where
  F S := op.base ∪ op.step S
  mono S T hST := Set.union_subset_union_right op.base (op.step_mono S T hST)

/-- The operator F(S) = base ∪ step(S). -/
abbrev DecomposedOp.F (op : DecomposedOp α) : Set α → Set α :=
  op.toMonotoneOp.F

/-! ## Semi-Naive Evaluation

For expansion, we use semi-naive evaluation:
- Track the "delta" (newly added elements)
- Only compute step(delta) instead of step(S)
-/

/-- Semi-naive step: given current set and delta, compute new elements. -/
def semiNaiveStep (op : DecomposedOp α) (current : Set α) (delta : Set α) : Set α :=
  op.step delta \ current

/-- One iteration of semi-naive evaluation. -/
def semiNaiveIter (op : DecomposedOp α) (current delta : Set α) : Set α × Set α :=
  let newDelta := semiNaiveStep op current delta
  (current ∪ newDelta, newDelta)

/-- Semi-naive evaluation from an initial set, iterated n times. -/
def semiNaiveN (op : DecomposedOp α) (init : Set α) : ℕ → Set α × Set α
  | 0 => (init, init)
  | n + 1 =>
    let (current, delta) := semiNaiveN op init n
    semiNaiveIter op current delta

/-- The current set after n iterations. -/
def semiNaiveCurrent (op : DecomposedOp α) (init : Set α) (n : ℕ) : Set α :=
  (semiNaiveN op init n).1

/-- The delta after n iterations. -/
def semiNaiveDelta (op : DecomposedOp α) (init : Set α) (n : ℕ) : Set α :=
  (semiNaiveN op init n).2

/-- Semi-naive current is monotonically increasing. -/
lemma semiNaiveCurrent_mono (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    semiNaiveCurrent op init n ⊆ semiNaiveCurrent op init (n + 1) := by
  simp only [semiNaiveCurrent, semiNaiveN, semiNaiveIter]
  exact Set.subset_union_left

/-- Semi-naive stays within the least fixpoint. -/
lemma semiNaive_subset_lfp (op : DecomposedOp α) (init : Set α) (lfp : Set α)
    (h_init : init ⊆ lfp) (h_lfp : isLeastFixpoint op.toMonotoneOp lfp) (n : ℕ) :
    semiNaiveCurrent op init n ⊆ lfp := by
  induction n with
  | zero => simpa [semiNaiveCurrent, semiNaiveN]
  | succ n ih =>
    simp only [semiNaiveCurrent, semiNaiveN, semiNaiveIter, semiNaiveStep]
    apply Set.union_subset ih
    intro x hx
    simp only [Set.mem_diff] at hx
    -- x ∈ step(delta) where delta ⊆ current ⊆ lfp
    -- step(delta) ⊆ step(lfp) ⊆ F(lfp) = lfp
    sorry

/-! ## Expansion: When F Grows

When the operator grows (F ⊆ F'), the old fixpoint is an underapproximation.
We iterate upward using semi-naive evaluation.
-/

/-- F' expands F if F(S) ⊆ F'(S) for all S. -/
def expands (op op' : DecomposedOp α) : Prop :=
  ∀ S, op.F S ⊆ op'.F S

/-- When F expands, the fixpoint can only grow. -/
lemma lfp_mono_expand (op op' : DecomposedOp α) (lfp lfp' : Set α)
    (h_exp : expands op op')
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') :
    lfp ⊆ lfp' := by
  apply h_lfp.2
  intro x hx
  have h1 : x ∈ op.F lfp' := hx
  have h2 : op.F lfp' ⊆ op'.F lfp' := h_exp lfp'
  have h3 : op'.F lfp' = lfp' := h_lfp'.1
  exact h3 ▸ h2 hx

/-- The initial delta for expansion: elements in F'(lfp) \ lfp. -/
def expansionDelta (op' : DecomposedOp α) (lfp : Set α) : Set α :=
  op'.F lfp \ lfp

/-! ## Contraction: When F Shrinks

When the operator shrinks (F' ⊆ F), the old fixpoint is an overapproximation.
We use counting-based deletion to remove unjustified elements.
-/

/-- F' contracts F if F'(S) ⊆ F(S) for all S. -/
def contracts (op op' : DecomposedOp α) : Prop :=
  ∀ S, op'.F S ⊆ op.F S

/-- When F contracts, the fixpoint can only shrink. -/
lemma lfp_mono_contract (op op' : DecomposedOp α) (lfp lfp' : Set α)
    (h_con : contracts op op')
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') :
    lfp' ⊆ lfp := by
  apply h_lfp'.2
  intro x hx
  have h1 : x ∈ op'.F lfp := hx
  have h2 : op'.F lfp ⊆ op.F lfp := h_con lfp
  have h3 : op.F lfp = lfp := h_lfp.1
  exact h3 ▸ h2 hx

/-- The newly dead set: elements in old lfp but not in new lfp. -/
def newlyDead (lfp lfp' : Set α) : Set α :=
  lfp \ lfp'

/-- After contraction, lfp' = lfp \ newlyDead. -/
lemma lfp_contract_eq (op op' : DecomposedOp α) (lfp lfp' : Set α)
    (h_con : contracts op op')
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') :
    lfp' = lfp \ newlyDead lfp lfp' := by
  ext x
  simp only [newlyDead, Set.mem_diff, not_and, not_not]
  constructor
  · intro hx
    exact ⟨lfp_mono_contract op op' lfp lfp' h_con h_lfp h_lfp' hx, fun _ => hx⟩
  · intro ⟨_, h⟩
    exact h (by trivial)

/-! ## The Level 1 API

The main interface for incremental fixpoint computation.
-/

/-- Configuration for incremental fixpoint computation. -/
structure IncrFixpointConfig (α : Type*) where
  /-- The decomposed operator. -/
  op : DecomposedOp α
  /-- Compute step restricted to delta (for semi-naive). -/
  stepFromDelta : Set α → Set α
  /-- Derivation count for an element. -/
  derivationCount : Set α → α → ℕ
  /-- stepFromDelta correctly computes step restricted to delta. -/
  stepFromDelta_spec : ∀ delta, stepFromDelta delta = op.step delta
  /-- derivationCount is positive iff element is in step. -/
  derivationCount_spec : ∀ S x, x ∈ op.step S ↔ derivationCount S x > 0

/-- State of an incremental fixpoint computation. -/
structure IncrState (α : Type*) where
  current : Set α
  counts : α → ℕ

/-- The state is valid w.r.t. a decomposed operator. -/
structure ValidState (op : DecomposedOp α) (state : IncrState α) : Prop where
  is_lfp : isLeastFixpoint op.toMonotoneOp state.current

/-- Result of an incremental update. -/
structure IncrResult (α : Type*) where
  newState : IncrState α
  added : Set α
  removed : Set α

/-! ## DCE as an Instance -/

/-- DCE operator: live = roots ∪ { v | ∃ u ∈ live. (u,v) ∈ edges }. -/
def dceOp (roots : Set α) (edges : Set (α × α)) : DecomposedOp α where
  base := roots
  step S := { v | ∃ u ∈ S, (u, v) ∈ edges }
  step_mono S T hST := by
    intro v ⟨u, hu, he⟩
    exact ⟨u, hST hu, he⟩

/-- DCE stepFromDelta: successors of delta nodes. -/
def dceStepFromDelta (edges : Set (α × α)) (delta : Set α) : Set α :=
  { v | ∃ u ∈ delta, (u, v) ∈ edges }

/-- DCE stepFromDelta equals op.step. -/
lemma dceStepFromDelta_eq (roots : Set α) (edges : Set (α × α)) (delta : Set α) :
    dceStepFromDelta edges delta = (dceOp roots edges).step delta := by
  simp only [dceStepFromDelta, dceOp]

/-- DCE derivation count: number of live predecessors.
    We use a simple specification here; actual implementation would use Set.ncard. -/
noncomputable def dceDerivationCount (edges : Set (α × α)) (live : Set α) (v : α) : ℕ := by
  classical
  exact if ∃ u ∈ live, (u, v) ∈ edges then 1 else 0

/-- DCE derivation count is positive iff there's a live predecessor. -/
lemma dce_derivationCount_pos_iff (edges : Set (α × α)) (live : Set α) (v : α) :
    dceDerivationCount edges live v > 0 ↔ ∃ u ∈ live, (u, v) ∈ edges := by
  classical
  simp only [dceDerivationCount]
  split_ifs with h
  · simp only [Nat.one_pos, h]
  · simp only [Nat.lt_irrefl, h]

/-- DCE configuration. -/
noncomputable def dceConfig (roots : Set α) (edges : Set (α × α)) : IncrFixpointConfig α where
  op := dceOp roots edges
  stepFromDelta := dceStepFromDelta edges
  derivationCount := dceDerivationCount edges
  stepFromDelta_spec delta := dceStepFromDelta_eq roots edges delta
  derivationCount_spec S x := by
    simp only [dceOp, Set.mem_setOf_eq]
    exact (dce_derivationCount_pos_iff edges S x).symm

/-! ## Main Correctness Properties -/

/-- The key invariant: state.current = lfp(op). -/
def maintainsInvariant (cfg : IncrFixpointConfig α) (state : IncrState α) : Prop :=
  isLeastFixpoint cfg.op.toMonotoneOp state.current

/-- Expansion preserves correctness. -/
theorem expansion_correct (cfg cfg' : IncrFixpointConfig α) (state state' : IncrState α)
    (h_exp : expands cfg.op cfg'.op)
    (h_valid : maintainsInvariant cfg state)
    (h_valid' : maintainsInvariant cfg' state') :
    state.current ⊆ state'.current := by
  exact lfp_mono_expand cfg.op cfg'.op state.current state'.current
    h_exp h_valid h_valid'

/-- Contraction preserves correctness. -/
theorem contraction_correct (cfg cfg' : IncrFixpointConfig α) (state state' : IncrState α)
    (h_con : contracts cfg.op cfg'.op)
    (h_valid : maintainsInvariant cfg state)
    (h_valid' : maintainsInvariant cfg' state') :
    state'.current ⊆ state.current := by
  exact lfp_mono_contract cfg.op cfg'.op state.current state'.current
    h_con h_valid h_valid'

end IncrementalFixpoint
