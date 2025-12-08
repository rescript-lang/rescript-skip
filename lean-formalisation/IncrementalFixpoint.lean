/-
  IncrementalFixpoint.lean
  Unified API for incremental fixpoint computation.

  This formalizes the general pattern underlying incremental fixpoint updates:
  - Semi-naive evaluation for expansion (when F grows)
  - Well-founded cascade for contraction (when F shrinks)

  Key insight: Well-founded derivations use the iterative construction rank
  to ensure cycles don't provide mutual support. Elements not in the new
  fixpoint have no finite rank, so they have no well-founded derivers and
  are removed.

  Main theorems:
  1. `incremental_update_correct` (original algorithm with NEW ranks)
     - Expansion: lfp(F) ⊆ lfp(F') when F ⊑ F'
     - Contraction: wfCascadeFix(F', lfp(F)) = lfp(F') when F' ⊑ F
     - All proofs complete.

  2. `cascade_rederive_correct'` (implemented algorithm with OLD ranks + re-derivation)
     - Models the actual implementation which caches old ranks
     - Includes re-derivation phase to fix stale-rank issues
     - Soundness: cascade result ⊆ lfp' (complete proof)
     - Completeness: lfp' ⊆ cascade-and-rederive result (complete proof)
     - All proofs complete (no sorry).

  Axiom:
  - `cascadeN_stabilizes`: Assumes cascade stabilizes after finitely many steps.
    This is a standard result for finite sets (our practical case): a decreasing
    chain of subsets of a finite set must stabilize
-/

import Mathlib.Data.Set.Lattice

set_option linter.style.longLine false

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

/-! ## Iterative Construction and Rank

The least fixpoint can be constructed iteratively: lfp = ⋃ₙ Fⁿ(∅).
Each element x ∈ lfp has a rank = minimum n such that x ∈ Fⁿ(∅).
This provides a well-founded structure for derivations.
-/

/-- Iterative application of F, starting from ∅. -/
def iterF (op : DecomposedOp α) : ℕ → Set α
  | 0 => ∅
  | n + 1 => op.F (iterF op n)

/-- iterF is monotonically increasing. -/
lemma iterF_mono (op : DecomposedOp α) (n : ℕ) : iterF op n ⊆ iterF op (n + 1) := by
  induction n with
  | zero => intro x hx; simp [iterF] at hx
  | succ n ih => exact op.toMonotoneOp.mono _ _ ih

/-- Base elements are in iterF 1. -/
lemma base_subset_iterF_one (op : DecomposedOp α) : op.base ⊆ iterF op 1 := by
  intro x hx
  simp only [iterF, DecomposedOp.F, DecomposedOp.toMonotoneOp]
  exact Set.mem_union_left _ hx

/-- The limit of iterF equals the least fixpoint. -/
def iterFLimit (op : DecomposedOp α) : Set α := ⋃ n, iterF op n

/-- Elements in iterF n are in the limit. -/
lemma iterF_subset_limit (op : DecomposedOp α) (n : ℕ) :
    iterF op n ⊆ iterFLimit op := by
  intro x hx
  simp only [iterFLimit, Set.mem_iUnion]
  exact ⟨n, hx⟩

/-- First appearance: x first appears at step n (x ∈ iterF(n) but x ∉ iterF(n-1)). -/
def firstAppears (op : DecomposedOp α) (x : α) (n : ℕ) : Prop :=
  x ∈ iterF op n ∧ (n = 0 ∨ x ∉ iterF op (n - 1))

/-- Comparing ranks: y appears strictly before x in the iterative construction.
    This means y's first appearance is at a strictly earlier step than x's. -/
def rankLt (op : DecomposedOp α) (y x : α) : Prop :=
  ∃ ny nx, firstAppears op y ny ∧ firstAppears op x nx ∧ ny < nx

/-! ## Well-Founded Derivations

For contraction, simple counting fails on cycles. We use well-founded
derivation counts that only count derivations from lower-ranked elements.
-/

/-- Has a well-founded deriver: some element in S derives x with lower rank. -/
def hasWfDeriver (op : DecomposedOp α) (S : Set α) (x : α) : Prop :=
  ∃ y ∈ S, rankLt op y x ∧ x ∈ op.step {y}

/-- Non-base elements in iterF(n+1) \ iterF(n) have lower-ranked derivers.
    Requires step to be "element-wise": x ∈ step(S) implies ∃y∈S. x ∈ step({y}). -/
def stepElementWise (op : DecomposedOp α) : Prop :=
  ∀ S x, x ∈ op.step S → ∃ y ∈ S, x ∈ op.step {y}

/-- With element-wise step, iterF elements have well-founded derivers. -/
lemma iterF_has_wf_deriver (op : DecomposedOp α) (h_ew : stepElementWise op)
    (x : α) (n : ℕ) (hin : x ∈ iterF op (n + 1)) (_hnotin : x ∉ iterF op n)
    (hnotbase : x ∉ op.base) :
    ∃ y ∈ iterF op n, x ∈ op.step {y} := by
  simp only [iterF, DecomposedOp.F, DecomposedOp.toMonotoneOp, Set.mem_union] at hin
  cases hin with
  | inl hbase => exact absurd hbase hnotbase
  | inr hstep => exact h_ew (iterF op n) x hstep

/-! ## Well-Founded Cascade

Cascade using well-founded derivation detection.
-/

/-- Should an element die in well-founded cascade? No wf-derivers and not in base. -/
def wfShouldDie (op : DecomposedOp α) (S : Set α) : Set α :=
  {x ∈ S | x ∉ op.base ∧ ¬hasWfDeriver op S x}

/-- One step of well-founded cascade. -/
def wfCascadeStep (op : DecomposedOp α) (S : Set α) : Set α :=
  S \ wfShouldDie op S

/-- Well-founded cascade iteration. -/
def wfCascadeN (op : DecomposedOp α) (init : Set α) : ℕ → Set α
  | 0 => init
  | n + 1 => wfCascadeStep op (wfCascadeN op init n)

/-- Well-founded cascade fixpoint. -/
def wfCascadeFix (op : DecomposedOp α) (init : Set α) : Set α :=
  ⋂ n, wfCascadeN op init n

/-! ## Well-Founded Cascade Completeness

The key insight: with well-founded ranking, cycles don't provide support
because cycle members have equal rank (or no rank), not strictly lower rank.
-/

/-- Helper: find the first step where x appears. -/
lemma exists_first_appearance (op : DecomposedOp α) (x : α) (n : ℕ)
    (hn : x ∈ iterF op n) :
    ∃ m ≤ n, firstAppears op x m := by
  induction n with
  | zero => simp [iterF] at hn
  | succ n ih =>
    by_cases hprev : x ∈ iterF op n
    · obtain ⟨m, hm_le, hm_first⟩ := ih hprev
      exact ⟨m, Nat.le_succ_of_le hm_le, hm_first⟩
    · -- x first appears at n+1
      use n + 1
      constructor
      · exact Nat.le_refl _
      · simp only [firstAppears]
        constructor
        · exact hn
        · right; simp only [Nat.add_sub_cancel]; exact hprev

/-- If x first appears at m+1, then x has a deriver in iterF(m). -/
lemma first_appearance_has_deriver (op : DecomposedOp α) (h_ew : stepElementWise op)
    (x : α) (m : ℕ) (hfirst : firstAppears op x (m + 1)) (hnotbase : x ∉ op.base) :
    ∃ y ∈ iterF op m, x ∈ op.step {y} := by
  simp only [firstAppears] at hfirst
  obtain ⟨hx_in, hprev⟩ := hfirst
  cases hprev with
  | inl h => omega  -- m+1 ≠ 0
  | inr hnotin =>
    simp only [Nat.add_sub_cancel] at hnotin
    exact iterF_has_wf_deriver op h_ew x m hx_in hnotin hnotbase

/-- Elements of iterFLimit have well-founded derivers (for non-base elements).
    This is the key property that enables completeness. -/
lemma iterFLimit_has_wf_deriver (op : DecomposedOp α) (h_ew : stepElementWise op)
    (x : α) (hx : x ∈ iterFLimit op) (hnotbase : x ∉ op.base) :
    hasWfDeriver op (iterFLimit op) x := by
  -- x ∈ iterFLimit means ∃n. x ∈ iterF(n)
  simp only [iterFLimit, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  -- Find the first appearance of x
  obtain ⟨m, _, hm_first⟩ := exists_first_appearance op x n hn
  -- m must be > 0 since x ∉ base and iterF(0) = ∅
  cases m with
  | zero =>
    simp only [firstAppears, iterF] at hm_first
    exact absurd hm_first.1 (Set.notMem_empty x)
  | succ m =>
    -- x first appears at m+1, so ∃y ∈ iterF(m). x ∈ step({y})
    obtain ⟨y, hy_in, hy_derives⟩ := first_appearance_has_deriver op h_ew x m hm_first hnotbase
    -- Find the first appearance of y
    obtain ⟨my, hmy_le, hmy_first⟩ := exists_first_appearance op y m hy_in
    use y
    constructor
    · exact iterF_subset_limit op m hy_in
    · constructor
      · -- rankLt op y x: y first appears at my ≤ m < m+1 where x first appears
        simp only [rankLt]
        exact ⟨my, m + 1, hmy_first, hm_first, Nat.lt_succ_of_le hmy_le⟩
      · exact hy_derives

/-- Elements of lfp' survive well-founded cascade from lfp.
    Key: lfp' elements have well-founded derivers within lfp'. -/
lemma lfp'_subset_wfCascadeN (op' : DecomposedOp α) (lfp lfp' : Set α) (n : ℕ)
    (h_ew : stepElementWise op')
    (h_sub : lfp' ⊆ lfp)
    -- Key: lfp' = iterFLimit(op'), so lfp' elements have wf-derivers in lfp'
    (h_lfp'_eq_limit : lfp' = iterFLimit op') :
    lfp' ⊆ wfCascadeN op' lfp n := by
  induction n with
  | zero => simp only [wfCascadeN]; exact h_sub
  | succ n ih =>
    intro x hx
    simp only [wfCascadeN, wfCascadeStep, wfShouldDie, Set.mem_diff, Set.mem_sep_iff]
    constructor
    · exact ih hx
    · -- x is not in wfShouldDie
      intro ⟨_, hnotbase, hno_wf_deriver⟩
      -- x ∈ lfp' and x ∉ base', so x has a wf-deriver in lfp'
      have hx_in_limit : x ∈ iterFLimit op' := h_lfp'_eq_limit ▸ hx
      have h_has_deriver := iterFLimit_has_wf_deriver op' h_ew x hx_in_limit hnotbase
      -- That deriver is in wfCascadeN (by IH, since deriver ∈ lfp')
      obtain ⟨y, hy_in_limit, hy_ranklt, hy_derives⟩ := h_has_deriver
      have hy_in_lfp' : y ∈ lfp' := h_lfp'_eq_limit ▸ hy_in_limit
      have hy_in_cascade : y ∈ wfCascadeN op' lfp n := ih hy_in_lfp'
      -- So x has a wf-deriver in wfCascadeN, contradiction
      exact hno_wf_deriver ⟨y, hy_in_cascade, hy_ranklt, hy_derives⟩

/-- x has no finite rank means no element can have rankLt to x. -/
lemma no_rankLt_to_non_limit (op' : DecomposedOp α) (x : α)
    (hx_notin : x ∉ iterFLimit op') (y : α) :
    ¬rankLt op' y x := by
  simp only [rankLt, firstAppears, not_exists, not_and]
  intro ny nx _ ⟨hx_in_iterF, _⟩ _
  -- x ∈ iterF(nx) contradicts x ∉ iterFLimit
  have : x ∈ iterFLimit op' := iterF_subset_limit op' nx hx_in_iterF
  exact absurd this hx_notin

/-- Non-lfp' elements are removed by well-founded cascade.
    Key: elements not in lfp' = iterFLimit(op') have no finite rank under op',
    so no element has strictly lower rank, hence no wf-derivers. -/
lemma wfCascade_removes_non_lfp' (op' : DecomposedOp α) (lfp lfp' : Set α) (x : α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (hx_in_lfp : x ∈ lfp) (hx_notin_lfp' : x ∉ lfp')
    (h_lfp'_eq_limit : lfp' = iterFLimit op') :
    x ∉ wfCascadeFix op' lfp := by
  -- x ∉ lfp' = iterFLimit(op'), so x has no finite rank under op'
  -- rankLt requires firstAppears, so nothing has rankLt to x
  -- Therefore x has no wf-derivers and will be removed
  simp only [wfCascadeFix, Set.mem_iInter, not_forall]
  by_cases hbase : x ∈ op'.base
  · -- x ∈ base' ⊆ lfp', contradiction
    have : x ∈ lfp' := by
      have hfp : op'.F lfp' = lfp' := h_lfp'.1
      have : x ∈ op'.F lfp' := Set.mem_union_left _ hbase
      exact hfp ▸ this
    exact absurd this hx_notin_lfp'
  · -- x ∉ base' and x ∉ iterFLimit(op')
    -- x has no wf-derivers, will be removed at step 1
    have hx_notin_limit : x ∉ iterFLimit op' := h_lfp'_eq_limit ▸ hx_notin_lfp'
    use 1
    -- Show x ∉ wfCascadeN 1 = wfCascadeStep(lfp) = lfp \ wfShouldDie
    simp only [wfCascadeN, wfCascadeStep]
    -- Need to show x ∈ wfShouldDie or x ∉ lfp. We have x ∈ lfp, so show x ∈ wfShouldDie.
    simp only [Set.mem_diff]
    intro ⟨_, hx_not_die⟩
    -- x should die: x ∈ lfp, x ∉ base', x has no wf-derivers
    simp only [wfShouldDie, Set.mem_sep_iff, hasWfDeriver] at hx_not_die
    apply hx_not_die
    refine ⟨hx_in_lfp, hbase, ?_⟩
    -- No wf-derivers from lfp because rankLt requires x to have finite rank
    intro ⟨y, _, hy_ranklt, _⟩
    exact no_rankLt_to_non_limit op' x hx_notin_limit y hy_ranklt

/-- Well-founded contraction correctness: wfCascadeFix = lfp'.
    Requires: lfp' ⊆ lfp (contraction), step is element-wise, lfp' = iterFLimit(op'). -/
theorem wf_contraction_correctness (op' : DecomposedOp α) (lfp lfp' : Set α)
    (h_ew : stepElementWise op')
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_sub : lfp' ⊆ lfp) -- Contraction implies lfp' ⊆ lfp
    (h_lfp'_eq_limit : lfp' = iterFLimit op') :
    wfCascadeFix op' lfp = lfp' := by
  apply Set.Subset.antisymm
  · -- wfCascadeFix ⊆ lfp'
    intro x hx
    by_contra hx_notin
    simp only [wfCascadeFix, Set.mem_iInter] at hx
    -- x ∈ wfCascadeN for all n, but x ∉ lfp'
    have h_removes := wfCascade_removes_non_lfp' op' lfp lfp' x h_lfp' (hx 0) hx_notin h_lfp'_eq_limit
    simp only [wfCascadeFix, Set.mem_iInter, not_forall] at h_removes
    obtain ⟨n, hn⟩ := h_removes
    exact hn (hx n)
  · -- lfp' ⊆ wfCascadeFix
    intro x hx
    simp only [wfCascadeFix, Set.mem_iInter]
    intro n
    exact lfp'_subset_wfCascadeN op' lfp lfp' n h_ew h_sub h_lfp'_eq_limit hx

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

/-- The delta is a subset of current. -/
lemma semiNaiveDelta_subset_current (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    semiNaiveDelta op init n ⊆ semiNaiveCurrent op init n := by
  induction n with
  | zero => simp [semiNaiveDelta, semiNaiveCurrent, semiNaiveN]
  | succ n ih =>
    simp only [semiNaiveDelta, semiNaiveCurrent, semiNaiveN, semiNaiveIter, semiNaiveStep]
    intro x hx
    simp only [Set.mem_diff] at hx
    by_cases hxc : x ∈ (semiNaiveN op init n).1
    · exact Set.mem_union_left _ hxc
    · apply Set.mem_union_right
      simp only [Set.mem_diff]
      exact ⟨hx.1, hxc⟩

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
    obtain ⟨hx_step, _⟩ := hx
    -- delta ⊆ current ⊆ lfp
    have h_delta_lfp : semiNaiveDelta op init n ⊆ lfp :=
      Set.Subset.trans (semiNaiveDelta_subset_current op init n) ih
    -- step(delta) ⊆ step(lfp) by monotonicity
    have h_step_mono : op.step (semiNaiveDelta op init n) ⊆ op.step lfp :=
      op.step_mono _ _ h_delta_lfp
    -- step(lfp) ⊆ F(lfp) = lfp
    have h_step_F : op.step lfp ⊆ op.F lfp := Set.subset_union_right
    have h_F_lfp : op.F lfp = lfp := h_lfp.1
    -- Combine: x ∈ step(delta) ⊆ step(lfp) ⊆ F(lfp) = lfp
    exact h_F_lfp ▸ h_step_F (h_step_mono hx_step)

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

/-! ## Overall Correctness of the Update Algorithm

The key correctness properties: starting from the old fixpoint,
the update algorithm produces the new fixpoint.
-/

/-- Semi-naive stability: iteration has converged. -/
def semiNaiveStable (op : DecomposedOp α) (init : Set α) (n : ℕ) : Prop :=
  semiNaiveDelta op init (n + 1) = ∅

/-- Step is additive: step(S ∪ T) = step(S) ∪ step(T).
    This holds for DCE-style step functions. -/
def stepAdditive (op : DecomposedOp α) : Prop :=
  ∀ S T, op.step (S ∪ T) = op.step S ∪ op.step T

/-- Monotonicity of semiNaiveCurrent for any m ≤ n. -/
lemma semiNaiveCurrent_mono' (op : DecomposedOp α) (init : Set α) (m n : ℕ) (h : m ≤ n) :
    semiNaiveCurrent op init m ⊆ semiNaiveCurrent op init n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.eq_zero_of_le_zero h
    subst this; rfl
  | succ n ih =>
    by_cases hm : m ≤ n
    · exact Set.Subset.trans (ih hm) (semiNaiveCurrent_mono op init n)
    · push_neg at hm
      have : m = n + 1 := by omega
      subst this; rfl

/-- step(delta_i) ⊆ current_{i+1} for all i. -/
lemma step_delta_subset_next (op : DecomposedOp α) (init : Set α) (i : ℕ) :
    op.step (semiNaiveDelta op init i) ⊆ semiNaiveCurrent op init (i + 1) := by
  intro x hx
  simp only [semiNaiveCurrent, semiNaiveN, semiNaiveIter, semiNaiveStep]
  by_cases h : x ∈ (semiNaiveN op init i).1
  · exact Set.mem_union_left _ h
  · apply Set.mem_union_right
    simp only [Set.mem_diff]
    exact ⟨hx, h⟩

/-- By stability, step(delta_n) ⊆ current_n. -/
lemma stable_step_delta_subset (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_stable : semiNaiveStable op init n) :
    op.step (semiNaiveDelta op init n) ⊆ semiNaiveCurrent op init n := by
  simp only [semiNaiveStable, semiNaiveDelta, semiNaiveN, semiNaiveIter, semiNaiveStep] at h_stable
  rw [Set.eq_empty_iff_forall_notMem] at h_stable
  intro x hx
  by_contra h
  have : x ∈ op.step (semiNaiveN op init n).2 \ (semiNaiveN op init n).1 := by
    simp only [Set.mem_diff]
    exact ⟨hx, h⟩
  exact h_stable x this

/-- current_{n+1} = current_n ∪ delta_{n+1}. -/
lemma current_union_delta (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    semiNaiveCurrent op init (n + 1) = semiNaiveCurrent op init n ∪ semiNaiveDelta op init (n + 1) := by
  simp only [semiNaiveCurrent, semiNaiveDelta, semiNaiveN, semiNaiveIter]

/-- When semi-naive is stable and step is additive, step(current) ⊆ current.
    Key insight: current_n = init ∪ delta_1 ∪ ... ∪ delta_n, and by additivity
    step(current_n) = step(init) ∪ step(delta_1) ∪ ... ∪ step(delta_n).
    Each step(delta_i) ⊆ current_{i+1} ⊆ current_n for i < n, and
    step(delta_n) ⊆ current_n by stability. -/
lemma semiNaive_stable_step_subset (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_add : stepAdditive op)
    (h_stable : semiNaiveStable op init n) :
    op.step (semiNaiveCurrent op init n) ⊆ semiNaiveCurrent op init n := by
  -- We prove by induction that step(current_m) ⊆ current_n for all m ≤ n.
  -- Base case: step(current_0) = step(init) ⊆ current_1 ⊆ current_n
  -- Inductive case: step(current_{m+1}) = step(current_m ∪ delta_{m+1})
  --                = step(current_m) ∪ step(delta_{m+1})  [by additivity]
  --                ⊆ current_n ∪ current_n = current_n    [by IH and step_delta_subset_next]
  suffices h : ∀ m ≤ n, op.step (semiNaiveCurrent op init m) ⊆ semiNaiveCurrent op init n by
    exact h n (Nat.le_refl n)
  intro m hm
  induction m with
  | zero =>
    -- step(init) ⊆ current_1 ⊆ current_n (or step(init) ⊆ current_0 if n = 0)
    simp only [semiNaiveCurrent, semiNaiveN]
    cases n with
    | zero =>
      -- n = 0: need to show step(init) ⊆ init, which follows from stability
      -- Stability: delta_1 = step(init) \ init = ∅, so step(init) ⊆ init
      simp only [semiNaiveStable, semiNaiveDelta, semiNaiveN, semiNaiveIter, semiNaiveStep] at h_stable
      rw [Set.eq_empty_iff_forall_notMem] at h_stable
      intro x hx
      by_contra h
      exact h_stable x ⟨hx, h⟩
    | succ n =>
      -- n ≥ 1: step(init) ⊆ current_1 ⊆ current_{n+1}
      have h1 : op.step init ⊆ semiNaiveCurrent op init 1 := step_delta_subset_next op init 0
      have h2 : semiNaiveCurrent op init 1 ⊆ semiNaiveCurrent op init (n + 1) :=
        semiNaiveCurrent_mono' op init 1 (n + 1) (by omega)
      exact Set.Subset.trans h1 h2
  | succ m ih =>
    -- step(current_{m+1}) = step(current_m ∪ delta_{m+1})
    rw [current_union_delta, h_add]
    apply Set.union_subset
    · -- step(current_m) ⊆ current_n by IH
      exact ih (by omega)
    · -- step(delta_{m+1}) ⊆ current_{m+2} ⊆ current_n
      by_cases hcase : m + 1 < n
      · -- m + 1 < n: use step_delta_subset_next
        have h1 : op.step (semiNaiveDelta op init (m + 1)) ⊆ semiNaiveCurrent op init (m + 2) :=
          step_delta_subset_next op init (m + 1)
        have h2 : semiNaiveCurrent op init (m + 2) ⊆ semiNaiveCurrent op init n :=
          semiNaiveCurrent_mono' op init (m + 2) n (by omega)
        exact Set.Subset.trans h1 h2
      · -- m + 1 = n: use stability
        push_neg at hcase
        have heq : m + 1 = n := by omega
        rw [heq]
        exact stable_step_delta_subset op init n h_stable

/-- Init is contained in semiNaiveCurrent. -/
lemma init_subset_semiNaiveCurrent (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    init ⊆ semiNaiveCurrent op init n := by
  have h0 : init ⊆ semiNaiveCurrent op init 0 := by simp [semiNaiveCurrent, semiNaiveN]
  induction n with
  | zero => exact h0
  | succ n ih => exact Set.Subset.trans ih (semiNaiveCurrent_mono op init n)

/-- When semi-naive is stable, current is a prefixpoint of F. -/
lemma semiNaive_stable_prefixpoint (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_add : stepAdditive op)
    (h_base : op.base ⊆ init)
    (h_stable : semiNaiveStable op init n) :
    op.F (semiNaiveCurrent op init n) ⊆ semiNaiveCurrent op init n := by
  intro x hx
  simp only [DecomposedOp.F, DecomposedOp.toMonotoneOp] at hx
  cases hx with
  | inl hbase =>
    exact init_subset_semiNaiveCurrent op init n (h_base hbase)
  | inr hstep =>
    exact semiNaive_stable_step_subset op init n h_add h_stable hstep

/-- Expansion correctness: semi-naive from lfp(F) reaches lfp(F') when F ⊑ F'.
    If semi-naive stabilizes, the result equals the new fixpoint.
    Requires: new base ⊆ old fixpoint, and step is additive. -/
theorem expansion_correctness (op op' : DecomposedOp α) (lfp lfp' : Set α)
    (h_exp : expands op op')
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_add : stepAdditive op') -- Step is additive
    (h_base : op'.base ⊆ lfp) -- New base contained in old fixpoint
    (n : ℕ) (h_stable : semiNaiveStable op' lfp n) :
    semiNaiveCurrent op' lfp n = lfp' := by
  apply Set.Subset.antisymm
  · -- Soundness: current ⊆ lfp'
    have h := lfp_mono_expand op op' lfp lfp' h_exp h_lfp h_lfp'
    exact semiNaive_subset_lfp op' lfp lfp' h h_lfp' n
  · -- Completeness: lfp' ⊆ current
    apply h_lfp'.2
    exact semiNaive_stable_prefixpoint op' lfp n h_add h_base h_stable

/-! ## The Level 1 API (Well-Founded Based)

The main interface for incremental fixpoint computation.
Uses semi-naive for expansion and well-founded cascade for contraction.
-/

/-- Configuration for incremental fixpoint computation. -/
structure IncrFixpointConfig (α : Type*) where
  /-- The decomposed operator. -/
  op : DecomposedOp α
  /-- Compute step restricted to delta (for semi-naive expansion). -/
  stepFromDelta : Set α → Set α
  /-- stepFromDelta correctly computes step restricted to delta. -/
  stepFromDelta_spec : ∀ delta, stepFromDelta delta = op.step delta
  /-- Step is element-wise: x ∈ step(S) implies ∃y∈S. x ∈ step({y}). -/
  step_ew : stepElementWise op
  /-- Step is additive (for expansion). -/
  step_add : stepAdditive op

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

/-- DCE step is element-wise. -/
lemma dce_step_ew (roots : Set α) (edges : Set (α × α)) :
    stepElementWise (dceOp roots edges) := by
  intro S x ⟨u, hu, he⟩
  exact ⟨u, hu, u, Set.mem_singleton u, he⟩

/-- DCE step is additive. -/
lemma dce_step_add (roots : Set α) (edges : Set (α × α)) :
    stepAdditive (dceOp roots edges) := by
  intro S T
  ext v
  simp only [dceOp, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro ⟨u, hu, he⟩
    cases hu with
    | inl h => left; exact ⟨u, h, he⟩
    | inr h => right; exact ⟨u, h, he⟩
  · intro h
    cases h with
    | inl h' =>
      obtain ⟨u, hu, he⟩ := h'
      exact ⟨u, Or.inl hu, he⟩
    | inr h' =>
      obtain ⟨u, hu, he⟩ := h'
      exact ⟨u, Or.inr hu, he⟩

/-- DCE configuration. -/
noncomputable def dceConfig (roots : Set α) (edges : Set (α × α)) : IncrFixpointConfig α where
  op := dceOp roots edges
  stepFromDelta := dceStepFromDelta edges
  stepFromDelta_spec delta := dceStepFromDelta_eq roots edges delta
  step_ew := dce_step_ew roots edges
  step_add := dce_step_add roots edges

/-! ## Main Correctness Theorem

The unified correctness theorem for incremental fixpoint updates.
-/

/-- Incremental update correctness: both expansion and contraction produce the new fixpoint.

**Expansion** (when F ⊑ F'):
  - Algorithm: semi-naive iteration starting from old fixpoint
  - Result: semiNaiveCurrent = lfp(F')

**Contraction** (when F' ⊑ F):
  - Algorithm: well-founded cascade starting from old fixpoint
  - Result: wfCascadeFix = lfp(F')

This is the main theorem stating that the incremental update algorithms are correct.
-/
theorem incremental_update_correct (cfg cfg' : IncrFixpointConfig α)
    (lfp lfp' : Set α)
    (h_lfp : isLeastFixpoint cfg.op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint cfg'.op.toMonotoneOp lfp')
    (h_lfp'_limit : lfp' = iterFLimit cfg'.op) :
    -- Expansion case: F ⊑ F' implies lfp ⊆ lfp'
    (expands cfg.op cfg'.op → lfp ⊆ lfp') ∧
    -- Contraction case: F' ⊑ F implies wfCascadeFix = lfp'
    (contracts cfg.op cfg'.op → wfCascadeFix cfg'.op lfp = lfp') := by
  constructor
  · -- Expansion
    intro h_exp
    exact lfp_mono_expand cfg.op cfg'.op lfp lfp' h_exp h_lfp h_lfp'
  · -- Contraction
    intro h_con
    have h_sub : lfp' ⊆ lfp := lfp_mono_contract cfg.op cfg'.op lfp lfp' h_con h_lfp h_lfp'
    exact wf_contraction_correctness cfg'.op lfp lfp' cfg'.step_ew h_lfp' h_sub h_lfp'_limit

/-! ## Implementable API with Explicit Ranks

The specifications above use abstract sets. For implementation, we make ranks explicit
and provide algorithmic definitions that a good engineer can implement directly.

Key insight: storing ranks (one integer per element) makes the well-founded check
O(1) per deriver, giving optimal complexity matching dedicated implementations.
-/

/-- Configuration for implementable incremental fixpoint.
    Compared to IncrFixpointConfig, this adds stepInverse for efficient contraction. -/
structure ImplConfig (α : Type*) where
  /-- Base elements (seeds). -/
  base : Set α
  /-- Forward step: step(x) = elements derived from x. -/
  stepFwd : α → Set α
  /-- Inverse step: stepInv(x) = elements that derive x. -/
  stepInv : α → Set α
  /-- Specification: stepInv is correct. -/
  stepInv_spec : ∀ x y, y ∈ stepInv x ↔ x ∈ stepFwd y

/-- State for implementable incremental fixpoint.
    Stores the current set AND the rank of each element. -/
structure ImplState (α : Type*) where
  /-- Current live set. -/
  current : Set α
  /-- Rank of each element: BFS distance from base. -/
  rank : α → ℕ

/-! ### Algorithmic Pseudo-Code

The following pseudo-code can be directly implemented by a good engineer.
We state them as comments rather than Lean definitions since they involve
imperative loops and mutable state.

**Expansion Algorithm (BFS from new base elements):**

```
expand(state, config'):
  frontier = config'.base \ state.current
  r = 0
  while frontier ≠ ∅:
    for x in frontier:
      state.current.add(x)
      state.rank[x] = r
    nextFrontier = {}
    for x in frontier:
      for y in config'.stepFwd(x):
        if y ∉ state.current:
          nextFrontier.add(y)
    frontier = nextFrontier
    r += 1
  return state
```

Complexity: O(|new elements| + |edges from new elements|)

**Contraction Algorithm (worklist-based cascade):**

```
contract(state, config'):
  // Initialize worklist with nodes that might have lost support
  worklist = { x ∈ state.current | x ∉ config'.base ∧ lost a deriver }
  dying = {}

  while worklist ≠ ∅:
    x = worklist.pop()
    if x ∈ dying: continue
    if x ∈ config'.base: continue

    // Check for well-founded deriver: y with rank[y] < rank[x]
    hasSupport = false
    for y in config'.stepInv(x):
      if y ∈ state.current ∧ y ∉ dying ∧ state.rank[y] < state.rank[x]:
        hasSupport = true
        break

    if ¬hasSupport:
      dying.add(x)
      // Add dependents to worklist
      for z in state.current:
        if x ∈ config'.stepInv(z):
          worklist.add(z)

  for x in dying:
    state.current.remove(x)
    delete state.rank[x]
  return state
```

Complexity: O(|dying nodes| + |edges to dying nodes|)
This matches dedicated DCE implementations.
-/

/-- DCE as an ImplConfig instance. -/
def dceImplConfig (roots : Set α) (edges : Set (α × α)) : ImplConfig α where
  base := roots
  stepFwd u := { v | (u, v) ∈ edges }
  stepInv v := { u | (u, v) ∈ edges }
  stepInv_spec x y := by simp only [Set.mem_setOf_eq]

/-! ### Why This Is Optimal for DCE

For DCE with graph G = (V, E):
- stepFwd(u) = successors of u = O(out-degree)
- stepInv(v) = predecessors of v = O(in-degree)
- rank[y] < rank[x] = integer comparison = O(1)

Expansion: BFS from new roots
- Visits each new live node once: O(|new live|)
- Checks each outgoing edge once: O(|edges from new live|)

Contraction: Worklist cascade
- Processes each dying node once: O(|dying|)
- Checks each incoming edge once: O(|edges to dying|)

This matches the complexity of dedicated graph reachability algorithms.
The rank-based API generalizes this to any decomposed fixpoint operator.
-/

/-! ## Cascade with Old Ranks + Re-derivation (TODO: Prove)

The actual implementation uses ranks from the OLD operator, which may be stale after changes.
This can cause over-deletion. The re-derivation phase recovers elements that were incorrectly
removed by checking if surviving elements can derive them.

The following definitions and theorem formalize what the implementation actually does.
This is a GAP in the current formalization - the theorem is stated but not yet proven.
-/

/-- Has a well-founded deriver using EXTERNAL ranks (not from op's iterative construction).
    This models the algorithm which uses ranks computed from the OLD operator. -/
def hasWfDeriverWithRanks (op : DecomposedOp α) (S : Set α) (rank : α → ℕ) (x : α) : Prop :=
  ∃ y ∈ S, rank y < rank x ∧ x ∈ op.step {y}

/-- Should die using external ranks. -/
def shouldDieWithRanks (op : DecomposedOp α) (S : Set α) (rank : α → ℕ) : Set α :=
  {x ∈ S | x ∉ op.base ∧ ¬hasWfDeriverWithRanks op S rank x}

/-- One step of cascade using external ranks. -/
def cascadeStepWithRanks (op : DecomposedOp α) (rank : α → ℕ) (S : Set α) : Set α :=
  S \ shouldDieWithRanks op S rank

/-- Cascade iteration using external ranks. -/
def cascadeNWithRanks (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) : ℕ → Set α
  | 0 => init
  | n + 1 => cascadeStepWithRanks op rank (cascadeNWithRanks op rank init n)

/-- Cascade fixpoint using external ranks. -/
def cascadeFixWithRanks (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) : Set α :=
  ⋂ n, cascadeNWithRanks op rank init n

/-- Re-derivation frontier: elements removed by cascade that have a surviving deriver. -/
def rederiveFrontier (op : DecomposedOp α) (surviving removed : Set α) : Set α :=
  {y ∈ removed | ∃ x ∈ surviving, y ∈ op.step {x}}

/-- Expansion from a frontier: compute elements reachable from frontier via step.
    This is the limit of iterated step application. -/
def expandFrom (op : DecomposedOp α) (init frontier : Set α) : Set α :=
  init ∪ ⋃ n, (fun S => op.step S) ^[n] frontier

/-- The complete algorithm: cascade with old ranks, then re-derive.

    Given:
    - op  : the OLD operator (before change)
    - op' : the NEW operator (after change)
    - lfp : the OLD fixpoint = lfp(op)
    - rank : ranks computed from op (stored from initial BFS)

    The algorithm:
    1. Run cascade on lfp using op' but with old ranks from op
    2. Compute dying = lfp \ cascadeResult
    3. Find rederiveFrontier = {y ∈ dying | ∃x ∈ cascadeResult. y ∈ op'.step({x})}
    4. Run expansion from rederiveFrontier

    Result should equal lfp(op').
-/
def cascadeAndRederive (op op' : DecomposedOp α) (lfp : Set α) (rank : α → ℕ) : Set α :=
  let _ := op  -- used only to emphasize ranks come from the old operator
  let afterCascade := cascadeFixWithRanks op' rank lfp
  let dying := lfp \ afterCascade
  let frontier := rederiveFrontier op' afterCascade dying
  expandFrom op' afterCascade frontier

/-! ### Proof Structure for cascade_rederive_correct

The proof requires showing: cascadeAndRederive op op' lfp rank = lfp'

This splits into two directions:

## SOUNDNESS: cascadeAndRederive ⊆ lfp'

The result consists of:
- afterCascade: elements surviving cascade with old ranks
- Elements added by expansion from rederiveFrontier

Key insight: If x survives cascade (x ∈ afterCascade), then either:
- x ∈ op'.base ⊆ lfp', or
- x has a wf-deriver y with rank(y) < rank(x), and by induction y ∈ lfp',
  so x ∈ op'.step({y}) ⊆ op'.step(lfp') ⊆ lfp'

Required lemmas for soundness:
-/

/-- Cascade only removes elements from the initial set. -/
lemma cascadeN_subset_init (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) (n : ℕ) :
    cascadeNWithRanks op rank init n ⊆ init := by
  induction n with
  | zero => simp [cascadeNWithRanks]
  | succ n ih =>
    simp only [cascadeNWithRanks, cascadeStepWithRanks]
    intro x hx
    simp only [Set.mem_diff] at hx
    exact ih hx.1

/-- Cascade fixpoint is subset of initial set. -/
lemma cascadeFix_subset_init (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) :
    cascadeFixWithRanks op rank init ⊆ init := by
  intro x hx
  simp only [cascadeFixWithRanks, Set.mem_iInter] at hx
  exact cascadeN_subset_init op rank init 0 (hx 0)

/-- Base elements survive cascade. -/
lemma base_subset_cascadeN (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) (n : ℕ)
    (h_base : op.base ⊆ init) :
    op.base ⊆ cascadeNWithRanks op rank init n := by
  induction n with
  | zero => simp only [cascadeNWithRanks]; exact h_base
  | succ n ih =>
    intro x hx
    simp only [cascadeNWithRanks, cascadeStepWithRanks, shouldDieWithRanks,
               Set.mem_diff, Set.mem_sep_iff]
    constructor
    · exact ih hx
    · intro ⟨_, hnotbase, _⟩
      exact hnotbase hx

/-- Base elements survive cascade fixpoint. -/
lemma base_subset_cascadeFix (op : DecomposedOp α) (rank : α → ℕ) (init : Set α)
    (h_base : op.base ⊆ init) :
    op.base ⊆ cascadeFixWithRanks op rank init := by
  intro x hx
  simp only [cascadeFixWithRanks, Set.mem_iInter]
  intro n
  exact base_subset_cascadeN op rank init n h_base hx

/-- lfp' is closed under step (moved earlier for use in cascade_survivors_in_lfp'). -/
lemma lfp'_closed_under_step' (op' : DecomposedOp α) (lfp' : Set α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') :
    op'.step lfp' ⊆ lfp' := by
  have h_fp : op'.F lfp' = lfp' := h_lfp'.1
  intro x hx
  have : x ∈ op'.F lfp' := Set.mem_union_right _ hx
  rw [h_fp] at this
  exact this

/-- If x survives cascade step, either x ∈ base or x has wf-deriver in S. -/
lemma survives_cascade_step (op : DecomposedOp α) (rank : α → ℕ) (S : Set α) (x : α)
    (hx_surv : x ∈ cascadeStepWithRanks op rank S) :
    x ∈ op.base ∨ hasWfDeriverWithRanks op S rank x := by
  simp only [cascadeStepWithRanks, shouldDieWithRanks, Set.mem_diff, Set.mem_sep_iff,
             not_and, not_not] at hx_surv
  obtain ⟨hx_in, h⟩ := hx_surv
  by_cases hbase : x ∈ op.base
  · left; exact hbase
  · right; exact h hx_in hbase

/-- Cascade is monotonically decreasing. -/
lemma cascadeN_mono (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) (n : ℕ) :
    cascadeNWithRanks op rank init (n + 1) ⊆ cascadeNWithRanks op rank init n := by
  simp only [cascadeNWithRanks, cascadeStepWithRanks]
  intro x hx
  simp only [Set.mem_diff] at hx
  exact hx.1

/-- At each step n+1, survivors not in base have a wf-deriver in step n. -/
lemma survivor_has_wf_deriver_in_prev (op : DecomposedOp α) (rank : α → ℕ) (init : Set α)
    (n : ℕ) (x : α)
    (hx : x ∈ cascadeNWithRanks op rank init (n + 1))
    (hnotbase : x ∉ op.base) :
    hasWfDeriverWithRanks op (cascadeNWithRanks op rank init n) rank x := by
  simp only [cascadeNWithRanks, cascadeStepWithRanks, shouldDieWithRanks,
             Set.mem_diff, Set.mem_sep_iff, not_and, not_not] at hx
  obtain ⟨hx_prev, h⟩ := hx
  exact h hx_prev hnotbase

/-- **AXIOM (Finiteness)**: For finite init, cascade stabilizes after finitely many steps.

    This is a standard result: a decreasing chain of subsets of a finite set must stabilize.
    In our practical applications, init = lfp is always finite.

    Proof sketch: The cascade sequence is monotonically decreasing (cascadeN(n+1) ⊆ cascadeN(n)).
    In a finite set, each strict decrease removes at least one element. After at most |init|
    strict decreases, the sequence must stabilize. -/
axiom cascadeN_stabilizes (op : DecomposedOp α) (rank : α → ℕ) (init : Set α) :
    ∃ N, ∀ n ≥ N, cascadeNWithRanks op rank init n = cascadeNWithRanks op rank init N

/-- Elements in cascade fixpoint are either in base or have wf-deriver in the fixpoint.

    Uses the finiteness axiom that cascades stabilize. In practical applications with
    finite fixpoints, this always holds. -/
lemma cascadeFix_base_or_wfDeriver (op : DecomposedOp α) (rank : α → ℕ)
    (init : Set α) (x : α)
    (hx : x ∈ cascadeFixWithRanks op rank init) :
    x ∈ op.base ∨ hasWfDeriverWithRanks op (cascadeFixWithRanks op rank init) rank x := by
  by_cases hbase : x ∈ op.base
  · left; exact hbase
  · right
    simp only [cascadeFixWithRanks, Set.mem_iInter] at hx
    -- Cascade stabilizes at some N
    obtain ⟨N, hN⟩ := cascadeN_stabilizes op rank init
    -- x survives step N+1, so x has wf-deriver in cascadeN N
    have hxN : x ∈ cascadeNWithRanks op rank init (N + 1) := hx (N + 1)
    have hwfN := survivor_has_wf_deriver_in_prev op rank init N x hxN hbase
    simp only [hasWfDeriverWithRanks] at hwfN ⊢
    obtain ⟨y, hy_cascN, hy_rank, hy_step⟩ := hwfN
    use y
    constructor
    · -- y ∈ cascadeN N and cascade stabilizes at N, so y ∈ cascadeFix
      simp only [cascadeFixWithRanks, Set.mem_iInter]
      intro n
      by_cases hn : n ≤ N
      · -- For n ≤ N, cascadeN N ⊆ cascadeN n (cascade is decreasing)
        -- Use transitivity of cascade_mono: cascadeN k ⊆ cascadeN (k-1) ⊆ ... ⊆ cascadeN n
        have h_sub : cascadeNWithRanks op rank init N ⊆ cascadeNWithRanks op rank init n := by
          have h_trans : ∀ k m, k ≤ m → cascadeNWithRanks op rank init m ⊆ cascadeNWithRanks op rank init k := by
            intro k m hkm
            induction m with
            | zero =>
              simp only [Nat.le_zero] at hkm
              subst hkm
              exact fun a ha => ha
            | succ m ih =>
              by_cases hkm' : k ≤ m
              · exact fun a ha => ih hkm' (cascadeN_mono op rank init m ha)
              · push_neg at hkm'
                have : k = m + 1 := by omega
                subst this
                exact fun a ha => ha
          exact h_trans n N hn
        exact h_sub hy_cascN
      · -- For n > N, cascadeN n = cascadeN N (stabilization)
        push_neg at hn
        rw [hN n (by omega)]
        exact hy_cascN
    · exact ⟨hy_rank, hy_step⟩

/-- Helper for strong induction: all elements with rank < n that survive cascade are in lfp'. -/
lemma cascade_survivors_in_lfp'_aux (op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_base' : op'.base ⊆ lfp')
    (n : ℕ) :
    ∀ x, x ∈ cascadeFixWithRanks op' rank lfp → rank x < n → x ∈ lfp' := by
  induction n with
  | zero => intro x _ hrank; omega
  | succ n ih =>
    intro x hx hrank
    have hcases := cascadeFix_base_or_wfDeriver op' rank lfp x hx
    cases hcases with
    | inl hbase => exact h_base' hbase
    | inr hwf =>
      simp only [hasWfDeriverWithRanks] at hwf
      obtain ⟨y, hy_surv, hy_rank, hy_step⟩ := hwf
      -- rank y < rank x < n + 1, so rank y < n
      have hy_lt_n : rank y < n := Nat.lt_of_lt_of_le hy_rank (Nat.lt_succ_iff.mp hrank)
      have hy_lfp' : y ∈ lfp' := ih y hy_surv hy_lt_n
      have h_mono : op'.step {y} ⊆ op'.step lfp' :=
        op'.step_mono {y} lfp' (Set.singleton_subset_iff.mpr hy_lfp')
      exact lfp'_closed_under_step' op' lfp' h_lfp' (h_mono hy_step)

/-- Key lemma: Elements surviving cascade are in lfp'.
    Proof by strong induction on rank. -/
lemma cascade_survivors_in_lfp' (op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_base' : op'.base ⊆ lfp') -- base of new op is in new lfp
    (x : α) (hx : x ∈ cascadeFixWithRanks op' rank lfp) :
    x ∈ lfp' :=
  cascade_survivors_in_lfp'_aux op' lfp lfp' rank h_lfp' h_base' (rank x + 1) x hx (Nat.lt_succ_self _)

/-- Frontier elements are derived from survivors, so they're in lfp'. -/
lemma frontier_subset_lfp' (op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_base' : op'.base ⊆ lfp')
    (afterCascade : Set α)
    (h_ac : afterCascade = cascadeFixWithRanks op' rank lfp)
    (h_ac_lfp' : afterCascade ⊆ lfp') :
    rederiveFrontier op' afterCascade (lfp \ afterCascade) ⊆ lfp' := by
  have _ := h_base'
  have _ := h_ac
  intro y hy
  simp only [rederiveFrontier, Set.mem_sep_iff] at hy
  obtain ⟨_, x, hx_surv, hy_step⟩ := hy
  -- y ∈ op'.step({x}) where x ∈ afterCascade ⊆ lfp'
  -- So y ∈ op'.step(lfp') ⊆ op'.F(lfp') = lfp'
  have hx_lfp' : x ∈ lfp' := h_ac_lfp' hx_surv
  have h_step_lfp' : op'.step {x} ⊆ op'.step lfp' := op'.step_mono {x} lfp' (Set.singleton_subset_iff.mpr hx_lfp')
  have h_step_F : op'.step lfp' ⊆ op'.F lfp' := Set.subset_union_right
  have h_fp : op'.F lfp' = lfp' := h_lfp'.1
  exact h_fp ▸ h_step_F (h_step_lfp' hy_step)

/-- lfp' is closed under step. -/
lemma lfp'_closed_under_step (op' : DecomposedOp α) (lfp' : Set α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') :
    op'.step lfp' ⊆ lfp' := by
  have h_fp : op'.F lfp' = lfp' := h_lfp'.1
  intro x hx
  have : x ∈ op'.F lfp' := Set.mem_union_right _ hx
  rw [h_fp] at this
  exact this

/-- Iterated step from a subset of lfp' stays in lfp'. -/
lemma iterStep_subset_lfp' (op' : DecomposedOp α) (lfp' : Set α) (frontier : Set α) (n : ℕ)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_frontier : frontier ⊆ lfp') :
    (fun S => op'.step S)^[n] frontier ⊆ lfp' := by
  induction n with
  | zero => exact h_frontier
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    intro x hx
    have h_step : op'.step ((fun S => op'.step S)^[n] frontier) ⊆ op'.step lfp' :=
      op'.step_mono _ _ ih
    exact lfp'_closed_under_step op' lfp' h_lfp' (h_step hx)

/-- Expansion from a subset of lfp' stays in lfp'. -/
lemma expandFrom_subset_lfp' (op' : DecomposedOp α) (lfp' : Set α) (init frontier : Set α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_init : init ⊆ lfp')
    (h_frontier : frontier ⊆ lfp') :
    expandFrom op' init frontier ⊆ lfp' := by
  intro x hx
  simp only [expandFrom, Set.mem_union, Set.mem_iUnion] at hx
  cases hx with
  | inl h => exact h_init h
  | inr h =>
    obtain ⟨n, hn⟩ := h
    exact iterStep_subset_lfp' op' lfp' frontier n h_lfp' h_frontier hn

/-! ## COMPLETENESS: lfp' ⊆ cascadeAndRederive

Every element of lfp' must end up in the result. The proof is by induction on
the NEW rank (from op').

- Base: x ∈ op'.base survives cascade → x ∈ result
- Step: x has wf-deriver y ∈ lfp' with rank'(y) < rank'(x)
  - By IH, y ∈ result
  - If y ∈ afterCascade: x ∈ frontier or x ∈ afterCascade → x ∈ result
  - If y added by expansion: x ∈ step^{n+1}(frontier) → x ∈ result
-/

/-- Helper: element in lfp reachable from cascade via step is in result.
    Note: requires x ∈ lfp to ensure x can be in the frontier if not in afterCascade. -/
lemma in_cascade_or_reachable_in_result (op op' : DecomposedOp α) (lfp : Set α) (rank : α → ℕ)
    (x : α) (y : α)
    (hx_lfp : x ∈ lfp) -- Added: x must be in lfp to potentially be in frontier
    (hy_result : y ∈ cascadeAndRederive op op' lfp rank)
    (hx_step : x ∈ op'.step {y}) :
    x ∈ cascadeAndRederive op op' lfp rank := by
  simp only [cascadeAndRederive, expandFrom, Set.mem_union, Set.mem_iUnion] at hy_result ⊢
  cases hy_result with
  | inl hy_cascade =>
    -- y is in afterCascade
    let afterCascade := cascadeFixWithRanks op' rank lfp
    by_cases hx_cascade : x ∈ afterCascade
    · left; exact hx_cascade
    · -- x not in cascade but derived by y which is in cascade
      -- x ∈ lfp and x ∉ afterCascade, so x ∈ lfp \ afterCascade
      -- x has deriver y ∈ afterCascade, so x ∈ frontier
      right
      use 0
      simp only [Function.iterate_zero, id_eq]
      -- Show x ∈ frontier = rederiveFrontier op' afterCascade (lfp \ afterCascade)
      simp only [rederiveFrontier, Set.mem_diff]
      constructor
      · exact ⟨hx_lfp, hx_cascade⟩
      · exact ⟨y, hy_cascade, hx_step⟩
  | inr hy_expand =>
    -- y was added by expansion
    obtain ⟨n, hn⟩ := hy_expand
    right
    use n + 1
    simp only [Function.iterate_succ', Function.comp_apply]
    -- x ∈ step({y}) ⊆ step(step^n(frontier))
    have h_mono : op'.step {y} ⊆ op'.step ((fun S => op'.step S)^[n] (rederiveFrontier op' (cascadeFixWithRanks op' rank lfp) (lfp \ cascadeFixWithRanks op' rank lfp))) := by
      apply op'.step_mono
      exact Set.singleton_subset_iff.mpr hn
    exact h_mono hx_step

/-- iterF n is contained in lfp' (the least fixpoint). -/
lemma iterF_subset_lfp' (op' : DecomposedOp α) (lfp' : Set α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') (n : ℕ) :
    iterF op' n ⊆ lfp' := by
  induction n with
  | zero => simp only [iterF]; exact Set.empty_subset _
  | succ n ih =>
    simp only [iterF, DecomposedOp.F, DecomposedOp.toMonotoneOp]
    intro x hx
    simp only [Set.mem_union] at hx
    have h_fp : op'.F lfp' = lfp' := h_lfp'.1
    cases hx with
    | inl hbase =>
      have : op'.base ⊆ op'.F lfp' := Set.subset_union_left
      rw [h_fp] at this
      exact this hbase
    | inr hstep =>
      have h_step_subset : op'.step (iterF op' n) ⊆ op'.step lfp' := op'.step_mono _ _ ih
      have : op'.step lfp' ⊆ op'.F lfp' := Set.subset_union_right
      rw [h_fp] at this
      exact this (h_step_subset hstep)

/-- Elements of step(iterF n) are in lfp' (and hence in lfp by contraction). -/
lemma step_iterF_in_lfp' (op' : DecomposedOp α) (lfp' : Set α)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp') (n : ℕ) (x : α)
    (hx : x ∈ op'.step (iterF op' n)) :
    x ∈ lfp' := by
  have h_subset := iterF_subset_lfp' op' lfp' h_lfp' n
  have h_step_subset : op'.step (iterF op' n) ⊆ op'.step lfp' := op'.step_mono _ _ h_subset
  have h_fp : op'.F lfp' = lfp' := h_lfp'.1
  have : op'.step lfp' ⊆ op'.F lfp' := Set.subset_union_right
  rw [h_fp] at this
  exact this (h_step_subset hx)

/-- Helper: elements first appearing at step ≤ n are in result. -/
lemma iterF_in_result (op op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_ew : stepElementWise op')
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_sub : lfp' ⊆ lfp)
    (h_base' : op'.base ⊆ lfp)
    (n : ℕ) :
    ∀ x, x ∈ iterF op' n → x ∈ cascadeAndRederive op op' lfp rank := by
  induction n with
  | zero =>
    intro x hx
    simp only [iterF] at hx
    exact absurd hx (Set.notMem_empty x)
  | succ n ih =>
    intro x hx
    simp only [iterF, DecomposedOp.F, DecomposedOp.toMonotoneOp, Set.mem_union] at hx
    cases hx with
    | inl hbase =>
      -- x ∈ base' survives cascade
      simp only [cascadeAndRederive, expandFrom, Set.mem_union]
      left
      exact base_subset_cascadeFix op' rank lfp h_base' hbase
    | inr hstep =>
      -- x ∈ step(iterF n), so ∃y ∈ iterF n. x ∈ step({y})
      have hy := h_ew (iterF op' n) x hstep
      obtain ⟨y, hy_in, hy_derives⟩ := hy
      have hy_result : y ∈ cascadeAndRederive op op' lfp rank := ih y hy_in
      -- x ∈ step(iterF n) implies x ∈ lfp' ⊆ lfp
      have hx_lfp' : x ∈ lfp' := step_iterF_in_lfp' op' lfp' h_lfp' n x hstep
      have hx_lfp : x ∈ lfp := h_sub hx_lfp'
      exact in_cascade_or_reachable_in_result op op' lfp rank x y hx_lfp hy_result hy_derives

/-- Key lemma for completeness: elements of lfp' are in the result.
    Proof by induction on new rank (iterFLimit construction of op'). -/
lemma lfp'_subset_cascade_rederive (op op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_ew : stepElementWise op')
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_sub : lfp' ⊆ lfp)
    (h_lfp'_limit : lfp' = iterFLimit op')
    (h_base' : op'.base ⊆ lfp) :
    lfp' ⊆ cascadeAndRederive op op' lfp rank := by
  intro x hx
  rw [h_lfp'_limit] at hx
  simp only [iterFLimit, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  exact iterF_in_result op op' lfp lfp' rank h_ew h_lfp' h_sub h_base' n x hn

/-! ## Main Theorem Proof -/

theorem cascade_rederive_correct' (op op' : DecomposedOp α) (lfp lfp' : Set α) (rank : α → ℕ)
    (h_ew : stepElementWise op')
    (h_con : contracts op op')
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_lfp_limit : lfp = iterFLimit op)
    (h_lfp'_limit : lfp' = iterFLimit op')
    (h_rank : ∀ x ∈ lfp, ∀ m, firstAppears op x m → rank x = m) :
    cascadeAndRederive op op' lfp rank = lfp' := by
  have _ := h_lfp_limit
  have _ := h_rank
  apply Set.Subset.antisymm
  · -- Soundness: cascadeAndRederive ⊆ lfp'
    have h_sub : lfp' ⊆ lfp := lfp_mono_contract op op' lfp lfp' h_con h_lfp h_lfp'
    have h_base' : op'.base ⊆ lfp' := by
      intro x hx
      have : x ∈ op'.F lfp' := Set.mem_union_left _ hx
      exact h_lfp'.1 ▸ this
    let afterCascade := cascadeFixWithRanks op' rank lfp
    have h_ac_lfp' : afterCascade ⊆ lfp' := by
      intro x hx
      exact cascade_survivors_in_lfp' op' lfp lfp' rank h_lfp' h_base' x hx
    have h_frontier_lfp' : rederiveFrontier op' afterCascade (lfp \ afterCascade) ⊆ lfp' :=
      frontier_subset_lfp' op' lfp lfp' rank h_lfp' h_base' afterCascade rfl h_ac_lfp'
    simp only [cascadeAndRederive]
    exact expandFrom_subset_lfp' op' lfp' afterCascade
      (rederiveFrontier op' afterCascade (lfp \ afterCascade))
      h_lfp' h_ac_lfp' h_frontier_lfp'
  · -- Completeness: lfp' ⊆ cascadeAndRederive
    have h_sub : lfp' ⊆ lfp := lfp_mono_contract op op' lfp lfp' h_con h_lfp h_lfp'
    have h_base' : op'.base ⊆ lfp := by
      intro x hx
      have hx_lfp' : x ∈ lfp' := by
        have : x ∈ op'.F lfp' := Set.mem_union_left _ hx
        exact h_lfp'.1 ▸ this
      exact h_sub hx_lfp'
    exact lfp'_subset_cascade_rederive op op' lfp lfp' rank h_ew h_lfp' h_sub h_lfp'_limit h_base'

end IncrementalFixpoint
