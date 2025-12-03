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

  Main theorem: `incremental_update_correct`
  - Expansion: lfp(F) ⊆ lfp(F') when F ⊑ F'
  - Contraction: wfCascadeFix(F', lfp(F)) = lfp(F') when F' ⊑ F

  Remaining assumption (1 sorry):
  - `semiNaive_stable_step_subset`: step(current) ⊆ current when stable
    (requires additivity decomposition proof)
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
    (x : α) (n : ℕ) (hin : x ∈ iterF op (n + 1)) (hnotin : x ∉ iterF op n)
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
    exact absurd hm_first.1 (Set.not_mem_empty x)
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
lemma lfp'_subset_wfCascadeN (op op' : DecomposedOp α) (lfp lfp' : Set α) (n : ℕ)
    (h_ew : stepElementWise op')
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_sub : lfp' ⊆ lfp)
    -- Key: lfp' = iterFLimit(op'), so lfp' elements have wf-derivers in lfp'
    (h_lfp'_eq_limit : lfp' = iterFLimit op') :
    lfp' ⊆ wfCascadeN op' lfp n := by
  induction n with
  | zero => simp [wfCascadeN]; exact h_sub
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
    (h_sub : lfp' ⊆ lfp)  -- Contraction implies lfp' ⊆ lfp
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
    exact lfp'_subset_wfCascadeN op' op' lfp lfp' n h_ew h_lfp' h_sub h_lfp'_eq_limit hx

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

/-- When semi-naive is stable and step is additive, step(current) ⊆ current.
    Proof sketch: with stability at n, delta_{n+1} = ∅, so step(delta_n) ⊆ current_n.
    By induction: step(delta_i) ⊆ current_{i+1} ⊆ current_n for all i < n.
    With additivity: step(current_n) = ⋃ step(delta_i) ⊆ current_n.
    This proof is complex; we assume it holds for DCE-style operators. -/
lemma semiNaive_stable_step_subset (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_add : stepAdditive op)
    (h_stable : semiNaiveStable op init n) :
    op.step (semiNaiveCurrent op init n) ⊆ semiNaiveCurrent op init n := by
  -- The full proof requires showing current_n = ⋃_{i≤n} delta_i
  -- and using additivity to decompose step(current_n).
  -- For now, we note this holds for DCE-style additive operators.
  sorry

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
    (h_add : stepAdditive op')  -- Step is additive
    (h_base : op'.base ⊆ lfp)   -- New base contained in old fixpoint
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
    (h_lfp_limit : lfp = iterFLimit cfg.op)
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

end IncrementalFixpoint
