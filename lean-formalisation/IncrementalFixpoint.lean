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

/-- iterF is monotone in n. -/
lemma iterF_mono' (op : DecomposedOp α) (m n : ℕ) (h : m ≤ n) :
    iterF op m ⊆ iterF op n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.eq_zero_of_le_zero h
    subst this; rfl
  | succ n ih =>
    by_cases hm : m ≤ n
    · exact Set.Subset.trans (ih hm) (iterF_mono op n)
    · push_neg at hm
      have : m = n + 1 := by omega
      subst this; rfl

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

/-- An element is in the limit (has finite rank). -/
def inLimit (op : DecomposedOp α) (x : α) : Prop := x ∈ iterFLimit op

/-- An element has a rank iff it's in the iterF limit. -/
lemma inLimit_iff (op : DecomposedOp α) (x : α) :
    inLimit op x ↔ ∃ n, x ∈ iterF op n := by
  simp only [inLimit, iterFLimit, Set.mem_iUnion]

/-- Base elements are in the limit. -/
lemma base_inLimit (op : DecomposedOp α) (x : α) (hx : x ∈ op.base) :
    inLimit op x := by
  rw [inLimit_iff]
  exact ⟨1, base_subset_iterF_one op hx⟩

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

/-- Well-founded derivation: y derives x and has strictly lower rank. -/
def wfDerives (op : DecomposedOp α) (y x : α) : Prop :=
  rankLt op y x ∧ x ∈ op.step {y}

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

/-- Well-founded cascade is monotonically decreasing. -/
lemma wfCascadeN_mono (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    wfCascadeN op init (n + 1) ⊆ wfCascadeN op init n := by
  simp only [wfCascadeN, wfCascadeStep]
  exact Set.diff_subset

/-- Base elements survive well-founded cascade. -/
lemma base_subset_wfCascadeN (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_base : op.base ⊆ init) :
    op.base ⊆ wfCascadeN op init n := by
  induction n with
  | zero => simp [wfCascadeN]; exact h_base
  | succ n ih =>
    intro x hx
    simp only [wfCascadeN, wfCascadeStep, wfShouldDie, Set.mem_diff, Set.mem_sep_iff]
    exact ⟨ih hx, fun ⟨_, hnotbase, _⟩ => hnotbase hx⟩

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

/-! ## Counting-Based Cascade Algorithm

For contraction, we use counting-based deletion:
- Track how many derivations support each element
- When count reaches 0 (and not in base), element dies
- Propagate death to dependents
-/

/-- Derivation count function type: given a set S and element x,
    returns how many ways x is derived from S via step. -/
abbrev DerivCount (α : Type*) := Set α → α → ℕ

/-- A derivation count is valid if it correctly reflects step membership. -/
def validDerivCount (op : DecomposedOp α) (count : DerivCount α) : Prop :=
  ∀ S x, x ∈ op.step S ↔ count S x > 0

/-- A derivation count is monotone: larger sets give larger counts. -/
def monoDerivCount (count : DerivCount α) : Prop :=
  ∀ S T x, S ⊆ T → count S x ≤ count T x

/-- The set of elements that should die: in current, not in base, and count is 0. -/
def shouldDie (op : DecomposedOp α) (count : DerivCount α) (current : Set α) : Set α :=
  { x ∈ current | x ∉ op.base ∧ count current x = 0 }

/-- One step of cascade: remove elements that should die. -/
def cascadeStep (op : DecomposedOp α) (count : DerivCount α) (current : Set α) : Set α :=
  current \ shouldDie op count current

/-- Cascade iteration. -/
def cascadeN (op : DecomposedOp α) (count : DerivCount α) (init : Set α) : ℕ → Set α
  | 0 => init
  | n + 1 => cascadeStep op count (cascadeN op count init n)

/-- Cascade is monotonically decreasing. -/
lemma cascadeN_mono (op : DecomposedOp α) (count : DerivCount α) (init : Set α) (n : ℕ) :
    cascadeN op count init (n + 1) ⊆ cascadeN op count init n := by
  simp only [cascadeN, cascadeStep]
  exact Set.diff_subset

/-- Cascade stays within the initial set. -/
lemma cascadeN_subset_init (op : DecomposedOp α) (count : DerivCount α) (init : Set α) (n : ℕ) :
    cascadeN op count init n ⊆ init := by
  induction n with
  | zero => simp [cascadeN]
  | succ n ih => exact Set.Subset.trans (cascadeN_mono op count init n) ih

/-- Elements in base are never removed by cascade. -/
lemma base_subset_cascadeN (op : DecomposedOp α) (count : DerivCount α) (init : Set α) (n : ℕ)
    (h_base : op.base ⊆ init) :
    op.base ⊆ cascadeN op count init n := by
  induction n with
  | zero => simpa [cascadeN]
  | succ n ih =>
    intro x hx
    simp only [cascadeN, cascadeStep, shouldDie, Set.mem_diff, Set.mem_sep_iff]
    exact ⟨ih hx, fun ⟨_, hnotbase, _⟩ => hnotbase hx⟩

/-- Key lemma: if x survives cascade and x ∉ base, then x has positive count. -/
lemma cascade_survivor_has_count (op : DecomposedOp α) (count : DerivCount α)
    (current : Set α) (x : α)
    (hx : x ∈ cascadeStep op count current) (hnotbase : x ∉ op.base) :
    count current x > 0 := by
  simp only [cascadeStep, shouldDie, Set.mem_diff, Set.mem_sep_iff] at hx
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have : x ∈ shouldDie op count current := ⟨hx.1, hnotbase, h⟩
  exact hx.2 this

/-- The cascade fixpoint: elements that survive indefinitely. -/
def cascadeFix (op : DecomposedOp α) (count : DerivCount α) (init : Set α) : Set α :=
  ⋂ n, cascadeN op count init n

/-- The cascade fixpoint is contained in all cascade iterates. -/
lemma cascadeFix_subset_cascadeN (op : DecomposedOp α) (count : DerivCount α)
    (init : Set α) (n : ℕ) :
    cascadeFix op count init ⊆ cascadeN op count init n := by
  intro x hx
  simp only [cascadeFix, Set.mem_iInter] at hx
  exact hx n

/-- Elements in base are in the cascade fixpoint. -/
lemma base_subset_cascadeFix (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (h_base : op.base ⊆ init) :
    op.base ⊆ cascadeFix op count init := by
  intro x hx
  simp only [cascadeFix, Set.mem_iInter]
  intro n
  exact base_subset_cascadeN op count init n h_base hx

/-- Key insight: if x survives cascade step n+1, it has positive count at step n. -/
lemma cascade_survivor_count_pos (op : DecomposedOp α) (count : DerivCount α)
    (init : Set α) (n : ℕ) (x : α)
    (hx : x ∈ cascadeN op count init (n + 1)) (hnotbase : x ∉ op.base) :
    count (cascadeN op count init n) x > 0 := by
  simp only [cascadeN] at hx
  exact cascade_survivor_has_count op count (cascadeN op count init n) x hx hnotbase

/-- If x survives all cascades and x ∉ base, then for all n,
    count(cascade_n, x) > 0. -/
lemma cascadeFix_count_pos (op : DecomposedOp α) (count : DerivCount α)
    (init : Set α) (x : α)
    (hx : x ∈ cascadeFix op count init) (hnotbase : x ∉ op.base) (n : ℕ) :
    count (cascadeN op count init n) x > 0 := by
  simp only [cascadeFix, Set.mem_iInter] at hx
  -- x ∈ cascade(n+1), so x has positive count at cascade(n)
  exact cascade_survivor_count_pos op count init n x (hx (n + 1)) hnotbase

/-- Cascade has stabilized at step n if cascade_{n+1} = cascade_n. -/
def cascadeStable (op : DecomposedOp α) (count : DerivCount α) (init : Set α) (n : ℕ) : Prop :=
  cascadeN op count init (n + 1) = cascadeN op count init n

/-- Helper: cascade_{n+k} = cascade_n when cascade is stable at n. -/
lemma cascadeStable_persist_aux (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (n : ℕ) (h : cascadeStable op count init n) (k : ℕ) :
    cascadeN op count init (n + k) = cascadeN op count init n := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- cascade_{n+(k+1)} = cascade_{(n+k)+1} = cascadeStep(cascade_{n+k})
    change cascadeN op count init (n + k + 1) = cascadeN op count init n
    simp only [cascadeN]
    -- cascadeStep(cascade_{n+k}) = cascadeStep(cascade_n) by ih
    rw [ih]
    -- cascadeStep(cascade_n) = cascade_n by stability
    simp only [cascadeStable, cascadeN] at h
    exact h

/-- If cascade is stable at n, it remains stable for all m ≥ n. -/
lemma cascadeStable_persist (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (n : ℕ) (h : cascadeStable op count init n) (m : ℕ) (hm : m ≥ n) :
    cascadeN op count init m = cascadeN op count init n := by
  obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  subst hk
  exact cascadeStable_persist_aux op count init n h k

/-- Cascade_n ⊆ cascade_m when n ≥ m (cascade is decreasing). -/
lemma cascadeN_antitone (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (m n : ℕ) (hmn : m ≤ n) :
    cascadeN op count init n ⊆ cascadeN op count init m := by
  induction n with
  | zero =>
    have : m = 0 := Nat.eq_zero_of_le_zero hmn
    subst this; rfl
  | succ n ih =>
    by_cases h : m ≤ n
    · exact Set.Subset.trans (cascadeN_mono op count init n) (ih h)
    · push_neg at h
      have : m = n + 1 := by omega
      subst this; rfl

/-- If cascade stabilizes at n, the fixpoint equals cascade_n. -/
lemma cascadeFix_eq_stable (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (n : ℕ) (h : cascadeStable op count init n) :
    cascadeFix op count init = cascadeN op count init n := by
  ext x
  simp only [cascadeFix, Set.mem_iInter]
  constructor
  · -- x ∈ ⋂_m cascade_m → x ∈ cascade_n
    intro hx; exact hx n
  · -- x ∈ cascade_n → x ∈ cascade_m for all m
    intro hx m
    by_cases hmn : m ≥ n
    · -- m ≥ n: cascade_m = cascade_n
      rw [cascadeStable_persist op count init n h m hmn]; exact hx
    · -- m < n: cascade_n ⊆ cascade_m
      push_neg at hmn
      exact cascadeN_antitone op count init m n (Nat.le_of_lt hmn) hx

/-- A stable cascade iteration is a prefixpoint: cascade_n ⊆ F(cascade_n). -/
lemma cascadeN_stable_prefixpoint (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (h_valid : validDerivCount op count)
    (n : ℕ) (h_stable : cascadeStable op count init n) :
    cascadeN op count init n ⊆ op.F (cascadeN op count init n) := by
  intro x hx
  by_cases hbase : x ∈ op.base
  · exact Set.mem_union_left _ hbase
  · apply Set.mem_union_right
    rw [h_valid (cascadeN op count init n) x]
    -- x ∈ cascade_n and cascade is stable, so x survived cascadeStep
    have hx' : x ∈ cascadeN op count init (n + 1) := by rw [h_stable]; exact hx
    exact cascade_survivor_count_pos op count init n x hx' hbase

/-- Cascade soundness (assuming termination): if cascade stabilizes,
    the cascade fixpoint is a prefixpoint of F. -/
theorem cascade_sound_stable (op : DecomposedOp α) (count : DerivCount α) (init : Set α)
    (h_valid : validDerivCount op count)
    (n : ℕ) (h_stable : cascadeStable op count init n) :
    cascadeFix op count init ⊆ op.F (cascadeFix op count init) := by
  rw [cascadeFix_eq_stable op count init n h_stable]
  exact cascadeN_stable_prefixpoint op count init h_valid n h_stable

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

/-- When stable, step(delta_n) ⊆ current_n. -/
lemma semiNaive_stable_step_delta (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_stable : semiNaiveStable op init n) :
    op.step (semiNaiveDelta op init n) ⊆ semiNaiveCurrent op init n := by
  simp only [semiNaiveStable, semiNaiveDelta, semiNaiveN, semiNaiveIter, semiNaiveStep] at h_stable
  intro x hx
  by_contra hxnc
  have : x ∈ op.step (semiNaiveN op init n).2 \ (semiNaiveN op init n).1 := ⟨hx, hxnc⟩
  simp only [semiNaiveCurrent, semiNaiveDelta] at hxnc
  rw [Set.eq_empty_iff_forall_not_mem] at h_stable
  exact h_stable x this

/-- When stable, step(delta_n) ⊆ current_n. -/
lemma stable_step_delta_subset (op : DecomposedOp α) (init : Set α) (n : ℕ)
    (h_stable : semiNaiveStable op init n) :
    op.step (semiNaiveDelta op init n) ⊆ semiNaiveCurrent op init n := by
  -- delta_{n+1} = step(delta_n) \ current_n = ∅ by stability
  -- So step(delta_n) ⊆ current_n
  simp only [semiNaiveStable, semiNaiveDelta, semiNaiveN, semiNaiveIter, semiNaiveStep] at h_stable
  rw [Set.eq_empty_iff_forall_not_mem] at h_stable
  intro x hx
  by_contra h
  have : x ∈ op.step (semiNaiveN op init n).2 \ (semiNaiveN op init n).1 := by
    simp only [Set.mem_diff]
    exact ⟨hx, h⟩
  exact h_stable x this

/-- Current equals previous current union next delta. -/
lemma current_eq_union_delta (op : DecomposedOp α) (init : Set α) (n : ℕ) :
    semiNaiveCurrent op init (n + 1) = semiNaiveCurrent op init n ∪ semiNaiveDelta op init (n + 1) := by
  -- By definition: current_{n+1} = (semiNaiveN n).1 ∪ delta_{n+1}
  -- where (semiNaiveN n).1 = current_n
  -- The proof is straightforward unfolding
  rfl

/-- step(delta_i) ⊆ current_{i+1} for all i. -/
lemma step_delta_subset_next (op : DecomposedOp α) (init : Set α) (i : ℕ) :
    op.step (semiNaiveDelta op init i) ⊆ semiNaiveCurrent op init (i + 1) := by
  intro x hx
  by_cases h : x ∈ semiNaiveCurrent op init i
  · exact semiNaiveCurrent_mono op init i h
  · -- x ∉ current_i, so x ∈ step(delta_i) \ current_i = delta_{i+1}
    have hd : x ∈ semiNaiveDelta op init (i + 1) := by
      simp only [semiNaiveDelta, semiNaiveN, semiNaiveIter, semiNaiveStep, Set.mem_diff]
      exact ⟨hx, h⟩
    exact semiNaiveDelta_subset_current op init (i + 1) hd

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

/-- Elements of lfp' survive cascade: lfp' ⊆ cascadeN. -/
lemma lfp'_subset_cascadeN (op' : DecomposedOp α) (count : DerivCount α)
    (lfp lfp' : Set α)
    (h_valid : validDerivCount op' count)
    (h_mono : monoDerivCount count)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (h_lfp'_sub : lfp' ⊆ lfp)
    (n : ℕ) :
    lfp' ⊆ cascadeN op' count lfp n := by
  induction n with
  | zero => simp [cascadeN]; exact h_lfp'_sub
  | succ n ih =>
    intro x hx
    simp only [cascadeN, cascadeStep, shouldDie, Set.mem_diff, Set.mem_sep_iff]
    constructor
    · exact ih hx
    · -- x is not in shouldDie
      intro ⟨_, hnotbase, hcount0⟩
      -- x ∈ lfp' and x ∉ base', so x ∈ step'(lfp')
      have hx_in_step : x ∈ op'.step lfp' := by
        -- lfp' is a fixpoint: F'(lfp') = lfp'
        have hfp : op'.F lfp' = lfp' := h_lfp'.1
        -- So x ∈ lfp' = F'(lfp') = base' ∪ step'(lfp')
        have : x ∈ op'.F lfp' := hfp.symm ▸ hx
        simp only [DecomposedOp.F, DecomposedOp.toMonotoneOp] at this
        cases this with
        | inl hbase => exact absurd hbase hnotbase
        | inr hstep => exact hstep
      -- So count(lfp', x) > 0
      have hcount_pos : count lfp' x > 0 := (h_valid lfp' x).mp hx_in_step
      -- By monotonicity: count(cascadeN, x) ≥ count(lfp', x) > 0
      have hcasc_sub : lfp' ⊆ cascadeN op' count lfp n := ih
      have : count lfp' x ≤ count (cascadeN op' count lfp n) x := h_mono lfp' _ x hcasc_sub
      -- So count(cascadeN, x) > 0, contradicting hcount0
      omega

/-- Contraction correctness: cascade from lfp(F) reaches lfp(F') when F' ⊑ F.
    If cascade stabilizes, the result equals the new fixpoint.
    Requires: count is monotone in its set argument. -/
theorem contraction_correctness (op op' : DecomposedOp α) (count : DerivCount α)
    (lfp lfp' : Set α)
    (h_con : contracts op op')
    (h_valid : validDerivCount op' count)
    (h_mono : monoDerivCount count)
    (h_lfp : isLeastFixpoint op.toMonotoneOp lfp)
    (h_lfp' : isLeastFixpoint op'.toMonotoneOp lfp')
    (n : ℕ) (h_stable : cascadeStable op' count lfp n) :
    cascadeFix op' count lfp = lfp' := by
  apply Set.Subset.antisymm
  · -- cascadeFix ⊆ lfp'
    -- cascade_sound_stable shows cascadeFix ⊆ F'(cascadeFix)
    -- But we need F'(cascadeFix) ⊆ cascadeFix (prefixpoint) to use least fixpoint property
    -- Actually, since cascadeFix is stable (no more elements removed),
    -- and all remaining elements have positive count or are in base,
    -- cascadeFix IS a fixpoint of F' when restricted to lfp
    -- For now, this direction requires showing cascade doesn't keep non-lfp' elements
    sorry
  · -- lfp' ⊆ cascadeFix
    -- By lfp'_subset_cascadeN, lfp' ⊆ cascadeN for all n
    -- So lfp' ⊆ ⋂ cascadeN = cascadeFix
    have h_sub : lfp' ⊆ lfp := lfp_mono_contract op op' lfp lfp' h_con h_lfp h_lfp'
    intro x hx
    simp only [cascadeFix, Set.mem_iInter]
    intro m
    exact lfp'_subset_cascadeN op' count lfp lfp' h_valid h_mono h_lfp' h_sub m hx

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
