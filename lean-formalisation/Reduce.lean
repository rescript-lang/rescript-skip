import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

open Multiset
open List

universe u v

namespace Reduce

-- Section 2: Preliminaries.
-- Definition (Collection).
-- A collection is a function from keys to multisets of values.
abbrev Collection (K : Type u) (V : Type v) :=
  K → Multiset V

-- Section 2: Preliminaries.
-- Update operation A × V → A, written in curried Lean style.
abbrev UpdateOp (A : Type u) (V : Type v) :=
  A → V → A

-- Section 2: Preliminaries.
-- Definition (Pairwise Commutative Operation).
-- Pairwise commutativity: (a ⋆ v₁) ⋆ v₂ = (a ⋆ v₂) ⋆ v₁.
def pairwiseComm {A : Type u} {V : Type v} (op : UpdateOp A V) : Prop :=
  ∀ (a : A) (v₁ v₂ : V), op (op a v₁) v₂ = op (op a v₂) v₁

-- Section 2: Preliminaries.
-- Definition (Fold over Sequence for an Operation).
-- Fold over a finite sequence (list) for an update operation.
def foldSeq {A : Type u} {V : Type v} (op : UpdateOp A V) : A → List V → A
  | a, []       => a
  | a, v :: vs  => foldSeq op (op a v) vs

-- Section 2: Preliminaries.
-- Auxiliary property used in Theorem 1:
-- order-independence of folding over lists (foldSeq depends only on the permutation class).
def orderIndependent {A : Type u} {V : Type v} (op : UpdateOp A V) : Prop :=
  ∀ (a : A) (l₁ l₂ : List V), l₁.Perm l₂ → foldSeq op a l₁ = foldSeq op a l₂

-- Section 2: Preliminaries.
-- Definition (Fold over Multiset for an Operation), via an enumeration.
noncomputable def foldMultiset {A : Type u} {V : Type v}
    (op : UpdateOp A V) (a : A) (s : Multiset V) : A :=
  foldSeq op a s.toList

-- Sanity check: collections and a simple numeric update op.

example {K V : Type u} (C : Collection K V) (k : K) :
    Multiset V :=
  C k

def addOp : UpdateOp Nat Nat :=
  fun a v => a + v

example : pairwiseComm addOp := by
  intro a v₁ v₂
  simp [addOp, Nat.add_comm, Nat.add_left_comm]

-- Section 2: Theorem 1 (Characterisation of Multiset Fold).
-- One direction: order-independence implies pairwise commutativity.
theorem characterisationMultisetFold_forward {A : Type u} {V : Type v}
    {op : UpdateOp A V} (h : orderIndependent op) :
    pairwiseComm op := by
  intro a v₁ v₂
  -- [v₁, v₂] is a permutation of [v₂, v₁]
  have hperm : List.Perm [v₁, v₂] [v₂, v₁] := by
    simpa using (List.Perm.swap v₂ v₁ [])
  -- apply order-independence and expand the folds
  have hfold := h a [v₁, v₂] [v₂, v₁] hperm
  simpa [foldSeq] using hfold

-- Section 2: Preliminaries (helper for Theorem 1).
-- foldSeq is invariant under list permutations, assuming pairwise commutativity.
theorem foldSeq_perm {A : Type u} {V : Type v}
    (op : UpdateOp A V) (hcomm : pairwiseComm op) :
    ∀ (a : A) {l₁ l₂ : List V}, l₁.Perm l₂ → foldSeq op a l₁ = foldSeq op a l₂ := by
  intro a l₁ l₂ hperm
  induction hperm generalizing a with
  | nil =>
      rfl
  | @cons x l₁ l₂ hperm ih =>
      -- x :: l₁ ~ x :: l₂
      simp [foldSeq, ih]    -- both sides reduce to foldSeq op (op a x) …
  | @swap x y l =>
      -- y :: x :: l ~ x :: y :: l
      simp [foldSeq]        -- goal: foldSeq op (op (op a y) x) l = foldSeq op (op (op a x) y) l
      have hxy : op (op a y) x = op (op a x) y := by
        have := hcomm a x y
        -- hcomm: op (op a x) y = op (op a y) x
        simpa using this.symm
      simp [hxy]
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      -- l₁ ~ l₂ and l₂ ~ l₃ ⇒ l₁ ~ l₃
      calc
        foldSeq op a l₁ = foldSeq op a l₂ := ih₁ a
        _                = foldSeq op a l₃ := ih₂ a

-- Section 2: Preliminaries.
-- Fold over append: folding over l₁ ++ l₂ is folding over l₁ then l₂.
lemma foldSeq_append {A : Type u} {V : Type v}
    (op : UpdateOp A V) (a : A) (l₁ l₂ : List V) :
    foldSeq op a (l₁ ++ l₂) = foldSeq op (foldSeq op a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil =>
      -- ([] ++ l₂) = l₂
      simp [foldSeq]
  | cons x xs ih =>
      -- ((x :: xs) ++ l₂) = x :: (xs ++ l₂)
      simp [foldSeq, ih, List.cons_append]

-- Section 2: Preliminaries.
-- Fold over Multiset is independent of the chosen enumeration (well-definedness).
lemma foldMultiset_wellDefined {A : Type u} {V : Type v}
    (op : UpdateOp A V) (hcomm : pairwiseComm op) (a : A)
    (s : Multiset V) (l : List V) (h : (l : Multiset V) = s) :
    foldSeq op a l = foldMultiset op a s := by
  classical
  have h_toList : (s.toList : Multiset V) = s := Multiset.coe_toList s
  have h_eq : (l : Multiset V) = (s.toList : Multiset V) :=
    h.trans h_toList.symm
  have hperm : l.Perm s.toList :=
    (Multiset.coe_eq_coe (α := V)).1 h_eq
  have hfold := foldSeq_perm op hcomm a hperm
  simpa [foldMultiset] using hfold

-- Section 2: Preliminaries.
-- Lemma (Fold over Union of Multisets).
lemma foldMultiset_union {A : Type u} {V : Type v}
    (op : UpdateOp A V) (hcomm : pairwiseComm op) (a : A)
    (M N : Multiset V) :
    foldMultiset op a (M + N) =
      foldMultiset op (foldMultiset op a M) N := by
  classical
  -- Represent `M + N` by the concatenation of `M.toList` and `N.toList`.
  have hMN :
      ((M.toList ++ N.toList : List V) : Multiset V) = M + N := by
    -- First, relate `M.toList ++ N.toList` to the multiset sum of the lists.
    have h₁ :
        ((M.toList ++ N.toList : List V) : Multiset V) =
          (M.toList + N.toList : Multiset V) := by
      exact (Multiset.coe_add (M.toList) (N.toList)).symm
    -- Then rewrite the multiset sum of the lists as `M + N`.
    have h₂ :
        (M.toList + N.toList : Multiset V) = M + N := by
      simp [Multiset.coe_toList]
    exact h₁.trans h₂
  -- Use well-definedness to switch from `foldMultiset` on `M + N`
  -- to a fold over the concatenated list.
  have h_fold :
      foldMultiset op a (M + N) =
        foldSeq op a (M.toList ++ N.toList) := by
    have h0 :=
      foldMultiset_wellDefined (op := op) (hcomm := hcomm) (a := a)
        (s := M + N) (l := M.toList ++ N.toList) hMN
    -- `foldMultiset_wellDefined` gives `foldSeq = foldMultiset`, so we flip it.
    simpa [foldMultiset] using h0.symm
  -- Now use the list-level append lemma and unfold `foldMultiset` on `M` and `N`.
  have h_append :
      foldSeq op a (M.toList ++ N.toList) =
        foldSeq op (foldSeq op a M.toList) N.toList := by
    simpa using foldSeq_append op a M.toList N.toList
  have h_rhs :
      foldSeq op (foldSeq op a M.toList) N.toList =
        foldMultiset op (foldMultiset op a M) N := by
    simp [foldMultiset]
  -- Put the pieces together.
  calc
    foldMultiset op a (M + N)
        = foldSeq op a (M.toList ++ N.toList) := h_fold
    _   = foldSeq op (foldSeq op a M.toList) N.toList := h_append
    _   = foldMultiset op (foldMultiset op a M) N := h_rhs

-- Section 2: Theorem 1 (Characterisation of Multiset Fold).
-- Converse direction: pairwise commutativity implies order-independence.
theorem characterisationMultisetFold_backward {A : Type u} {V : Type v}
    {op : UpdateOp A V} (hcomm : pairwiseComm op) :
    orderIndependent op := by
  intro a l₁ l₂ hperm
  exact foldSeq_perm op hcomm a hperm

-- Section 2: Theorem 1 (Characterisation of Multiset Fold), as an equivalence.
theorem characterisationMultisetFold {A : Type u} {V : Type v}
    (op : UpdateOp A V) :
    orderIndependent op ↔ pairwiseComm op :=
  ⟨characterisationMultisetFold_forward, characterisationMultisetFold_backward⟩


-- Section 4: Incremental Updates.
-- Definition (Reducer).
-- A reducer packs an initial value and add/remove update operations.
structure Reducer (A : Type u) (V : Type v) where
  ι : A
  add : UpdateOp A V
  remove : UpdateOp A V

-- Section 4: Incremental Updates.
-- Reducer-level pairwise commutativity (both add and remove).
def Reducer.pairwiseComm {A : Type u} {V : Type v} (R : Reducer A V) : Prop :=
  Reduce.pairwiseComm R.add ∧ Reduce.pairwiseComm R.remove

-- Section 4: Incremental Updates.
-- Definition (Well-Formed Reducer).
-- Well-formedness: remove undoes add on reachable accumulator values.
def WellFormedReducer {A : Type u} {V : Type v} (R : Reducer A V) : Prop :=
  ∀ (M : Multiset V) (v : V),
    R.remove (R.add (foldMultiset R.add R.ι M) v) v =
      foldMultiset R.add R.ι M

-- Section 4: Aggregate Classes.
-- Definition (Distributive Aggregate).
def DistributiveAggregate {A : Type u} {V : Type v}
    (ι : A) (op : UpdateOp A V) : Prop :=
  ∀ (M N : Multiset V),
    foldMultiset op ι (M + N) =
      foldMultiset op (foldMultiset op ι M) N

-- Section 4: Aggregate Classes.
-- Pairwise commutativity implies the distributive-aggregate law (Lemma 1).
lemma distributiveAggregate_of_pairwiseComm {A : Type u} {V : Type v}
    (ι : A) {op : UpdateOp A V} (hcomm : pairwiseComm op) :
    DistributiveAggregate ι op := by
  intro M N
  simpa [DistributiveAggregate] using
    (foldMultiset_union (op := op) (hcomm := hcomm) (a := ι) M N)

-- Section 4: Aggregate Classes.
-- Definition (Invertible Distributive Aggregate) for a reducer.
def InvertibleDistributiveAggregate {A : Type u} {V : Type v}
    (R : Reducer A V) : Prop :=
  DistributiveAggregate R.ι R.add ∧ WellFormedReducer R

-- Section 4: Aggregate Classes.
-- For reducers with pairwise-commutative add/remove, well-formedness
-- is equivalent to being an invertible distributive aggregate.
lemma wellFormedReducer_iff_invertibleDistributive {A : Type u} {V : Type v}
    (R : Reducer A V) (hcomm : Reducer.pairwiseComm R) :
    InvertibleDistributiveAggregate R ↔ WellFormedReducer R := by
  constructor
  · intro h
    exact h.2
  · intro hWF
    -- distributivity follows from pairwise commutativity of `add`
    exact And.intro (distributiveAggregate_of_pairwiseComm R.ι hcomm.1) hWF

-- Section 3: Reduce Combinator.
-- Definition (Reduce Combinator).
-- The reduce combinator for a reducer and a collection.
noncomputable def reduce {K : Type u} {A : Type u} {V : Type v}
    (R : Reducer A V) (C : Collection K V) : K → A :=
  fun k => foldMultiset R.add R.ι (C k)

-- Section 4: Incremental Updates.
-- Definition (Delta).
-- Deltas: added and removed multisets of values per key.
structure Delta (K : Type u) (V : Type v) where
  added : K → Multiset V
  removed : K → Multiset V

-- Section 4: Incremental Updates.
-- Definition (Valid Delta for a Collection).
def ValidDelta {K : Type u} {V : Type v}
    (C : Collection K V) (Δ : Delta K V) : Prop :=
  ∀ k, Δ.removed k ≤ C k

-- Section 4: Incremental Updates.
-- Definition (Delta Application) on collections.
noncomputable def applyDelta {K : Type u} {V : Type v} [DecidableEq V]
    (C : Collection K V) (Δ : Delta K V) : Collection K V :=
  fun k => (Multiset.sub (C k) (Δ.removed k)) + Δ.added k

-- Section 4: Incremental Updates.
-- Definition (Incremental Reduce).
-- Incremental update: first remove, then add.
noncomputable def update {K : Type u} {A : Type u} {V : Type v}
    (R : Reducer A V) (a : A) (Δ : Delta K V) (k : K) : A :=
  let a' := foldMultiset R.remove a (Δ.removed k)
  foldMultiset R.add a' (Δ.added k)

-- -------------------------------------------------------------
-- Section 5: Correctness.
-- Incremental correctness property (per key) for a reducer.
def IncrementalCorrectnessProperty {K : Type u} {A : Type u} {V : Type v}
    [DecidableEq V] (R : Reducer A V) : Prop :=
  ∀ (C : Collection K V) (Δ : Delta K V),
    ValidDelta C Δ →
    ∀ k : K,
      reduce R (applyDelta C Δ) k =
        update R (reduce R C k) Δ k

-- The remaining Section 5 lemmas from the paper are left as
-- commented-out skeletons for now; we will turn them into
-- fully proved Lean lemmas one by one.

-- Helper lemma: cancellation over a decomposed multiset M₀ ⊎ D.
lemma cancellation_decomposed {A : Type u} {V : Type v}
    (R : Reducer A V)
    (hWF : WellFormedReducer R)
    (hAdd : pairwiseComm R.add)
    (hRem : pairwiseComm R.remove) :
    ∀ (D M₀ : Multiset V),
      foldMultiset R.remove (foldMultiset R.add R.ι (M₀ + D)) D =
        foldMultiset R.add R.ι M₀ := by
  classical
  intro D
  -- Induction on the multiset `D`.
  refine Multiset.induction_on D ?base ?step
  · -- Base case: D = 0.
    intro M₀
    simp [foldMultiset, foldSeq]
  · -- Inductive step: D = v ::ₘ D'
    intro v D' ih M₀
    -- Let M' := M₀ + D'.
    let M' : Multiset V := M₀ + D'
    -- First, relate M₀ + (v ::ₘ D') to M' + {v}.
    have hM : M₀ + v ::ₘ D' = M' + ({v} : Multiset V) := by
      -- M₀ + v ::ₘ D' = v ::ₘ (M₀ + D')
      have h1 : M₀ + v ::ₘ D' = v ::ₘ (M₀ + D') := by
        exact (Multiset.add_cons v M₀ D')
      -- v ::ₘ (M₀ + D') = {v} + (M₀ + D')
      have h2 : v ::ₘ (M₀ + D') = ({v} : Multiset V) + (M₀ + D') := by
        -- `singleton_add` already states `{v} + (M₀ + D') = v ::ₘ (M₀ + D')`.
        -- We just use it in the desired orientation.
        exact (Multiset.singleton_add v (M₀ + D')).symm
      -- {v} + (M₀ + D') = (M₀ + D') + {v} = M' + {v}
      calc
        M₀ + v ::ₘ D'
            = v ::ₘ (M₀ + D') := h1
        _   = ({v} : Multiset V) + (M₀ + D') := h2
        _   = (M₀ + D') + ({v} : Multiset V) := by
                simpa using
                  (Multiset.add_comm (({v} : Multiset V)) (M₀ + D'))
        _   = M' + ({v} : Multiset V) := by
                simp [M']
    -- Fold-add over M₀ + (v ::ₘ D') factors as fold-add over M' and then the singleton {v}.
    have hAgg :
        foldMultiset R.add R.ι (M₀ + v ::ₘ D') =
          R.add (foldMultiset R.add R.ι M') v := by
      -- Use the distributivity lemma for `add` on M' and {v}.
      have h_union :
          foldMultiset R.add R.ι (M' + ({v} : Multiset V)) =
            foldMultiset R.add (foldMultiset R.add R.ι M') ({v} : Multiset V) :=
        foldMultiset_union (op := R.add) (hcomm := hAdd)
          (a := R.ι) (M := M') (N := ({v} : Multiset V))
      -- Rewrite M' + {v} back to M₀ + v ::ₘ D', and simplify the singleton fold.
      have h_union' :
          foldMultiset R.add R.ι (M₀ + v ::ₘ D') =
            foldMultiset R.add (foldMultiset R.add R.ι M') ({v} : Multiset V) := by
        -- First rewrite the multiset argument using `hM`, then apply `h_union`.
        calc
          foldMultiset R.add R.ι (M₀ + v ::ₘ D')
              = foldMultiset R.add R.ι (M' + ({v} : Multiset V)) := by
                  simp [hM]
          _ = foldMultiset R.add (foldMultiset R.add R.ι M') ({v} : Multiset V) :=
                  h_union
      -- Over a singleton multiset, `foldMultiset` is a single application of `add`.
      simpa [foldMultiset, foldSeq] using h_union'
    -- Removing the singleton {v} cancels the last add, by well-formedness.
    have h_remove_singleton :
        foldMultiset R.remove
            (foldMultiset R.add R.ι (M₀ + v ::ₘ D')) ({v} : Multiset V) =
          foldMultiset R.add R.ι M' := by
      -- First identify the accumulator using `hAgg`, then apply well-formedness.
      have hWF_M' := hWF M' v
      -- From `hAgg` and well-formedness we get a cancellation equation at `v`.
      have h_cancel :
          R.remove (foldMultiset R.add R.ι (M₀ + v ::ₘ D')) v =
            foldMultiset R.add R.ι M' := by
        -- Rewrite the accumulator using `hAgg`, then apply `hWF_M'`.
        have hAgg' :
            R.remove (foldMultiset R.add R.ι (M₀ + v ::ₘ D')) v =
              R.remove (R.add (foldMultiset R.add R.ι M') v) v :=
          congrArg (fun x => R.remove x v) hAgg
        exact hAgg'.trans hWF_M'
      -- `foldMultiset` over a singleton is just one application of the op.
      simpa [foldMultiset, foldSeq] using h_cancel
    -- Now decompose the fold over D = v ::ₘ D' as a fold over {v} then D'.
    calc
      foldMultiset R.remove (foldMultiset R.add R.ι (M₀ + v ::ₘ D')) (v ::ₘ D')
          = foldMultiset R.remove
              (foldMultiset R.add R.ι (M₀ + v ::ₘ D'))
              (({v} : Multiset V) + D') := by
                -- Rewrite `v ::ₘ D'` as `{v} + D'`.
                have hD : (v ::ₘ D') = ({v} : Multiset V) + D' := by
                  -- `singleton_add` already states `{v} + D' = v ::ₘ D'`.
                  -- We just use it in the desired orientation.
                  exact (Multiset.singleton_add v D').symm
                exact congrArg
                  (fun s => foldMultiset R.remove
                      (foldMultiset R.add R.ι (M₀ + v ::ₘ D')) s)
                  hD
      _ = foldMultiset R.remove
            (foldMultiset R.remove
              (foldMultiset R.add R.ι (M₀ + v ::ₘ D'))
              ({v} : Multiset V))
            D' := by
              -- Apply the distributivity lemma for `remove` over `{v} + D'`.
              exact
                (foldMultiset_union (op := R.remove) (hcomm := hRem)
                  (a := foldMultiset R.add R.ι (M₀ + v ::ₘ D'))
                  (M := ({v} : Multiset V)) (N := D'))
      _ = foldMultiset R.remove
            (foldMultiset R.add R.ι M') D' := by
              -- Cancel the `{v}` using `h_remove_singleton`.
              exact
                congrArg
                  (fun x => foldMultiset R.remove x D')
                  h_remove_singleton
      _ = foldMultiset R.add R.ι M₀ := by
              -- Use the induction hypothesis on D' and M₀, noting M' = M₀ + D'.
              simpa [M'] using ih M₀

-- Section 5: Correctness.
-- Cancellation for a Delta, phrased for arbitrary collections.
lemma cancellationForDelta {K : Type u} {A : Type u} {V : Type v}
    [DecidableEq V]
    (R : Reducer A V)
    (hWF : WellFormedReducer R)
    (hcomm : Reducer.pairwiseComm R)
    (C : Collection K V) (Δ : Delta K V)
    (hΔ : ValidDelta C Δ) (k : K) :
    foldMultiset R.remove
        (foldMultiset R.add R.ι (C k)) (Δ.removed k) =
      foldMultiset R.add R.ι ((C k) - Δ.removed k) := by
  classical
  -- Notation: M is the original multiset, D the removed part.
  let M : Multiset V := C k
  let D : Multiset V := Δ.removed k
  have hle : D ≤ M := by
    -- ValidDelta tells us that removed k ≤ C k.
    simpa [M, D] using hΔ k
  -- Let M₀ be the remaining multiset after removing D.
  let M₀ : Multiset V := M - D
  -- Using multiset subtraction, we know that (M - D) + D = M.
  have h_decomp : M₀ + D = M := by
    -- `sub_add_cancel` yields `M - D + D = M`.
    simpa [M₀] using (Multiset.sub_add_cancel (s := M) (t := D) hle)
  -- Apply cancellation over the decomposed multiset M₀ ⊎ D.
  have h_cancel :=
    cancellation_decomposed (R := R) (hWF := hWF)
      (hAdd := hcomm.1) (hRem := hcomm.2) D M₀
  -- Rewrite the accumulator using the decomposition M = M₀ + D.
  have h_cancel' :
      foldMultiset R.remove
          (foldMultiset R.add R.ι M) D =
        foldMultiset R.add R.ι M₀ := by
    -- `h_cancel` is stated with `M₀ + D`; rewrite it to use `M`.
    simpa [h_decomp] using h_cancel
  -- Finally, unfold the local definitions of M, D, M₀.
  simpa [M, D, M₀] using h_cancel'

-- Section 5: Correctness.
-- (Soundness direction) Well-formed reducers satisfy incremental correctness.
theorem wellFormedReducer_implies_incrementalCorrectness
    {K : Type u} {A : Type u} {V : Type v} [DecidableEq V]
    (R : Reducer A V) (hWF : WellFormedReducer R) (hcomm : Reducer.pairwiseComm R) :
    IncrementalCorrectnessProperty (K := K) R := by
  classical
  -- We unfold the incremental correctness property and work pointwise.
  intro C Δ hΔ k
  -- Notation at the key k.
  let M : Multiset V := C k
  let Dminus : Multiset V := Δ.removed k
  let Dplus : Multiset V := Δ.added k
  -- Distributivity of the add operation.
  have hDA : DistributiveAggregate R.ι R.add :=
    distributiveAggregate_of_pairwiseComm R.ι hcomm.1
  -- First compute the denotational recomputation path.
  have h_recompute :
      reduce R (applyDelta C Δ) k =
        foldMultiset R.add R.ι ((Multiset.sub M Dminus) + Dplus) := by
    -- `applyDelta` removes `Dminus` and then adds `Dplus`.
    simp [reduce, applyDelta, M, Dminus, Dplus]
  -- Next compute the incremental update path.
  have h_incremental :
      update R (reduce R C k) Δ k =
        foldMultiset R.add
          (foldMultiset R.add R.ι (Multiset.sub M Dminus)) Dplus := by
    -- Start from the definition of `update`, then simplify the removal step
    -- using `cancellationForDelta`, and finally rewrite using our notation.
    have h_cancel :=
      cancellationForDelta (R := R) (hWF := hWF) (hcomm := hcomm)
        (C := C) (Δ := Δ) (hΔ := hΔ) (k := k)
    -- `h_cancel` simplifies the intermediate accumulator after removals.
    have h_cancel' :
        foldMultiset R.remove
            (foldMultiset R.add R.ι M) Dminus =
          foldMultiset R.add R.ι (Multiset.sub M Dminus) := by
      -- This is just `h_cancel` specialized at `k`, rewritten with our
      -- local names for `M` and `Dminus`.
      -- Note that `M - Dminus` is definitionally `Multiset.sub M Dminus`.
      simpa [M, Dminus] using h_cancel
    -- Now expand `update` and `reduce` and use `h_cancel'`.
    simp [update, reduce, M, Dminus, Dplus, h_cancel']
  -- Finally, connect both paths via distributivity of `add`.
  have h_distrib :
      foldMultiset R.add R.ι ((Multiset.sub M Dminus) + Dplus) =
        foldMultiset R.add
          (foldMultiset R.add R.ι (Multiset.sub M Dminus)) Dplus :=
    hDA (Multiset.sub M Dminus) Dplus
  -- Chain the equalities to conclude.
  calc
    reduce R (applyDelta C Δ) k
        = foldMultiset R.add R.ι ((M - Dminus) + Dplus) := h_recompute
    _   = foldMultiset R.add
            (foldMultiset R.add R.ι (M - Dminus)) Dplus := h_distrib
    _   = update R (reduce R C k) Δ k := h_incremental.symm

-- Section 5: Correctness.
-- (Full characterization) Well-formedness ⇔ incremental correctness.
-- We assume `K` is inhabited so that the incremental
-- correctness property is non-vacuous.
theorem wellFormedReducer_iff_incrementalCorrectness
    {K : Type u} {A : Type u} {V : Type v} [DecidableEq V] [Inhabited K]
    (R : Reducer A V) (hcomm : Reducer.pairwiseComm R) :
    WellFormedReducer R ↔ IncrementalCorrectnessProperty (K := K) R := by
  constructor
  · -- Soundness direction: well-formed ⇒ incremental correctness.
    intro hWF
    exact wellFormedReducer_implies_incrementalCorrectness
      (K := K) (R := R) hWF hcomm
  · -- Completeness direction: incremental correctness ⇒ well-formedness.
    intro hIC
    classical
    -- We must show that remove undoes add on reachable
    -- accumulator values, i.e. on folds over multisets.
    refine fun M v => ?_
    -- Define a constant collection with a single logical key,
    -- whose multiset is `M ⊎ {v}` at every key.
    let C' : Collection K V := fun _ => M + ({v} : Multiset V)
    -- Define a delta that removes `{v}` and adds nothing.
    let Δ' : Delta K V :=
      { added := fun _ => (0 : Multiset V)
        removed := fun _ => ({v} : Multiset V) }
    -- This delta is valid for `C'`: the removed multiset
    -- is always a sub-multiset of `M ⊎ {v}`.
    have hValid : ValidDelta C' Δ' := by
      intro k
      -- `{v} ≤ M ⊎ {v}` since `v ∈ M ⊎ {v}`.
      have hv : v ∈ C' k := by
        simp [C']
      exact (Multiset.singleton_le (a := v) (s := C' k)).2 hv
    -- Instantiate incremental correctness at `C'`, `Δ'`
    -- and an arbitrary key (the default inhabitant of `K`).
    have hEq := hIC (C := C') (Δ := Δ') hValid (default : K)
    -- Simplify both sides of the correctness equation.
    -- Left-hand side: recompute via `applyDelta`.
    have h_left :
        reduce R (applyDelta C' Δ') (default : K) =
          foldMultiset R.add R.ι M := by
      -- `applyDelta` performs `(M ⊎ {v}) - {v} + ∅ = M`.
      have h_sub :
          Multiset.sub (M + ({v} : Multiset V)) ({v} : Multiset V) = M := by
        classical
        -- Rewrite via singleton subtraction and erase laws.
        have hv : v ∈ ({v} : Multiset V) := by simp
        calc
          Multiset.sub (M + ({v} : Multiset V)) ({v} : Multiset V)
              = (M + ({v} : Multiset V)) - ({v} : Multiset V) := rfl
          _   = (M + ({v} : Multiset V)).erase v := by
                  simp [Multiset.sub_singleton]
          _   = M + ({v} : Multiset V).erase v := by
                  -- Remove `v` from the right summand `{v}`.
                  simp [Multiset.erase_add_right_pos, hv]
          _   = M + 0 := by
                  simp
          _   = M := by
                  simp
      simp [reduce, applyDelta, C', Δ', h_sub]
    -- Right-hand side: incremental path via `update`.
    have h_right :
        update R (reduce R C' (default : K)) Δ' (default : K) =
          foldMultiset R.remove
            (foldMultiset R.add R.ι (M + ({v} : Multiset V)))
            ({v} : Multiset V) := by
      -- First unfold `reduce` at `C'`, then `update`,
      -- and finally simplify the empty-add case.
      simp [reduce, update, C', Δ', foldMultiset, foldSeq]
    -- Combine the simplified forms to get an equation
    -- between the two explicit accumulators.
    have h_fold :
        foldMultiset R.add R.ι M =
          foldMultiset R.remove
            (foldMultiset R.add R.ι (M + ({v} : Multiset V)))
            ({v} : Multiset V) := by
      -- Rewrite both sides of `hEq` using `h_left` and `h_right`.
      -- Note that `h_left` and `h_right` are definitional equalities,
      -- so we can substitute them into `hEq`.
      simpa [h_left, h_right] using hEq
    -- Now rewrite the accumulator over `M ⊎ {v}` using
    -- the distributive law for the add operation, exploiting
    -- pairwise commutativity of `add`.
    have h_add_singleton :
        foldMultiset R.add R.ι (M + ({v} : Multiset V)) =
          R.add (foldMultiset R.add R.ι M) v := by
      -- First use the multiset-union fold lemma, then simplify
      -- the fold over the singleton `{v}`.
      have h_union :
          foldMultiset R.add R.ι (M + ({v} : Multiset V)) =
            foldMultiset R.add
              (foldMultiset R.add R.ι M)
              ({v} : Multiset V) :=
        foldMultiset_union (op := R.add) (hcomm := hcomm.1)
          (a := R.ι) (M := M) (N := ({v} : Multiset V))
      -- Over a singleton multiset, `foldMultiset` applies `add` once.
      simpa [foldMultiset, foldSeq] using h_union
    -- Substitute `h_add_singleton` into `h_fold` and
    -- expand the fold over `{v}` on the remove side.
    have h_final :
        foldMultiset R.add R.ι M =
          R.remove (R.add (foldMultiset R.add R.ι M) v) v := by
      -- Rewrite the accumulator over `M ⊎ {v}` and then
      -- expand the fold over the singleton `{v}`.
      have h_fold' :
          foldMultiset R.add R.ι M =
            foldMultiset R.remove
              (R.add (foldMultiset R.add R.ι M) v)
              ({v} : Multiset V) := by
        simpa [h_add_singleton] using h_fold
      -- Now expand the fold over `{v}`.
      simpa [foldMultiset, foldSeq] using h_fold'
    -- Rearrange `h_final` to match the well-formedness statement.
    exact h_final.symm

end Reduce
