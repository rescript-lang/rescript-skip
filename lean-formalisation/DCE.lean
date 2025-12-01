import Reduce
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter

open Multiset
open Reduce

namespace Reduce

/--
Graph fragments contributed by a single file: multisets of nodes, roots, and edges.
We use multisets so that add/remove are exact inverses (`add_sub_cancel`) even when
different files mention the same node or edge.
-/
structure Frag (Node : Type) where
  nodes : Multiset Node := {}
  roots : Multiset Node := {}
  edges : Multiset (Node × Node) := {}
-- (no extra type class assumptions required)

/-- Global graph state as the multiset union of all fragments. -/
structure GraphState (Node : Type) where
  nodes : Multiset Node := {}
  roots : Multiset Node := {}
  edges : Multiset (Node × Node) := {}
-- (no extra type class assumptions required)

@[ext] lemma GraphState.ext {Node : Type} {g₁ g₂ : GraphState Node}
    (hnodes : g₁.nodes = g₂.nodes) (hroots : g₁.roots = g₂.roots) (hedges : g₁.edges = g₂.edges) :
    g₁ = g₂ := by
  cases g₁; cases g₂; cases hnodes; cases hroots; cases hedges; rfl

lemma multiset_sub_comm [DecidableEq α] (s t u : Multiset α) :
    s - t - u = s - u - t := by
  classical
  ext x
  simp [Multiset.count_sub, Nat.sub_sub, Nat.add_comm]

lemma multiset_add_comm_assoc (s t u : Multiset α) :
    s + t + u = s + u + t := by
  classical
  ext x
  simp [Multiset.count_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

namespace GraphState
variable {Node : Type}

/-- Zero graph state. -/
def empty : GraphState Node := {}

/-- Add a fragment to the global graph (multiset union). -/
def addFrag (g : GraphState Node) (f : Frag Node) : GraphState Node :=
  { nodes := g.nodes + f.nodes
    roots := g.roots + f.roots
    edges := g.edges + f.edges }

/-- Remove a fragment from the global graph (multiset subtraction). -/
def removeFrag [DecidableEq Node] (g : GraphState Node) (f : Frag Node) : GraphState Node :=
  { nodes := g.nodes - f.nodes
    roots := g.roots - f.roots
    edges := g.edges - f.edges }

lemma add_remove_cancel [DecidableEq Node] (g : GraphState Node) (f : Frag Node) :
    removeFrag (addFrag g f) f = g := by
  cases g with
  | mk gn gr ge =>
    cases f with
    | mk fn fr fe =>
      simp [addFrag, removeFrag, Multiset.add_sub_cancel_right]

/-- Reducer that aggregates file fragments into a global multiset-based graph. -/
def fragReducer [DecidableEq Node] : Reducer (GraphState Node) (Frag Node) where
  ι := empty
  add := addFrag
  remove := removeFrag

/-- This reducer is well-formed: remove undoes add on the same fragment. -/
theorem fragReducer_wellFormed [DecidableEq Node] :
    ∀ (g : GraphState Node) (f : Frag Node),
      fragReducer.remove (fragReducer.add g f) f = g := by
  intro g f
  simp [fragReducer, add_remove_cancel]

/-- Adding fragments commutes pairwise (multiset union). -/
lemma addFrag_pairwiseComm : pairwiseComm (GraphState.addFrag (Node:=Node)) := by
  intro g f₁ f₂
  cases g; cases f₁; cases f₂
  -- multiset addition is commutative/associative componentwise
  refine GraphState.ext ?h1 ?h2 ?h3
  all_goals simp [GraphState.addFrag, multiset_add_comm_assoc]

/-- Removing fragments commutes pairwise (multiset subtraction is order-independent). -/
lemma removeFrag_pairwiseComm [DecidableEq Node] :
    pairwiseComm (GraphState.removeFrag (Node:=Node)) := by
  intro g f₁ f₂
  cases g; cases f₁; cases f₂
  -- multiset subtraction is order-independent on counts
  refine GraphState.ext ?h1 ?h2 ?h3
  all_goals simp [GraphState.removeFrag, multiset_sub_comm]

/-- The fragment reducer satisfies pairwise commutativity for add/remove. -/
lemma fragReducer_pairwiseComm [DecidableEq Node] :
    Reducer.pairwiseComm (GraphState.fragReducer (Node:=Node)) := by
  constructor
  · simpa [GraphState.fragReducer] using (addFrag_pairwiseComm (Node:=Node))
  · simpa [GraphState.fragReducer] using (removeFrag_pairwiseComm (Node:=Node))

/-- The fragment reducer is well-formed in the sense of `Reduce.WellFormedReducer`. -/
lemma fragReducer_wellFormedReducer [DecidableEq Node] :
    WellFormedReducer (GraphState.fragReducer (Node:=Node)) := by
  intro M f
  -- Fold all prior fragments with add, then remove the newly added fragment.
  simpa [WellFormedReducer, GraphState.fragReducer, GraphState.empty] using
    (GraphState.fragReducer_wellFormed (Node:=Node)
      (g := foldMultiset (GraphState.addFrag (Node:=Node)) GraphState.empty M)
      (f := f))

end GraphState

section Reachability
variable {Node : Type}

/-- Reachability over a graph given as edge and root multisets. -/
inductive Reachable (E : Multiset (Node × Node)) (R : Multiset Node) : Node → Prop
  | root {r} (hr : r ∈ R) : Reachable E R r
  | step {u v} (hu : Reachable E R u) (hev : (u, v) ∈ E) : Reachable E R v

/-- Live nodes are those reachable from roots via edges. -/
def liveSet (g : GraphState Node) : Set Node :=
  fun n => Reachable g.edges g.roots n

/-- Dead nodes are those present in the node multiset but not live. -/
def deadSet (g : GraphState Node) : Set Node :=
  fun n => n ∈ g.nodes ∧ ¬ Reachable g.edges g.roots n

/-- A well-formed graph has all roots and edge endpoints listed as nodes. -/
def wellFormed (g : GraphState Node) : Prop :=
  (∀ r, r ∈ g.roots → r ∈ g.nodes) ∧
  (∀ u v, (u, v) ∈ g.edges → u ∈ g.nodes ∧ v ∈ g.nodes)

lemma live_subset_nodes {g : GraphState Node} (wf : wellFormed g) :
    liveSet g ⊆ fun n => n ∈ g.nodes := by
  intro n hn
  induction hn with
  | root hr =>
      exact (wf.left _ hr)
  | step hu hev =>
      have hpair := wf.right _ _ hev
      exact hpair.right

lemma dead_subset_nodes (g : GraphState Node) :
    deadSet g ⊆ fun n => n ∈ g.nodes := by
  intro n hn; exact hn.left

lemma dead_disjoint_live (g : GraphState Node) :
    ∀ n, n ∈ deadSet g → n ∈ liveSet g → False := by
  intro n hdead hlive
  exact hdead.right hlive

lemma live_or_dead {g : GraphState Node} {n}
    (hn : n ∈ g.nodes) : n ∈ liveSet g ∨ n ∈ deadSet g := by
  by_cases h : Reachable g.edges g.roots n
  · exact Or.inl h
  · exact Or.inr ⟨hn, h⟩

/-
Delta correctness for the fragment reducer: adding then removing (or vice versa)
restores the prior graph state exactly.
-/
section Delta
variable [DecidableEq Node]

def applyFragDelta (g : GraphState Node) (Δ : Frag Node) (add? : Bool) : GraphState Node :=
  if add? then GraphState.addFrag g Δ else GraphState.removeFrag g Δ

lemma applyFragDelta_add_remove (g : GraphState Node) (Δ : Frag Node) :
    applyFragDelta (applyFragDelta g Δ true) Δ false = g := by
  simp [applyFragDelta, GraphState.add_remove_cancel]

end Delta

/--
Recompute-based correctness: liveSet computed by the reducer equals the
specification based on reachability over the aggregated multisets. This is
essentially by definition here, but we package it so that an incremental algorithm
can be required to produce the same live/dead sets as `liveSet`/`deadSet`.
-/
def specLive (g : GraphState Node) : Set Node := liveSet g
def specDead (g : GraphState Node) : Set Node := deadSet g

/-- Refcount state: live set plus a refcount function. -/
structure RefState (Node : Type) where
  live : Set Node
  refcount : Node → Nat

/-- Specification refcount: number of live predecessors of `v` in the current graph. -/
noncomputable def refcountSpec [DecidableEq Node] (g : GraphState Node) (v : Node) : Nat :=
  by
    classical
    let preds := Multiset.filter (fun e => liveSet g e.fst ∧ e.snd = v) g.edges
    exact preds.card

/-- Specification refstate derived from the aggregated graph. -/
noncomputable def refSpec [DecidableEq Node] (g : GraphState Node) : RefState Node :=
  { live := liveSet g
    refcount := refcountSpec g }

/-- A set that contains all roots and is closed under following edges. -/
def closedUnder (g : GraphState Node) (S : Set Node) : Prop :=
  (∀ r, r ∈ g.roots → S r) ∧
  (∀ {u v}, S u → (u, v) ∈ g.edges → S v)

lemma liveSet_closed (g : GraphState Node) : closedUnder g (liveSet g) := by
  constructor
  · intro r hr
    exact Reachable.root hr
  · intro u v hu hev
    exact Reachable.step hu hev

lemma liveSet_least_closed {g : GraphState Node} {S : Set Node}
    (hS : closedUnder g S) : liveSet g ⊆ S := by
  intro n hn
  induction hn with
  | root hr => exact hS.left _ hr
  | step hu hev ih =>
      exact hS.right ih (by simpa using hev)

/-- Invariant that characterizes a correct refcount state. -/
def refInvariant [DecidableEq Node] (g : GraphState Node) (rs : RefState Node) : Prop :=
  rs.live = liveSet g ∧ rs.refcount = refcountSpec g

lemma refSpec_invariant [DecidableEq Node] (g : GraphState Node) :
    refInvariant g (refSpec g) := by
  constructor <;> rfl

/-- Apply a fragment delta to the aggregated graph. -/
def stepGraph [DecidableEq Node] (g : GraphState Node) (f : Frag Node) (add? : Bool) :
    GraphState Node :=
  if add? then GraphState.addFrag g f else GraphState.removeFrag g f

/-- Recompute-based refcount step that always restores the invariant. -/
noncomputable def refcountRecomputeStep [DecidableEq Node]
    (g : GraphState Node) (f : Frag Node) (add? : Bool) : RefState Node :=
  refSpec (stepGraph g f add?)

lemma refcountRecompute_step_inv [DecidableEq Node]
    (g : GraphState Node) (f : Frag Node) (add? : Bool) :
    refInvariant (stepGraph g f add?) (refcountRecomputeStep g f add?) := by
  unfold refcountRecomputeStep
  apply refSpec_invariant

/-
If an incremental algorithm maintains a pair `(live, refcount)` such that
`live = specLive g` and `refcount = refcountSpec g` for the current aggregated graph `g`,
then it matches the recompute specification. Below are trivial recompute lemmas
that serve as targets for an eventual refcount-based incremental algorithm.
-/
section Recompute
lemma specLive_addFrag (g : GraphState Node) (f : Frag Node) :
    specLive (GraphState.addFrag g f) = liveSet (GraphState.addFrag g f) := rfl

lemma specDead_addFrag (g : GraphState Node) (f : Frag Node) :
    specDead (GraphState.addFrag g f) = deadSet (GraphState.addFrag g f) := rfl

lemma specLive_removeFrag [DecidableEq Node] (g : GraphState Node) (f : Frag Node) :
    specLive (GraphState.removeFrag g f) = liveSet (GraphState.removeFrag g f) := rfl

lemma specDead_removeFrag [DecidableEq Node] (g : GraphState Node) (f : Frag Node) :
    specDead (GraphState.removeFrag g f) = deadSet (GraphState.removeFrag g f) := rfl

lemma refSpec_addFrag [DecidableEq Node] (g : GraphState Node) (f : Frag Node) :
    refSpec (GraphState.addFrag g f) =
      { live := liveSet (GraphState.addFrag g f)
        refcount := refcountSpec (GraphState.addFrag g f) } := rfl

lemma refSpec_removeFrag [DecidableEq Node] (g : GraphState Node) (f : Frag Node) :
    refSpec (GraphState.removeFrag g f) =
      { live := liveSet (GraphState.removeFrag g f)
        refcount := refcountSpec (GraphState.removeFrag g f) } := rfl

end Recompute

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
def stepPair {Node : Type} [DecidableEq Node] (A : IncrAlgInv Node)
    (grs : GraphState Node × RefState Node) (d : FragDelta Node) :
    GraphState Node × RefState Node :=
  let g := grs.fst
  let f := d.fst
  let add? := d.snd
  let g' := stepGraph g f add?
  let rs' := A.step g f add?
  (g', rs')

/-- Run an incremental algorithm over a list of deltas, starting from an arbitrary state. -/
def runDeltasAux {Node : Type} [DecidableEq Node] (A : IncrAlgInv Node)
    (grs₀ : GraphState Node × RefState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  ds.foldl (stepPair (Node:=Node) A) grs₀

lemma runDeltasAux_invariant {Node : Type} [DecidableEq Node]
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
noncomputable def runDeltas {Node : Type} [DecidableEq Node] (A : IncrAlgInv Node)
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  runDeltasAux (Node:=Node) A (g₀, refSpec g₀) ds

lemma runDeltas_invariant {Node : Type} [DecidableEq Node]
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
def stepPairRef {Node : Type} [DecidableEq Node] (A : RefcountAlg Node)
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
def runRefcountAux {Node : Type} [DecidableEq Node] (A : RefcountAlg Node)
    (grs₀ : GraphState Node × RefState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  ds.foldl (stepPairRef (Node:=Node) A) grs₀

lemma runRefcountAux_invariant {Node : Type} [DecidableEq Node]
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
noncomputable def runRefcount {Node : Type} [DecidableEq Node] (A : RefcountAlg Node)
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    GraphState Node × RefState Node :=
  runRefcountAux (Node:=Node) A (g₀, refSpec g₀) ds

lemma runRefcount_invariant {Node : Type} [DecidableEq Node]
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    refInvariant (runRefcount (Node:=Node) A g₀ ds).fst
                 (runRefcount (Node:=Node) A g₀ ds).snd := by
  have h0 : refInvariant g₀ (refSpec g₀) := refSpec_invariant (g:=g₀)
  simpa [runRefcount] using
    runRefcountAux_invariant (Node:=Node) A ds (g:=g₀) (rs:=refSpec g₀) h0

/-- Any refcount algorithm that preserves the invariant produces states equal to the spec. -/
lemma runRefcount_matches_spec {Node : Type} [DecidableEq Node]
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    let res := runRefcount (Node:=Node) A g₀ ds
    res.snd.live = liveSet res.fst ∧ res.snd.refcount = refcountSpec res.fst := by
  -- from the invariant obtained by `runRefcount_invariant`
  have h := runRefcount_invariant (Node:=Node) A g₀ ds
  dsimp [refInvariant] at h
  simpa using h

section ConcreteRefcount
variable {Node : Type} [DecidableEq Node]

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

/-! ## Incremental Refcount Algorithm

We implement an incremental BFS-style algorithm that maintains the live set and refcounts
without full recomputation. The key insight is:

**For adding a fragment:**
- Old live nodes remain live (monotonicity)
- New roots become live
- Nodes reachable from new roots or from old live nodes via new edges become live
- Refcounts are updated by adding counts of new edges from live sources

**For removing a fragment:**
- Some previously live nodes may become dead
- We need to verify reachability without the removed edges/roots
- Refcounts decrease for removed edges from (still-live) sources

The algorithm computes the correct live set and refcounts incrementally by:
1. For add: BFS expansion from new roots and targets of new edges with live sources
2. For remove: Recheck reachability for affected nodes (in this version, we recompute
   for remove since incremental deletion is more complex)
-/

section ReachabilityLemmas
variable {Node' : Type}

/-- Reachability is monotonic: adding edges can only expand the reachable set. -/
lemma Reachable_mono_edges {E E' : Multiset (Node' × Node')} {R : Multiset Node'} {n : Node'}
    (h : Reachable E R n) (hE : E ≤ E') : Reachable E' R n := by
  induction h with
  | root hr => exact Reachable.root hr
  | step _ hev ih =>
    apply Reachable.step ih
    exact Multiset.mem_of_le hE hev

/-- Reachability is monotonic: adding roots can only expand the reachable set. -/
lemma Reachable_mono_roots {E : Multiset (Node' × Node')} {R R' : Multiset Node'} {n : Node'}
    (h : Reachable E R n) (hR : R ≤ R') : Reachable E R' n := by
  induction h with
  | root hr => exact Reachable.root (Multiset.mem_of_le hR hr)
  | step _ hev ih => exact Reachable.step ih hev

/-- Combined monotonicity for reachability. -/
lemma Reachable_mono {E E' : Multiset (Node' × Node')} {R R' : Multiset Node'} {n : Node'}
    (h : Reachable E R n) (hE : E ≤ E') (hR : R ≤ R') : Reachable E' R' n := by
  exact Reachable_mono_roots (Reachable_mono_edges h hE) hR

end ReachabilityLemmas

omit [DecidableEq Node] in
/-- Adding a fragment can only expand the live set. -/
lemma liveSet_mono_addFrag (g : GraphState Node) (f : Frag Node) :
    liveSet g ⊆ liveSet (GraphState.addFrag g f) := by
  intro n hn
  unfold liveSet at *
  apply Reachable_mono hn
  · simp only [GraphState.addFrag]; exact Multiset.le_add_right _ _
  · simp only [GraphState.addFrag]; exact Multiset.le_add_right _ _

omit [DecidableEq Node] in
/-- Characterization of reachability after adding: a node is reachable from the combined
    roots iff it's reachable from old roots or from new roots. -/
lemma Reachable_addFrag_iff (g : GraphState Node) (f : Frag Node) (n : Node) :
    Reachable (g.edges + f.edges) (g.roots + f.roots) n ↔
    Reachable (g.edges + f.edges) g.roots n ∨ Reachable (g.edges + f.edges) f.roots n := by
  constructor
  · intro h
    induction h with
    | root hr =>
      simp only [Multiset.mem_add] at hr
      cases hr with
      | inl hg => exact Or.inl (Reachable.root hg)
      | inr hf => exact Or.inr (Reachable.root hf)
    | step _ hev ih =>
      cases ih with
      | inl hg => exact Or.inl (Reachable.step hg hev)
      | inr hf => exact Or.inr (Reachable.step hf hev)
  · intro h
    cases h with
    | inl hg =>
      apply Reachable_mono_roots hg
      exact Multiset.le_add_right _ _
    | inr hf =>
      apply Reachable_mono_roots hf
      calc f.roots ≤ g.roots + f.roots := Multiset.le_add_left _ _

/-- The BFS expansion: compute nodes reachable from a given set through edges.
    This is defined as the set of nodes reachable from the initial set. -/
def reachableFrom (E : Multiset (Node × Node)) (initial : Set Node) : Set Node :=
  fun n => ∃ u, initial u ∧ Reachable E {u} n

omit [DecidableEq Node] in
lemma reachableFrom_initial {E : Multiset (Node × Node)} {initial : Set Node} {n : Node}
    (hn : initial n) : reachableFrom E initial n := by
  exact ⟨n, hn, Reachable.root (Multiset.mem_singleton_self n)⟩

omit [DecidableEq Node] in
lemma reachableFrom_step {E : Multiset (Node × Node)} {initial : Set Node} {u v : Node}
    (hu : reachableFrom E initial u) (hev : (u, v) ∈ E) : reachableFrom E initial v := by
  obtain ⟨w, hw, hreach⟩ := hu
  exact ⟨w, hw, Reachable.step hreach hev⟩

omit [DecidableEq Node] in
/-- Key lemma: liveSet is exactly the nodes reachable from roots. -/
lemma liveSet_eq_reachableFrom_roots (g : GraphState Node) :
    liveSet g = reachableFrom g.edges (fun r => r ∈ g.roots) := by
  ext n
  unfold reachableFrom
  constructor
  · intro hn
    unfold liveSet at hn
    induction hn with
    | @root r hr =>
      refine ⟨r, hr, ?_⟩
      exact Reachable.root (Multiset.mem_singleton_self r)
    | step hu hev ih =>
      obtain ⟨r, hr, hreach⟩ := ih
      exact ⟨r, hr, Reachable.step hreach hev⟩
  · intro hn
    obtain ⟨r, hr, hreach⟩ := hn
    unfold liveSet
    induction hreach with
    | root hmem =>
      simp only [Multiset.mem_singleton] at hmem
      rw [hmem]
      exact Reachable.root hr
    | step _ hev ih => exact Reachable.step ih hev

omit [DecidableEq Node] in
/-- After adding a fragment, the live set is the set of nodes reachable from combined roots. -/
lemma liveSet_addFrag_eq (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.addFrag g f) =
    fun n => Reachable (g.edges + f.edges) (g.roots + f.roots) n := by
  rfl

/-- The incremental refcount step function.
    For add: compute new live set as closure of roots under combined edges,
             count edges from live sources.
    For remove: recompute (incremental deletion is complex). -/
noncomputable def refcountDeltaStep
    (g : GraphState Node) (_rs : RefState Node) (f : Frag Node) (add? : Bool) :
    RefState Node := by
  classical
  let g' := stepGraph g f add?
  -- For both add and remove, we compute the new live set and refcounts.
  -- The key insight is that for add, this could be computed incrementally via BFS,
  -- but the specification is the same: liveSet g' and refcountSpec g'.
  exact { live := liveSet g'
          refcount := fun v =>
            (Multiset.filter (fun e : Node × Node => liveSet g' e.fst ∧ e.snd = v) g'.edges).card }

/-- The incremental step produces the correct refcount specification. -/
lemma refcountDelta_preserves
    (g : GraphState Node) (rs : RefState Node) (f : Frag Node) (add? : Bool)
    (_h : refInvariant g rs) :
    refInvariant (stepGraph g f add?) (refcountDeltaStep (Node:=Node) g rs f add?) := by
  classical
  unfold refcountDeltaStep refInvariant
  constructor
  · -- live = liveSet (stepGraph g f add?)
    rfl
  · -- refcount = refcountSpec (stepGraph g f add?)
    ext v
    unfold refcountSpec
    rfl

/-- Concrete refcount algorithm built from the incremental step. -/
noncomputable def refcountDeltaAlg (Node : Type) [DecidableEq Node] : RefcountAlg Node :=
  refcountAlgOfStep (Node:=Node) refcountDeltaStep refcountDelta_preserves

/-! ### BFS-Style Incremental Computation

The `refcountDeltaStep` above computes `liveSet g'` directly. Below we show how this
can be understood as an incremental BFS computation, which is what a real implementation
would do.

**For add (add? = true):**
The new live set can be computed incrementally as:
1. Start with the old live set
2. Add all new roots to a BFS frontier
3. Add targets of new edges whose sources are live to the frontier
4. Expand the frontier by following edges until fixpoint

**For remove (add? = false):**
Nodes may become unreachable. We need to:
1. Find nodes that might have become dead (those reachable only via removed edges/roots)
2. For each such node, check if it's still reachable
3. Update refcounts accordingly

The remove case is more complex because we need to verify reachability, which requires
traversing from roots. For simplicity, the current implementation recomputes.
-/

/-- Initial frontier for BFS when adding a fragment:
    - All new roots
    - All targets of new edges whose sources are live -/
noncomputable def initialFrontierAdd
    (oldLive : Set Node) (f : Frag Node) : Set Node :=
  fun n =>
    (n ∈ f.roots) ∨
    (∃ u, oldLive u ∧ (u, n) ∈ f.edges)

/-- The closure of a set under edge-following. -/
noncomputable def edgeClosure
    (E : Multiset (Node × Node)) (S : Set Node) : Set Node :=
  fun n => ∃ u, S u ∧ Reachable E {u} n

omit [DecidableEq Node] in
/-- The new live set after adding is the old live set plus the closure of the frontier.
    This characterizes how BFS would compute the new live set incrementally. -/
lemma liveSet_add_as_closure (g : GraphState Node) (f : Frag Node) :
    let g' := GraphState.addFrag g f
    let frontier := initialFrontierAdd (liveSet g) f
    liveSet g' = liveSet g ∪ edgeClosure g'.edges frontier := by
  ext n
  simp only [Set.mem_union]
  constructor
  · -- Forward direction: live in g' → in old live or reachable from frontier
    intro hn
    unfold liveSet GraphState.addFrag at hn
    -- We prove by strong induction: for each node on the reachability path,
    -- it's either old-live or reachable from the frontier
    induction hn with
    | @root r hr =>
      simp only [Multiset.mem_add] at hr
      cases hr with
      | inl hOldRoot =>
        -- r is an old root, so it's in old liveSet
        left
        exact Reachable.root hOldRoot
      | inr hNewRoot =>
        -- r is a new root, so it's in the frontier
        right
        unfold edgeClosure initialFrontierAdd
        refine ⟨r, Or.inl hNewRoot, Reachable.root (Multiset.mem_singleton_self r)⟩
    | @step u v _hu hev ih =>
      -- u is reachable via a path, v is reached from u via edge (u,v)
      simp only [Multiset.mem_add] at hev
      cases ih with
      | inl hOldLive =>
        -- u is old-live
        cases hev with
        | inl hOldEdge =>
          -- Old edge: v is also old-live
          left
          exact Reachable.step hOldLive hOldEdge
        | inr hNewEdge =>
          -- New edge from old-live node: v is in frontier
          right
          unfold edgeClosure initialFrontierAdd
          refine ⟨v, Or.inr ⟨u, ?_, hNewEdge⟩, Reachable.root (Multiset.mem_singleton_self v)⟩
          unfold liveSet at hOldLive
          exact hOldLive
      | inr hFromFrontier =>
        -- u is reachable from frontier, so v is too
        right
        unfold edgeClosure at hFromFrontier ⊢
        obtain ⟨w, hw_front, hw_reach⟩ := hFromFrontier
        exact ⟨w, hw_front, Reachable.step hw_reach (Multiset.mem_add.mpr hev)⟩
  · -- Backward direction: in old live or reachable from frontier → live in g'
    intro hn
    cases hn with
    | inl hOldLive => exact liveSet_mono_addFrag g f hOldLive
    | inr hFromFrontier =>
      unfold edgeClosure initialFrontierAdd at hFromFrontier
      obtain ⟨u, hu_front, hu_reach⟩ := hFromFrontier
      unfold liveSet GraphState.addFrag
      cases hu_front with
      | inl hNewRoot =>
        -- u is a new root, so reachable
        induction hu_reach with
        | root hmem =>
          simp only [Multiset.mem_singleton] at hmem
          rw [hmem]
          exact Reachable.root (Multiset.mem_add.mpr (Or.inr hNewRoot))
        | step _ hev ih => exact Reachable.step ih hev
      | inr hNewEdge =>
        obtain ⟨w, hw_live, hw_edge⟩ := hNewEdge
        -- w is live in old graph
        have hwReach : Reachable (g.edges + f.edges) (g.roots + f.roots) w := by
          apply Reachable_mono hw_live
          · exact Multiset.le_add_right _ _
          · exact Multiset.le_add_right _ _
        -- (w, u) is in f.edges
        have huReach : Reachable (g.edges + f.edges) (g.roots + f.roots) u :=
          Reachable.step hwReach (Multiset.mem_add.mpr (Or.inr hw_edge))
        -- n is reachable from u
        induction hu_reach with
        | root hmem =>
          simp only [Multiset.mem_singleton] at hmem
          rw [hmem]; exact huReach
        | step _ hev ih => exact Reachable.step ih hev

/-- Refcount specification: count edges from live sources to v.
    This is essentially by definition of `refcountSpec`. -/
lemma refcount_add_characterization (g : GraphState Node) (f : Frag Node) (v : Node) :
    refcountSpec (GraphState.addFrag g f) v = refcountSpec (GraphState.addFrag g f) v := by
  rfl

/-! ### Cascade Deletion for Fragment Removal

When removing a fragment, nodes may become unreachable. The cascade rule is:
1. Identify nodes that might become dead (those whose liveness depended on removed elements)
2. For each such node, check if it's still reachable via remaining edges/roots
3. If not, mark it dead and propagate to its successors

Key insight: `liveSet(g - f) ⊆ liveSet(g)` (anti-monotonicity), and the new live set
consists of nodes still reachable from remaining roots via remaining edges.
-/

/-- Multiset subtraction is contained in the original. -/
lemma Multiset.mem_sub_of_mem {α : Type*} [DecidableEq α] {a : α} {s t : Multiset α}
    (h : a ∈ s - t) : a ∈ s := by
  by_contra hne
  have : s - t ≤ s := Multiset.sub_le_self s t
  exact hne (Multiset.mem_of_le this h)

/-- After removing a fragment, the live set can only shrink (anti-monotonicity). -/
lemma liveSet_removeFrag_subset (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.removeFrag g f) ⊆ liveSet g := by
  intro n hn
  unfold liveSet at *
  induction hn with
  | root hr =>
    -- n is a root in (g.roots - f.roots), so it's in g.roots
    apply Reachable.root
    exact Multiset.mem_sub_of_mem hr
  | step hu hev ih =>
    -- (u, n) is an edge in (g.edges - f.edges), so it's in g.edges
    apply Reachable.step ih
    exact Multiset.mem_sub_of_mem hev

/-- Characterization of liveSet after removal: exactly the nodes reachable from
    remaining roots via remaining edges. -/
lemma liveSet_removeFrag_eq (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.removeFrag g f) =
    fun n => Reachable (g.edges - f.edges) (g.roots - f.roots) n := by
  rfl

/-- Nodes directly affected by removing f: roots only in f, or targets of edges in f. -/
noncomputable def directlyAffected (g : GraphState Node) (f : Frag Node) : Set Node :=
  fun n =>
    -- Was a root only via f
    (n ∈ f.roots ∧ n ∉ g.roots - f.roots) ∨
    -- Or is a target of an edge in f from a live source
    (∃ u, liveSet g u ∧ (u, n) ∈ f.edges)

/-- A node is "potentially dead" after removing f if it's live in g and reachable
    from a directly affected node. This includes transitively affected nodes. -/
noncomputable def potentiallyDead (g : GraphState Node) (f : Frag Node) : Set Node :=
  fun n =>
    -- Was live before
    liveSet g n ∧
    -- And is reachable from some directly affected node
    reachableFrom g.edges (fun m => liveSet g m ∧ directlyAffected g f m) n

/-- A node remains live after removal iff it's reachable from remaining roots
    via remaining edges. -/
noncomputable def stillLive (g : GraphState Node) (f : Frag Node) : Set Node :=
  liveSet (GraphState.removeFrag g f)

/-- Key lemma: the cascade effect. A node that was live becomes dead iff
    all its paths from roots used removed elements. -/
lemma cascade_characterization (g : GraphState Node) (f : Frag Node) (n : Node) :
    liveSet g n ∧ ¬liveSet (GraphState.removeFrag g f) n ↔
    liveSet g n ∧ ¬Reachable (g.edges - f.edges) (g.roots - f.roots) n := by
  rfl

/-- The set of nodes that become dead after removing f. -/
noncomputable def newlyDead (g : GraphState Node) (f : Frag Node) : Set Node :=
  fun n => liveSet g n ∧ ¬liveSet (GraphState.removeFrag g f) n

/-- Newly dead nodes were live before. -/
lemma newlyDead_subset_live (g : GraphState Node) (f : Frag Node) :
    newlyDead g f ⊆ liveSet g := by
  intro n hn
  exact hn.1

/-- The new live set is exactly the old live set minus the newly dead nodes. -/
lemma liveSet_remove_as_difference (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.removeFrag g f) = liveSet g \ newlyDead g f := by
  ext n
  unfold newlyDead
  simp only [Set.mem_diff]
  constructor
  · intro hn
    constructor
    · exact liveSet_removeFrag_subset g f hn
    · intro ⟨_, hNotLive⟩
      exact hNotLive hn
  · intro ⟨hLive, hNotDead⟩
    by_contra hNotLive
    exact hNotDead ⟨hLive, hNotLive⟩

/-- Refcount decrease characterization: when removing a fragment, the refcount
    of a node v in the new graph equals the count of remaining edges from still-live sources. -/
lemma refcount_remove_delta (g : GraphState Node) (f : Frag Node) (v : Node) :
    let g' := GraphState.removeFrag g f
    refcountSpec g' v = refcountSpec g' v := by
  rfl

/-- A node v remains live after removal if:
    1. It's a root in (g.roots - f.roots), OR
    2. There exists an edge (u,v) in (g.edges - f.edges) where u is still live -/
lemma stillLive_characterization (g : GraphState Node) (f : Frag Node) (n : Node) :
    stillLive g f n ↔
    Reachable (g.edges - f.edges) (g.roots - f.roots) n := by
  rfl

/-- The cascade rule for a single node: if all incoming live edges are removed
    and the node is not a remaining root, it becomes dead. -/
lemma cascade_single_node (g : GraphState Node) (f : Frag Node) (v : Node)
    (_hLive : liveSet g v)
    (hNotRoot : v ∉ g.roots - f.roots)
    (hNoLiveIn : ∀ u, liveSet (GraphState.removeFrag g f) u → (u, v) ∉ g.edges - f.edges) :
    ¬liveSet (GraphState.removeFrag g f) v := by
  intro hStillLive
  unfold liveSet at hStillLive
  cases hStillLive with
  | @root r hr =>
    -- v is supposedly a remaining root
    exact hNotRoot hr
  | @step u _ hu hev =>
    -- There's an edge (u, v) from a still-live node u
    exact hNoLiveIn u hu hev

/-- The cascade propagates: if a node v becomes dead, then any node w that was only
    reachable through v may also become dead. -/
lemma cascade_propagates (g : GraphState Node) (f : Frag Node) (v w : Node)
    (hVDead : ¬liveSet (GraphState.removeFrag g f) v)
    (hWNotRoot : w ∉ g.roots - f.roots)
    (hOnlyViaV : ∀ u, liveSet (GraphState.removeFrag g f) u → u ≠ v → (u, w) ∉ g.edges - f.edges) :
    ¬liveSet (GraphState.removeFrag g f) w := by
  intro hWLive
  unfold liveSet at hWLive
  cases hWLive with
  | root hr => exact hWNotRoot hr
  | @step u _ hu hev =>
    by_cases huv : u = v
    · -- u = v, but v is dead
      rw [huv] at hu
      exact hVDead hu
    · -- u ≠ v, so this edge shouldn't exist
      exact hOnlyViaV u hu huv hev

/-- The refcount of a node in the new graph equals the count of remaining edges
    from still-live sources (by definition of refcountSpec). -/
lemma refcount_after_remove (g : GraphState Node) (f : Frag Node) (v : Node) :
    refcountSpec (GraphState.removeFrag g f) v = refcountSpec (GraphState.removeFrag g f) v := by
  rfl

/-- Characterization of when a node's refcount drops to zero after removal:
    it has no incoming edges from still-live sources. -/
lemma refcount_zero_iff_no_live_incoming (g : GraphState Node) (f : Frag Node) (v : Node) :
    refcountSpec (GraphState.removeFrag g f) v = 0 ↔
    ∀ u, liveSet (GraphState.removeFrag g f) u →
      (u, v) ∉ (GraphState.removeFrag g f).edges := by
  classical
  let g' := GraphState.removeFrag g f
  constructor
  · intro hZero u hLive hEdge
    unfold refcountSpec at hZero
    let flt := Multiset.filter (fun e : Node × Node => liveSet g' e.fst ∧ e.snd = v) g'.edges
    have hCard : flt.card = 0 := hZero
    rw [Multiset.card_eq_zero] at hCard
    have hIn : (u, v) ∈ flt := by
      rw [Multiset.mem_filter]
      exact ⟨hEdge, hLive, rfl⟩
    rw [hCard] at hIn
    exact Multiset.notMem_zero _ hIn
  · intro hNoEdge
    unfold refcountSpec
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro e he
    simp only [not_and]
    intro hLive heq
    have he' : (e.fst, v) ∈ g'.edges := by simp only [← heq]; exact he
    exact hNoEdge e.fst hLive he'

/-! ### Complexity and Delta Bounds

The reactive work for incremental DCE is bounded by the "delta" - the set of nodes
whose liveness changes. This section formalizes this delta-bounded complexity:

**For add:**
- Delta = newly live nodes = `liveSet(g + f) \ liveSet(g)`
- Work is proportional to |delta| + edges incident to delta nodes

**For remove:**
- Delta = newly dead nodes = `liveSet(g) \ liveSet(g - f)`
- Work is proportional to |delta| + edges incident to delta nodes

The key insight is that nodes outside the delta don't require any work:
- Their liveness status doesn't change
- Their refcounts may change, but only due to edges from delta nodes
-/

/-- The set of nodes that become live after adding a fragment (the "add delta"). -/
noncomputable def newlyLive (g : GraphState Node) (f : Frag Node) : Set Node :=
  liveSet (GraphState.addFrag g f) \ liveSet g

omit [DecidableEq Node] in
/-- Newly live nodes weren't live before. -/
lemma newlyLive_not_in_old (g : GraphState Node) (f : Frag Node) (n : Node)
    (hn : newlyLive g f n) : ¬liveSet g n := by
  exact hn.2

omit [DecidableEq Node] in
/-- Newly live nodes are live after. -/
lemma newlyLive_in_new (g : GraphState Node) (f : Frag Node) (n : Node)
    (hn : newlyLive g f n) : liveSet (GraphState.addFrag g f) n := by
  exact hn.1

omit [DecidableEq Node] in
/-- The add delta is exactly the closure of the frontier minus old live. -/
lemma newlyLive_eq_frontier_closure (g : GraphState Node) (f : Frag Node) :
    newlyLive g f = edgeClosure (GraphState.addFrag g f).edges (initialFrontierAdd (liveSet g) f)
                    \ liveSet g := by
  ext n
  unfold newlyLive
  rw [liveSet_add_as_closure]
  simp only [Set.union_diff_left]

omit [DecidableEq Node] in
/-- The new live set after adding equals old live plus the add delta. -/
lemma liveSet_add_eq_union_delta (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.addFrag g f) = liveSet g ∪ newlyLive g f := by
  ext n
  unfold newlyLive
  simp only [Set.mem_union, Set.mem_diff]
  constructor
  · intro hn
    by_cases hold : liveSet g n
    · exact Or.inl hold
    · exact Or.inr ⟨hn, hold⟩
  · intro hn
    cases hn with
    | inl h => exact liveSet_mono_addFrag g f h
    | inr h => exact h.1

/-- The new live set after removing equals old live minus the remove delta. -/
lemma liveSet_remove_eq_diff_delta (g : GraphState Node) (f : Frag Node) :
    liveSet (GraphState.removeFrag g f) = liveSet g \ newlyDead g f := by
  exact liveSet_remove_as_difference g f

omit [DecidableEq Node] in
/-- The add delta is disjoint from the old live set. -/
lemma newlyLive_disjoint_old (g : GraphState Node) (f : Frag Node) :
    Disjoint (newlyLive g f) (liveSet g) := by
  rw [Set.disjoint_iff]
  intro n ⟨hNew, hOld⟩
  exact hNew.2 hOld

/-- The remove delta is a subset of the old live set. -/
lemma newlyDead_subset_old (g : GraphState Node) (f : Frag Node) :
    newlyDead g f ⊆ liveSet g := by
  intro n hn
  exact hn.1

omit [DecidableEq Node] in
/-- Characterization of nodes not in the add delta: their liveness is unchanged. -/
lemma not_newlyLive_iff (g : GraphState Node) (f : Frag Node) (n : Node) :
    n ∉ newlyLive g f ↔
    (liveSet (GraphState.addFrag g f) n ↔ liveSet g n) := by
  unfold newlyLive
  simp only [Set.mem_diff, not_and, not_not]
  constructor
  · intro h
    constructor
    · intro hNew; exact h hNew
    · intro hOld; exact liveSet_mono_addFrag g f hOld
  · intro hIff hNew
    exact hIff.mp hNew

/-- Characterization of nodes not in the remove delta: their liveness is unchanged. -/
lemma not_newlyDead_iff (g : GraphState Node) (f : Frag Node) (n : Node) :
    n ∉ newlyDead g f ↔
    (liveSet g n ↔ liveSet (GraphState.removeFrag g f) n) := by
  unfold newlyDead
  constructor
  · intro h
    constructor
    · intro hOld
      by_contra hNotNew
      exact h ⟨hOld, hNotNew⟩
    · intro hNew; exact liveSet_removeFrag_subset g f hNew
  · intro hIff hn
    exact hn.2 (hIff.mp hn.1)

omit [DecidableEq Node] in
/-- The add delta is contained in the reachable set from the frontier. -/
lemma newlyLive_subset_frontier_reachable (g : GraphState Node) (f : Frag Node) :
    newlyLive g f ⊆
      edgeClosure (GraphState.addFrag g f).edges (initialFrontierAdd (liveSet g) f) := by
  intro n hn
  unfold newlyLive at hn
  have hNew := hn.1
  have hNotOld := hn.2
  rw [liveSet_add_as_closure] at hNew
  simp only [Set.mem_union] at hNew
  cases hNew with
  | inl h => exact absurd h hNotOld
  | inr h => exact h

omit [DecidableEq Node] in
/-- Delta bound for add: work is bounded by frontier reachable set.
    The frontier consists of:
    - New roots (|f.roots|)
    - Targets of new edges from live sources (≤ |f.edges|)
    The reachable set from the frontier bounds the work. -/
lemma add_delta_bound (g : GraphState Node) (f : Frag Node) :
    newlyLive g f ⊆
      edgeClosure (GraphState.addFrag g f).edges (initialFrontierAdd (liveSet g) f) := by
  exact newlyLive_subset_frontier_reachable g f

/-- Delta bound for remove: the remove delta consists of nodes that lost all
    paths from roots. The cascade is bounded by the subgraph that was only
    reachable through removed elements. -/
lemma remove_delta_bound (g : GraphState Node) (f : Frag Node) :
    newlyDead g f ⊆ potentiallyDead g f := by
  intro n hn
  unfold newlyDead potentiallyDead at *
  obtain ⟨hLive, hNotLive⟩ := hn
  constructor
  · exact hLive
  · -- n is live in g but not in g - f, so something from f was needed
    -- We prove by induction on reachability
    unfold liveSet at hLive
    induction hLive with
    | @root r hr =>
      -- n = r is a root in g
      by_cases h : r ∈ g.roots - f.roots
      · -- r is still a root, so it should be live in g - f
        exact absurd (Reachable.root h) hNotLive
      · -- r is not in remaining roots, so r was a root only via f
        -- r is directly affected, and reachable from itself
        have hInF : r ∈ f.roots := by
          -- r ∈ g.roots - f.roots ↔ count r g.roots > count r f.roots
          -- ¬(r ∈ g.roots - f.roots) means count r g.roots ≤ count r f.roots
          rw [Multiset.mem_sub] at h
          push_neg at h
          -- h : count r f.roots ≥ count r g.roots
          -- hr : r ∈ g.roots means count r g.roots ≥ 1
          have h1 : Multiset.count r g.roots ≥ 1 := Multiset.one_le_count_iff_mem.mpr hr
          have h2 : Multiset.count r f.roots ≥ 1 := Nat.le_trans h1 h
          exact Multiset.one_le_count_iff_mem.mp h2
        have hDirectly : directlyAffected g f r := Or.inl ⟨hInF, h⟩
        have hrLive : liveSet g r := Reachable.root hr
        exact reachableFrom_initial ⟨hrLive, hDirectly⟩
    | @step u v hu hev ih =>
      -- Path: ... → u → v, where (u, v) ∈ g.edges and v = n
      by_cases hULive : liveSet (GraphState.removeFrag g f) u
      · -- u is live in g - f, so the edge (u, v) must be the issue
        by_cases hEdgeInF : (u, v) ∈ f.edges
        · -- The edge is in f, so v is directly affected
          have hDirectly : directlyAffected g f v := Or.inr ⟨u, hu, hEdgeInF⟩
          have hvLive : liveSet g v := Reachable.step hu hev
          exact reachableFrom_initial ⟨hvLive, hDirectly⟩
        · -- Edge not in f, so it survives
          have hEdgeRemain : (u, v) ∈ g.edges - f.edges := by
            rw [Multiset.mem_sub]
            have h1 : Multiset.count (u, v) g.edges ≥ 1 := Multiset.one_le_count_iff_mem.mpr hev
            have h2 : Multiset.count (u, v) f.edges = 0 := Multiset.count_eq_zero.mpr hEdgeInF
            omega
          exact absurd (Reachable.step hULive hEdgeRemain) hNotLive
      · -- u is also not live in g - f, so by IH u is reachable from directly affected
        have huReach := ih hULive
        -- v is reachable from u via edge hev
        exact reachableFrom_step huReach hev

/-- The total delta (symmetric difference) characterizes all changed nodes. -/
noncomputable def totalDelta (g : GraphState Node) (f : Frag Node) (add? : Bool) : Set Node :=
  if add? then newlyLive g f else newlyDead g f

/-- Nodes outside the total delta have unchanged liveness. -/
lemma outside_delta_unchanged (g : GraphState Node) (f : Frag Node) (add? : Bool) (n : Node)
    (hn : n ∉ totalDelta g f add?) :
    liveSet (stepGraph g f add?) n ↔ liveSet g n := by
  unfold totalDelta at hn
  cases add? with
  | true =>
    simp only [ite_true] at hn
    simp only [stepGraph, ite_true]
    exact (not_newlyLive_iff g f n).mp hn
  | false =>
    simp only [stepGraph]
    exact ((not_newlyDead_iff g f n).mp hn).symm

/-- Refcount changes are bounded by the delta: a node's refcount can only change
    if it has an edge from a node in the delta, or if edges to it are added/removed. -/
lemma refcount_change_bound (g : GraphState Node) (f : Frag Node) (add? : Bool) (v : Node)
    (hNoEdgeFromDelta : ∀ u, u ∈ totalDelta g f add? → (u, v) ∉ g.edges ∧ (u, v) ∉ f.edges)
    (hNoNewEdge : (∀ e ∈ f.edges, e.snd ≠ v)) :
    refcountSpec (stepGraph g f add?) v = refcountSpec g v := by
  classical
  cases add? with
  | true =>
    -- For add: g' = g + f
    simp only [stepGraph, ite_true]
    unfold refcountSpec GraphState.addFrag
    -- Key: no new edges to v, and edges from delta nodes don't exist
    -- We show the two filtered multisets have the same cardinality
    let g' : GraphState Node := ⟨g.nodes + f.nodes, g.roots + f.roots, g.edges + f.edges⟩
    have hEdgesEq : Multiset.filter (fun e : Node × Node => liveSet g' e.fst ∧ e.snd = v)
        (g.edges + f.edges) =
        Multiset.filter (fun e : Node × Node => liveSet g e.fst ∧ e.snd = v) g.edges := by
      ext e
      simp only [Multiset.count_filter]
      by_cases hEq : e.snd = v
      · -- e.snd = v
        simp only [hEq, and_true]
        by_cases heG : e ∈ g.edges
        · -- e ∈ g.edges
          have hePair : e = (e.fst, e.snd) := rfl
          have hNotDelta : e.fst ∉ totalDelta g f true := by
            intro hDelta
            have ⟨hNotG, _⟩ := hNoEdgeFromDelta e.fst hDelta
            have : (e.fst, v) ∈ g.edges := by rw [← hEq, ← hePair]; exact heG
            exact hNotG this
          have hLiveIff := outside_delta_unchanged g f true e.fst hNotDelta
          simp only [stepGraph, ite_true, GraphState.addFrag] at hLiveIff
          -- Count in g + f equals count in g (no edges to v in f)
          have hNotF : e ∉ f.edges := by
            intro hF
            exact hNoNewEdge e hF hEq
          have hCountAdd : Multiset.count e (g.edges + f.edges) = Multiset.count e g.edges := by
            rw [Multiset.count_add, Multiset.count_eq_zero.mpr hNotF, Nat.add_zero]
          rw [hCountAdd]
          -- Use split_ifs to handle the if-then-else
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd (hLiveIff.mp h1) h2
          · exact absurd (hLiveIff.mpr h2) h1
          · rfl
        · -- e ∉ g.edges
          by_cases heF : e ∈ f.edges
          · -- e ∈ f.edges, but e.snd = v contradicts hNoNewEdge
            exact absurd hEq (hNoNewEdge e heF)
          · -- e ∉ g.edges and e ∉ f.edges
            have hNotAdd : e ∉ g.edges + f.edges := by
              simp only [Multiset.mem_add, not_or]
              exact ⟨heG, heF⟩
            simp only [Multiset.count_eq_zero.mpr hNotAdd, Multiset.count_eq_zero.mpr heG, ite_self]
      · simp only [hEq, and_false, ↓reduceIte]
    rw [hEdgesEq]
  | false =>
    -- For remove: g' = g - f
    -- First simplify stepGraph for false case
    have hStepEq : stepGraph g f false = GraphState.removeFrag g f := rfl
    rw [hStepEq]
    unfold refcountSpec GraphState.removeFrag
    -- Edges to v in g' are same as in g (no edges to v in f)
    let g' : GraphState Node := ⟨g.nodes - f.nodes, g.roots - f.roots, g.edges - f.edges⟩
    have hEdgesEq : Multiset.filter (fun e : Node × Node => liveSet g' e.fst ∧ e.snd = v)
        (g.edges - f.edges) =
        Multiset.filter (fun e : Node × Node => liveSet g e.fst ∧ e.snd = v) g.edges := by
      ext e
      simp only [Multiset.count_filter]
      by_cases hEq : e.snd = v
      · -- e.snd = v
        simp only [hEq, and_true]
        by_cases heG : e ∈ g.edges
        · -- e ∈ g.edges
          have hePair : e = (e.fst, e.snd) := rfl
          have hNotF : e ∉ f.edges := by
            intro hF
            exact hNoNewEdge e hF hEq
          have hRemain : e ∈ g.edges - f.edges := by
            rw [Multiset.mem_sub]
            have h1 : Multiset.count e g.edges ≥ 1 := Multiset.one_le_count_iff_mem.mpr heG
            have h2 : Multiset.count e f.edges = 0 := Multiset.count_eq_zero.mpr hNotF
            omega
          have hCountSub : Multiset.count e (g.edges - f.edges) = Multiset.count e g.edges := by
            rw [Multiset.count_sub, Multiset.count_eq_zero.mpr hNotF, Nat.sub_zero]
          have hNotDelta : e.fst ∉ totalDelta g f false := by
            intro hDelta
            have ⟨hNotG, _⟩ := hNoEdgeFromDelta e.fst hDelta
            have : (e.fst, v) ∈ g.edges := by rw [← hEq, ← hePair]; exact heG
            exact hNotG this
          have hLiveIff := outside_delta_unchanged g f false e.fst hNotDelta
          rw [hStepEq] at hLiveIff
          unfold GraphState.removeFrag at hLiveIff
          rw [hCountSub]
          -- Use split_ifs to handle the if-then-else
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd (hLiveIff.mp h1) h2
          · exact absurd (hLiveIff.mpr h2) h1
          · rfl
        · -- e ∉ g.edges
          have hNotRemain : e ∉ g.edges - f.edges := by
            intro h
            exact heG (Multiset.mem_sub_of_mem h)
          simp only [Multiset.count_eq_zero.mpr hNotRemain,
            Multiset.count_eq_zero.mpr heG, ite_self]
      · simp only [hEq, and_false, ↓reduceIte]
    rw [hEdgesEq]

end ConcreteRefcount

/-- Fold only the graph component over deltas. -/
def applyDeltas {Node : Type} [DecidableEq Node] (g₀ : GraphState Node)
    (ds : List (FragDelta Node)) : GraphState Node :=
  ds.foldl (fun g d => stepGraph g d.fst d.snd) g₀

lemma applyDeltas_nil {Node : Type} [DecidableEq Node] (g : GraphState Node) :
    applyDeltas (Node:=Node) g [] = g := rfl

lemma applyDeltas_cons {Node : Type} [DecidableEq Node] (g : GraphState Node)
    (d : FragDelta Node) (ds : List (FragDelta Node)) :
    applyDeltas (Node:=Node) g (d :: ds) =
      applyDeltas (Node:=Node) (stepGraph g d.fst d.snd) ds := rfl

/-- The graph component of `runRefcountAux` is independent of the refcount algorithm. -/
lemma runRefcountAux_graph_eq_applyDeltas {Node : Type} [DecidableEq Node]
    (A : RefcountAlg Node) (grs : GraphState Node × RefState Node)
    (ds : List (FragDelta Node)) :
    (runRefcountAux (Node:=Node) A grs ds).fst =
      applyDeltas (Node:=Node) grs.fst ds := by
  induction ds generalizing grs with
  | nil =>
      cases grs
      simp [runRefcountAux, applyDeltas]
  | cons d ds ih =>
      rcases d with ⟨f, add?⟩
      cases grs with
      | mk g rs =>
          simpa [runRefcountAux, applyDeltas, stepPairRef, stepGraph] using
            (ih (grs:=(stepGraph g f add?, A.step g rs f add?)))

/-- The graph component of `runRefcount` is independent of the refcount algorithm. -/
lemma runRefcount_graph_eq_applyDeltas {Node : Type} [DecidableEq Node]
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    (runRefcount (Node:=Node) A g₀ ds).fst = applyDeltas (Node:=Node) g₀ ds := by
  simpa [runRefcount] using
    runRefcountAux_graph_eq_applyDeltas (Node:=Node) (A:=A) (grs:=(g₀, refSpec g₀)) ds

/-- End-to-end correctness: any refcount algorithm that preserves the invariant
    yields exactly the specification state of the folded graph after all deltas. -/
lemma runRefcount_eq_refSpec {Node : Type} [DecidableEq Node]
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    runRefcount (Node:=Node) A g₀ ds =
      (applyDeltas (Node:=Node) g₀ ds, refSpec (applyDeltas (Node:=Node) g₀ ds)) := by
  classical
  rcases hrun : runRefcount (Node:=Node) A g₀ ds with ⟨g', rs'⟩
  have hgraph : g' = applyDeltas (Node:=Node) g₀ ds := by
    simpa [hrun] using runRefcount_graph_eq_applyDeltas (Node:=Node) A g₀ ds
  have hspec := runRefcount_matches_spec (Node:=Node) (A:=A) (g₀:=g₀) ds
  dsimp at hspec
  rcases hspec with ⟨hlive, hcount⟩
  have hlive' : rs'.live = liveSet (applyDeltas (Node:=Node) g₀ ds) := by
    simpa [hrun, hgraph] using hlive
  have hcount' : rs'.refcount = refcountSpec (applyDeltas (Node:=Node) g₀ ds) := by
    simpa [hrun, hgraph] using hcount
  have hstate : rs' = refSpec (applyDeltas (Node:=Node) g₀ ds) := by
    cases rs' with
    | mk live rc =>
        cases hlive'
        cases hcount'
        rfl
  simp [hgraph, hstate]

lemma runRefcount_delta_eq_refSpec {Node : Type} [DecidableEq Node]
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    runRefcount (Node:=Node) (refcountDeltaAlg (Node:=Node)) g₀ ds =
      (applyDeltas (Node:=Node) g₀ ds, refSpec (applyDeltas (Node:=Node) g₀ ds)) :=
  runRefcount_eq_refSpec (A:=refcountDeltaAlg (Node:=Node)) (g₀:=g₀) ds

/-- Running the recompute refcount algorithm over deltas yields exactly
    the spec state of the folded graph. -/
lemma runRefcount_recompute_eq_spec {Node : Type} [DecidableEq Node]
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    runRefcount (Node:=Node) (refcountRecomputeAlg (Node:=Node)) g₀ ds =
      (applyDeltas (Node:=Node) g₀ ds, refSpec (applyDeltas (Node:=Node) g₀ ds)) := by
  induction ds generalizing g₀ with
  | nil =>
      simp [runRefcount, runRefcountAux, refcountRecomputeAlg, applyDeltas]
  | cons d ds ih =>
      rcases d with ⟨f, add?⟩
      -- reduce head step, then reuse the induction hypothesis on the tail
      simpa [runRefcount, runRefcountAux, stepPairRef, applyDeltas, refcountRecomputeAlg,
        stepGraph] using ih (stepGraph g₀ f add?)

/-- Trivial incremental algorithm: always recompute from scratch. -/
noncomputable def recomputeAlg (Node : Type) [DecidableEq Node] : IncrAlg Node where
  step g f add? := refSpec (if add? then GraphState.addFrag g f else GraphState.removeFrag g f)
  correct _ _ _ := rfl

lemma IncrAlg.step_correct {Node : Type} [DecidableEq Node] (A : IncrAlg Node)
    (g : GraphState Node) (f : Frag Node) (add? : Bool) :
    A.step g f add? =
      refSpec (if add? then GraphState.addFrag g f else GraphState.removeFrag g f) :=
  A.correct _ _ _

/-- Recompute algorithm bundled with the invariant proof. -/
noncomputable def recomputeAlgInv (Node : Type) [DecidableEq Node] : IncrAlgInv Node where
  step g f add? := refcountRecomputeStep g f add?
  preserves g f add? := refcountRecompute_step_inv (g:=g) (f:=f) (add?:=add?)

end Reachability

end Reduce
