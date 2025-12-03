/-
  Layer2/Spec.lean
  Basic definitions and specifications for incremental DCE.
  Contains: Reachable, liveSet, deadSet, RefState, refcountSpec, refInvariant.
-/
import Reduce
import DCE.Layer1
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter

open Multiset
open Reduce

namespace Reduce

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

end Reachability

end Reduce



