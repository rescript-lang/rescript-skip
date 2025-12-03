import Reduce
import Mathlib.Data.Multiset.AddSub

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

end Reduce

