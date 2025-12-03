/-
  Layer2/Bounds.lean
  Delta bounds and end-to-end correctness theorems.
  Contains: newlyLive, delta bounds, totalDelta, refcount_change_bound,
  applyDeltas, runRefcount_eq_refSpec, and related lemmas.
-/
import DCE.Layer2.Characterization

open Multiset
open Reduce

namespace Reduce

section Bounds
variable {Node : Type} [DecidableEq Node]

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

/-- Fold only the graph component over deltas. -/
def applyDeltas (g₀ : GraphState Node)
    (ds : List (FragDelta Node)) : GraphState Node :=
  ds.foldl (fun g d => stepGraph g d.fst d.snd) g₀

lemma applyDeltas_nil (g : GraphState Node) :
    applyDeltas (Node:=Node) g [] = g := rfl

lemma applyDeltas_cons (g : GraphState Node)
    (d : FragDelta Node) (ds : List (FragDelta Node)) :
    applyDeltas (Node:=Node) g (d :: ds) =
      applyDeltas (Node:=Node) (stepGraph g d.fst d.snd) ds := rfl

/-- The graph component of `runRefcountAux` is independent of the refcount algorithm. -/
lemma runRefcountAux_graph_eq_applyDeltas
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
lemma runRefcount_graph_eq_applyDeltas
    (A : RefcountAlg Node) (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    (runRefcount (Node:=Node) A g₀ ds).fst = applyDeltas (Node:=Node) g₀ ds := by
  simpa [runRefcount] using
    runRefcountAux_graph_eq_applyDeltas (Node:=Node) (A:=A) (grs:=(g₀, refSpec g₀)) ds

/-- End-to-end correctness: any refcount algorithm that preserves the invariant
    yields exactly the specification state of the folded graph after all deltas. -/
lemma runRefcount_eq_refSpec
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

lemma runRefcount_delta_eq_refSpec
    (g₀ : GraphState Node) (ds : List (FragDelta Node)) :
    runRefcount (Node:=Node) (refcountDeltaAlg (Node:=Node)) g₀ ds =
      (applyDeltas (Node:=Node) g₀ ds, refSpec (applyDeltas (Node:=Node) g₀ ds)) :=
  runRefcount_eq_refSpec (A:=refcountDeltaAlg (Node:=Node)) (g₀:=g₀) ds

/-- Running the recompute refcount algorithm over deltas yields exactly
    the spec state of the folded graph. -/
lemma runRefcount_recompute_eq_spec
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

lemma IncrAlg.step_correct (A : IncrAlg Node)
    (g : GraphState Node) (f : Frag Node) (add? : Bool) :
    A.step g f add? =
      refSpec (if add? then GraphState.addFrag g f else GraphState.removeFrag g f) :=
  A.correct _ _ _

/-- Recompute algorithm bundled with the invariant proof. -/
noncomputable def recomputeAlgInv (Node : Type) [DecidableEq Node] : IncrAlgInv Node where
  step g f add? := refcountRecomputeStep g f add?
  preserves g f add? := refcountRecompute_step_inv (g:=g) (f:=f) (add?:=add?)

end Bounds

end Reduce

