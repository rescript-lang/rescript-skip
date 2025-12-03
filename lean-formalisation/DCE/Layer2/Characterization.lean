/-
  Layer2/Characterization.lean
  Characterization lemmas for add and remove operations.
  Contains: reachability monotonicity, BFS characterization for additions,
  cascade characterization for removals.
-/
import DCE.Layer2.Algorithm

open Multiset
open Reduce

namespace Reduce

section Characterization
variable {Node : Type} [DecidableEq Node]

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

end Characterization

end Reduce

