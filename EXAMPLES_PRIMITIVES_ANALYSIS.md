# Examples: Primitives Analysis

This document analyzes each example from the catalogue to determine:
1. What primitives are needed to implement it with the existing Skip bindings
2. Whether a reducer is required, or if simpler operators suffice
3. What calculus primitives would be needed to express the solution

## Extended Examples (Deep Dives)

The following examples have detailed analysis with multiple solution approaches, trade-offs, and implementation sketches:

| Example | Topic | Key Insight |
|---------|-------|-------------|
| [2.5 Top-K per group](#example-25-top-k-per-group) | Ranking, bounded aggregation | Structural solution using key ordering—no reducer needed |
| [2.7 Approximate distinct (HLL)](#example-27-approximate-distinct-hll) | Probabilistic data structures | Well-formed if append-only; hybrid exact/approx for deletions |
| [4.6 Sliding window average](#example-46-rxjs-style-sliding-window--moving-average) | Temporal aggregation | External eviction (Skip idiom) keeps reducer simple |
| [5.1 Undo/redo history](#example-51-elm-style-undoredo-history) | Sequential state, time-travel | Fundamentally non-commutative—cannot be a reducer |
| [5.4 Resettable accumulator](#example-54-frp-style-resettable-accumulator) | Reset semantics | Epoch-based keys transform reset into standard aggregation |
| [6.3 Acyclic joins](#example-63-dynamic-acyclic-join-yannakakis) | Multi-way joins | Map with context lookups—Skip handles delta propagation |
| [6.4 Counting/DRed views](#example-64-counting-and-dred-style-materialized-views) | Recursive queries | Sum reducer for non-recursive; fixpoint for recursive |
| [6.7 Fixpoint algorithms](#example-67-iterative-graph-algorithms-with-fixpoints) | Graph algorithms | Requires iteration—need new `fixpoint` primitive |

### Related: Reactive DCE Case Study

The document `dce_reactive_view.tex` provides a fully worked example of **reactive dead-code elimination** that demonstrates the two-layer architecture in practice:

- **Layer 1 (aggregation)**: File fragments `(nodes, roots, edges)` are combined via multiset union—a well-formed reducer (Examples 6.4/6.6 pattern).
- **Layer 2 (graph algorithm)**: Incremental liveness via refcounts + BFS/cascade propagation—a compute node, not a reducer (Examples 6.4 recursive / 6.7 pattern).

The Lean formalization (`lean-formalisation/DCE.lean`) proves well-formedness for Layer 1 and delta-boundedness for Layer 2. Section 7 of that document explicitly analyzes why Layer 2 *cannot* be packaged as an invertible reducer—reaching the same conclusion as Examples 6.4 and 6.7 in this analysis.

---

## Available Skip Primitives

From the bindings (`SkipruntimeCore.res`):

| Category | Primitives | Description |
|----------|------------|-------------|
| **Structural** | `map` | Transform entries `(k, vs) → [(k', v'), ...]` |
| | `slice(start, end)` | Keep keys in range `[start, end]` |
| | `slices(ranges)` | Keep keys in any of multiple ranges |
| | `take(n)` | Keep first n entries by key order |
| | `merge(collections)` | Union: each key gets values from all inputs |
| **Aggregation** | `reduce(reducer)` | Per-key fold with `(initial, add, remove)` |
| | `mapReduce(mapper, reducer)` | Fused map + reduce |
| **Lazy/Compute** | `LazyCollection` | On-demand computation |
| | `LazyCompute` | Custom compute function |
| **External** | `useExternalResource` | Integrate external services |

## Classification Legend

- **🟢 Structural only**: No reducer needed; uses only `map`, `slice`, `take`, `merge`
- **🟡 Standard reducer**: Needs a reducer, but a simple/standard one (count, sum, min, max)
- **🟠 Enriched reducer**: Needs a reducer with enriched state `(sum, count)`, `(min, secondMin, countMin)`, etc.
- **🔴 Partial/recompute**: Reducer that may need to recompute on remove (e.g., set membership, top-K eviction)
- **🟣 Compute node**: Needs lazy compute, fixpoint, or external—not a reducer pattern

---

## Section 1: Simple Per-Key Views

### Example 1.1: Active members per group
**Classification: 🟡 Standard reducer (count)**

```
Input:  memberships : GroupId × UserId
        activeUsers : UserId × bool (external filter)
Output: activeMembers : GroupId → int
```

**Implementation:**
```rescript
// Step 1: Filter to active memberships only (map with filter)
let activeMemberships = memberships->map(filterActiveMapper)  // uses activeUsers lookup

// Step 2: Reduce per group with count
let activeMembers = activeMemberships->reduce(countReducer)
```

**Primitives needed:** `map` (with context lookup), `reduce` (count)

---

### Example 1.2: Total sales by category
**Classification: 🟡 Standard reducer (sum)**

```
Input:  sales : SaleId × Sale{categoryId, amount}
Output: categoryTotals : CategoryId → Money
```

**Implementation:**
```rescript
let categoryTotals = sales
  ->map(sale => (sale.categoryId, sale.amount))  // re-key by category
  ->reduce(sumReducer)                            // sum per category
```

**Primitives needed:** `map` (re-key), `reduce` (sum)

---

### Example 1.3: Portfolio value by sector
**Classification: 🟡 Standard reducer (sum)**

```
Input:  positions : PositionId × Position{sector, shares, price}
Output: sectorValue : SectorId → Money
```

**Implementation:**
```rescript
let sectorValue = positions
  ->map(pos => (pos.sector, pos.shares * pos.price))
  ->reduce(sumReducer)
```

**Primitives needed:** `map` (re-key + compute), `reduce` (sum)

---

### Example 1.4: Global active-user count
**Classification: 🟡 Standard reducer (count)**

```
Input:  users : UserId × UserState{isActive}
Output: activeCount : Unit → int
```

**Implementation:**
```rescript
let activeCount = users
  ->map((userId, state) => if state.isActive { [((), 1)] } else { [] })
  ->reduce(countReducer)  // or sumReducer since we emit 1s
```

**Primitives needed:** `map` (filter + single-key), `reduce` (count)

---

### Example 1.5: Max value per key
**Classification: 🔴 Partial/recompute OR 🟠 Enriched**

```
Input:  measurements : KeyId × Value
Output: maxPerKey : KeyId → Value
```

**Implementation options:**

*Option A (partial reducer):*
```rescript
// Simple max reducer; remove triggers recompute when removing the current max
let maxReducer = Reducer.make(
  ~initial = _ => Some(neg_infinity),
  ~add = (acc, v, _) => max(acc, v),
  ~remove = (acc, v, _) => if v < acc { Some(acc) } else { None }  // recompute
)
```

*Option B (enriched reducer):*
```rescript
// Track (max, secondMax, countOfMax) to avoid some recomputes
// Still partial if all copies of max are removed and no secondMax
```

**Primitives needed:** `reduce` (with partial remove)

---

### Example 1.6: Min value per key
**Classification: 🔴 Partial/recompute OR 🟠 Enriched**

Same as max, symmetric.

---

### Example 1.7: Continuous count per key (KTable-style)
**Classification: 🟡 Standard reducer (count)**

```
Input:  events : KeyId × Event
Output: counts : KeyId → int
```

**Implementation:**
```rescript
let counts = events->reduce(countReducer)
```

**Primitives needed:** `reduce` (count)

---

### Example 1.8: Per-window sum
**Classification: 🟡 Standard reducer (sum)**

```
Input:  values : (KeyId, WindowId) × Number
Output: windowSum : (KeyId, WindowId) → Number
```

**Implementation:**
```rescript
// Key already includes WindowId; just sum
let windowSum = values->reduce(sumReducer)
```

**Primitives needed:** `reduce` (sum)

*Note:* Window management (creating/expiring WindowIds) is external.

---

### Example 1.9: Aggregated materialized view (GROUP BY SUM)
**Classification: 🟡 Standard reducer (sum)**

```
Input:  Sales(productId, amount)
Output: ProductTotals : ProductId → Money
```

**Implementation:**
```rescript
let productTotals = sales
  ->map(sale => (sale.productId, sale.amount))
  ->reduce(sumReducer)
```

**Primitives needed:** `map`, `reduce` (sum)

---

### Example 1.10: FRP event-counter (foldp)
**Classification: 🟡 Standard reducer (count)**

```
Input:  clicks : CounterId × unit
Output: clickCount : CounterId → int
```

**Implementation:**
```rescript
let clickCount = clicks->reduce(countReducer)
```

**Primitives needed:** `reduce` (count)

---

### Example 1.11: Cart totals and sums
**Classification: 🟡 Standard reducer (sum)**

```
Input:  cartItems : UserId × CartItem{quantity, unitPrice}
Output: cartTotal : UserId → Money
```

**Implementation:**
```rescript
let cartTotal = cartItems
  ->map((userId, item) => (userId, item.quantity * item.unitPrice))
  ->reduce(sumReducer)
```

**Primitives needed:** `map`, `reduce` (sum)

---

### Example 1.12: Per-player score
**Classification: 🟡 Standard reducer (sum)**

```
Input:  scoreEvents : PlayerId × int (delta)
Output: scores : PlayerId → int
```

**Implementation:**
```rescript
let scores = scoreEvents->reduce(sumReducer)
```

**Primitives needed:** `reduce` (sum)

---

### Example 1.13: Vertex-degree counting
**Classification: 🟡 Standard reducer (count)**

```
Input:  edges : EdgeId × (src, dst)
Output: degree : NodeId → int
```

**Implementation:**
```rescript
// Emit both endpoints for undirected, or just dst for in-degree
let nodeDegree = edges
  ->map((_, edge) => [(edge.src, 1), (edge.dst, 1)])
  ->reduce(sumReducer)  // sum of 1s = count
```

**Primitives needed:** `map` (fan-out), `reduce` (count/sum)

---

## Section 2: Enriched-State Views

### Example 2.1: Average rating per item
**Classification: 🟠 Enriched reducer**

```
Input:  ratings : ItemId × Rating{score}
Output: avgRating : ItemId → float
```

**Implementation:**
```rescript
// Accumulator: (sum, count)
let avgReducer = Reducer.make(
  ~initial = _ => Some((0.0, 0)),
  ~add = ((sum, count), rating, _) => (sum + rating.score, count + 1),
  ~remove = ((sum, count), rating, _) => 
    if count > 1 { Some((sum - rating.score, count - 1)) } else { None }
)

let avgRating = ratings
  ->reduce(avgReducer)
  ->map(((sum, count)) => sum / float(count))  // project to ratio
```

**Primitives needed:** `reduce` (enriched), `map` (project)

---

### Example 2.2: Histogram / frequency distribution
**Classification: 🟠 Enriched reducer**

```
Input:  events : KeyId × Value
Output: histograms : KeyId → Map<BucketId, int>
```

**Implementation:**
```rescript
// Accumulator: Map<BucketId, int>
let histReducer = Reducer.make(
  ~initial = _ => Some(Map.empty),
  ~add = (hist, v, _) => {
    let b = bucket(v)
    Map.update(hist, b, n => n + 1)
  },
  ~remove = (hist, v, _) => {
    let b = bucket(v)
    let newCount = Map.get(hist, b) - 1
    if newCount == 0 { Some(Map.remove(hist, b)) } 
    else { Some(Map.set(hist, b, newCount)) }
  }
)
```

**Primitives needed:** `reduce` (enriched with map accumulator)

---

### Example 2.3: Distinct count with reference counts
**Classification: 🟠 Enriched reducer**

```
Input:  events : KeyId × Value
Output: distinctCount : KeyId → int
```

**Implementation:**
```rescript
// Accumulator: Map<Value, int> (frequency map)
let distinctReducer = Reducer.make(
  ~initial = _ => Some(Map.empty),
  ~add = (freq, v, _) => Map.update(freq, v, n => n + 1),
  ~remove = (freq, v, _) => {
    let newCount = Map.get(freq, v) - 1
    if newCount == 0 { Some(Map.remove(freq, v)) }
    else { Some(Map.set(freq, v, newCount)) }
  }
)

let distinctCount = events
  ->reduce(distinctReducer)
  ->map(freq => Map.size(freq))
```

**Primitives needed:** `reduce` (enriched), `map` (project)

---

### Example 2.4: Weighted average
**Classification: 🟠 Enriched reducer**

```
Input:  measurements : KeyId × (value, weight)
Output: weightedAvg : KeyId → float
```

**Implementation:**
```rescript
// Accumulator: (sumWeights, sumWeightedValues)
let weightedAvgReducer = Reducer.make(
  ~initial = _ => Some((0.0, 0.0)),
  ~add = ((sw, swv), (v, w), _) => (sw + w, swv + w * v),
  ~remove = ((sw, swv), (v, w), _) => 
    if sw > w { Some((sw - w, swv - w * v)) } else { None }
)
```

**Primitives needed:** `reduce` (enriched), `map` (project ratio)

---

### Example 2.5: Top-K per group
**Classification: 🔴 Partial/recompute OR 🟢 Structural (depending on approach)**

```
Input:  scores : GroupId × (itemId, score)
Output: topK : GroupId → array<(Id, float)>
```

#### Requirements Analysis

The goal is to maintain, for each group, the K items with the highest scores. We need to handle:
- **Additions**: New item may enter the top-K, evicting the current Kth item
- **Removals**: Removed item may have been in top-K, requiring a replacement
- **Updates**: Item's score changes (modeled as remove + add)

The core challenge: **when an item in the top-K is removed, where do we find its replacement?**

#### Solution 1: Structural (No Reducer) — SIMPLEST

**Key insight**: Skip collections are multi-valued and ordered by key. We can encode ranking in the key structure.

```
Step 1: Re-key by (groupId, negativeScore, itemId)
Step 2: For each group, the first K entries by key order are the top-K
```

**Implementation:**
```rescript
// Re-key so that highest scores come first in key order
// Using negative score ensures descending order (Skip orders keys ascending)
let rankedItems = scores->map((groupId, (itemId, score)) => 
  ((groupId, -.score, itemId), (itemId, score))  // compound key, original value
)

// To get top-K for a specific group:
// Use slice to get entries for that group, then take(K)
// This requires knowing the group bounds in the key space

// Alternatively, expose as a LazyCompute that queries per group:
let topKCompute = LazyCompute.make((self, groupId, ctx, params) => {
  let k = params[0]  // K parameter
  // Get all items for this group by slicing on the group prefix
  let groupItems = rankedItems->slice((groupId, neg_infinity, ""), (groupId, infinity, ""))
  // Take first K
  groupItems->take(k)->getAll->Array.map(((_, _, _), v) => v)
})
```

**Trade-offs:**
- ✅ No reducer needed — purely structural
- ✅ No partial recomputation — Skip handles ordering
- ✅ Always correct
- ❌ Stores all items, not just top-K (but Skip manages this efficiently)
- ❌ `slice` per group may be less efficient than a dedicated per-key aggregator

**Verdict**: For most use cases, this structural approach is simplest and correct. Use a reducer only if memory for non-top-K items is a hard constraint.

#### Solution 2: Buffered Reducer (Enriched State)

If we must limit memory per group, maintain a buffer larger than K:

```rescript
// Accumulator: sorted array of top (K + buffer_size) items
// Buffer provides candidates when a top-K item is removed
type topKState = {
  items: array<(Id, float)>,  // sorted descending by score
  k: int,
  bufferSize: int,
}

let topKReducer = Reducer.make(
  ~initial = params => Some({ items: [], k: params[0], bufferSize: params[1] }),
  
  ~add = (state, (id, score), _) => {
    // Insert in sorted order, keep at most K + bufferSize
    let newItems = insertSorted(state.items, (id, score))
    if Array.length(newItems) > state.k + state.bufferSize {
      { ...state, items: Array.slice(newItems, 0, state.k + state.bufferSize) }
    } else {
      { ...state, items: newItems }
    }
  },
  
  ~remove = (state, (id, score), _) => {
    let newItems = Array.filter(state.items, ((i, _)) => i != id)
    // If removed item was in buffer, we're fine
    // If buffer is now empty and we had K+bufferSize items, might need recompute
    if Array.length(newItems) >= state.k || Array.length(state.items) <= state.k {
      Some({ ...state, items: newItems })
    } else {
      None  // Buffer exhausted, need recompute
    }
  }
)

// Project to just the top K for output
let topK = scores->reduce(topKReducer)->map(state => Array.slice(state.items, 0, state.k))
```

**Trade-offs:**
- ✅ Bounded memory per group (K + buffer)
- ✅ Avoids most recomputes when buffer is sufficient
- ⚠️ Still partial: recomputes when buffer exhausted
- ❌ More complex implementation

#### Solution 3: Full Recompute Reducer (Partial)

The simplest reducer that trades off recomputation for minimal state:

```rescript
let simpleTopKReducer = Reducer.make(
  ~initial = _ => Some([]),
  ~add = (topK, (id, score), params) => {
    let k = params[0]
    insertSortedAndTruncate(topK, (id, score), k)
  },
  ~remove = (topK, (id, score), _) => {
    if Array.some(topK, ((i, _)) => i == id) {
      None  // Item was in top-K, must recompute
    } else {
      Some(topK)  // Item wasn't in top-K, no change
    }
  }
)
```

**Verdict**: Use Solution 1 (structural) unless you have specific memory constraints.

**Primitives needed:** 
- Solution 1: `map` (re-key), `slice`, `take`, or `LazyCompute`
- Solution 2/3: `reduce` (enriched or partial)

---

### Example 2.6: Top-N ranking
**Classification: 🔴 Partial/recompute**

Same as Top-K.

---

### Example 2.7: Approximate distinct (HLL)
**Classification: 🟡 Standard reducer (append-only) OR 🔴 Partial OR 🟠 Enriched**

```
Input:  events : KeyId × UserId
Output: approxDistinct : KeyId → int
```

#### Requirements Analysis

HyperLogLog (HLL) is a probabilistic data structure for cardinality estimation. It:
- Uses O(log log n) space to estimate n distinct elements
- Supports `add(element)` efficiently
- **Does NOT natively support `remove(element)`**

The fundamental question: **Are deletions required?**

#### Solution 1: Append-Only (No Deletions) — SIMPLEST

If the input collection is append-only (events are never deleted), HLL is a perfect well-formed reducer:

```rescript
// HLL accumulator (assuming an HLL library)
let hllReducer = Reducer.make(
  ~initial = _ => Some(HLL.empty(precision: 14)),  // ~16KB per key, 0.8% error
  
  ~add = (hll, userId, _) => HLL.add(hll, userId),
  
  ~remove = (hll, userId, _) => Some(hll)  // Ignore removes — they don't happen
)

let approxDistinct = events
  ->reduce(hllReducer)
  ->map(hll => HLL.cardinality(hll))
```

**This is well-formed** because:
- `add` is commutative: HLL.add order doesn't matter
- `remove` is never called (or is a no-op)

**Trade-offs:**
- ✅ O(1) add, O(log log n) space
- ✅ Well-formed reducer
- ❌ Cannot handle deletions
- ❌ Approximate (typically 1-2% error with standard precision)

#### Solution 2: Partial Reducer (Deletions Trigger Recompute)

If deletions are possible but rare, accept recomputation:

```rescript
let hllPartialReducer = Reducer.make(
  ~initial = _ => Some(HLL.empty(precision: 14)),
  
  ~add = (hll, userId, _) => HLL.add(hll, userId),
  
  ~remove = (hll, userId, _) => None  // Any deletion triggers full recompute
)
```

**Trade-offs:**
- ✅ Simple implementation
- ✅ Correct (via recompute)
- ❌ Expensive on delete: O(n) to rebuild HLL from all remaining elements

#### Solution 3: Exact Counting with HLL Fallback (Enriched)

For small cardinalities, use exact counting; switch to HLL when it gets large:

```rescript
type hybridState = 
  | Exact(Map<UserId, int>)  // frequency map
  | Approx(HLL.t)

let threshold = 10000  // Switch to HLL above this

let hybridReducer = Reducer.make(
  ~initial = _ => Some(Exact(Map.empty)),
  
  ~add = (state, userId, _) => {
    switch state {
    | Exact(freq) => {
        let newFreq = Map.update(freq, userId, n => n + 1)
        if Map.size(newFreq) > threshold {
          // Convert to HLL
          let hll = Map.keys(newFreq)->Array.reduce(HLL.empty(), HLL.add)
          Approx(hll)
        } else {
          Exact(newFreq)
        }
      }
    | Approx(hll) => Approx(HLL.add(hll, userId))
    }
  },
  
  ~remove = (state, userId, _) => {
    switch state {
    | Exact(freq) => {
        let count = Map.get(freq, userId)
        if count == 1 {
          Some(Exact(Map.remove(freq, userId)))
        } else {
          Some(Exact(Map.set(freq, userId, count - 1)))
        }
      }
    | Approx(_) => None  // Once in HLL mode, deletions trigger recompute
    }
  }
)
```

**Trade-offs:**
- ✅ Exact for small cardinalities (supports deletions)
- ✅ Space-efficient for large cardinalities
- ⚠️ Partial in HLL mode
- ❌ More complex implementation

#### Solution 4: Use Exact Distinct Count (Enriched Reducer)

If approximate isn't acceptable or deletions are common, use the exact distinct count pattern from Example 2.3:

```rescript
// From Example 2.3: frequency map as accumulator
let exactDistinctReducer = Reducer.make(
  ~initial = _ => Some(Map.empty),
  ~add = (freq, userId, _) => Map.update(freq, userId, n => n + 1),
  ~remove = (freq, userId, _) => {
    let count = Map.get(freq, userId) - 1
    if count == 0 { Some(Map.remove(freq, userId)) }
    else { Some(Map.set(freq, userId, count)) }
  }
)

let exactDistinct = events
  ->reduce(exactDistinctReducer)
  ->map(freq => Map.size(freq))
```

**This is well-formed** (fully invertible) but uses O(n) space.

#### Verdict

| Scenario | Best Solution |
|----------|---------------|
| Append-only data | Solution 1 (HLL, well-formed) |
| Rare deletions | Solution 2 (HLL, partial) |
| Small cardinalities with deletions | Solution 4 (exact, well-formed) |
| Mixed | Solution 3 (hybrid) |

**Primitives needed:** `reduce` (various forms), `map` (project cardinality)

---

### Example 2.8: Sliding-window averages
**Classification: 🟠 Enriched reducer**

Same as average (sum, count), but with WindowId in key.

---

### Example 2.9: Enriched min/max with secondary state
**Classification: 🟠 Enriched reducer**

```
Input:  values : KeyId × Value
Output: minPerKey : KeyId → Value
```

**Implementation:**
```rescript
// Accumulator: (min, secondMin, countMin)
let enrichedMinReducer = Reducer.make(
  ~initial = _ => Some((infinity, infinity, 0)),
  ~add = ((min, second, count), v, _) => {
    if v < min { (v, min, 1) }
    else if v == min { (min, second, count + 1) }
    else if v < second { (min, v, count) }
    else { (min, second, count) }
  },
  ~remove = ((min, second, count), v, _) => {
    if v == min {
      if count > 1 { Some((min, second, count - 1)) }
      else { Some((second, infinity, 1)) }  // promote secondMin
    } else if v == second { None }  // recompute to find new second
    else { Some((min, second, count)) }
  }
)
```

**Primitives needed:** `reduce` (enriched, sometimes partial)

---

## Section 3: Set and Index Views

### Example 3.1: Groups-per-user index (inverted index)
**Classification: 🟢 Structural only**

```
Input:  groupMembers : GroupId × UserId
Output: groupsPerUser : UserId → array<GroupId>
```

**Implementation:**
```rescript
// Just re-key: emit (userId, groupId) for each (groupId, userId)
// No reducer needed! The collection naturally accumulates multiple values per key.
let groupsPerUser = groupMembers
  ->map((groupId, userId) => (userId, groupId))
```

**Primitives needed:** `map` only!

*Note:* Skip collections are multi-valued by default. Each key can have multiple values, so "collecting all groups for a user" is just the default behavior after re-keying.

---

### Example 3.2: Exact distinct count per key
**Classification: 🟠 Enriched reducer**

Same as Example 2.3.

---

### Example 3.3: Distinct visitors (exact or HLL)
**Classification: 🟠 Enriched OR 🔴 Partial**

Same patterns as 2.3 or 2.7.

---

### Example 3.4: General inverted index
**Classification: 🟢 Structural only**

```
Input:  relations : LeftId × RightId
Output: rightPerLeft : LeftId → array<RightId>
        leftPerRight : RightId → array<LeftId>
```

**Implementation:**
```rescript
// Both are just map operations
let rightPerLeft = relations  // identity, already keyed by LeftId
let leftPerRight = relations->map((left, right) => (right, left))
```

**Primitives needed:** `map` only (twice for bidirectional)

---

## Section 4: Windowed and Session-Based Views

### Example 4.1: Sliding time-window aggregate
**Classification: 🟡 Standard reducer (count/sum) + External window management**

```
Input:  events : (KeyId, Timestamp) × Payload
Output: lastHourCount : KeyId → int
```

**Implementation:**
The reducer itself is standard (count/sum). Window management (expiring old events) is external.

**Primitives needed:** `reduce` (standard) + external scheduler

---

### Example 4.2: Session-based aggregation
**Classification: 🟡 Standard reducer + External sessionization**

Same pattern: standard per-session reducer, sessionization logic external.

---

### Example 4.3: Fixed/sliding window sum/average
**Classification: 🟡/🟠 Standard/enriched reducer**

Standard sum or enriched (sum, count) for average.

---

### Example 4.4: Session window count
**Classification: 🟡 Standard reducer (count)**

---

### Example 4.5: Materialize-style time-bounded active count
**Classification: 🟡 Standard reducer (sum)**

Model as +1 at start, -1 at end. Reducer is just sum.

---

### Example 4.6: RxJS-style sliding window / moving average
**Classification: 🟡 Standard reducer + External eviction (SIMPLEST) OR 🔴 Internal buffer**

```
Input:  samples : (StreamId, Timestamp) × float
Output: movingAvg : StreamId → float
```

#### Requirements Analysis

A sliding window average computes the mean of values within a time window (e.g., last 5 minutes) or count window (e.g., last 100 samples). The key challenges:

1. **Time-based window**: Which samples are "in" the window changes over time
2. **Count-based window**: Need to track ordering to know which samples to evict
3. **Eviction**: Old samples must be removed from the average

#### Solution 1: External Window Management — SIMPLEST (Skip Idiom)

**Key insight**: Skip already has add/remove semantics. Let an external process manage the window by inserting and deleting samples from the collection.

```
Architecture:
┌─────────────────┐      ┌──────────────────┐      ┌─────────────────┐
│  Sample Source  │ ──── │  Skip Collection │ ──── │  Avg Reducer    │
│  (inserts)      │      │  samples         │      │  (sum, count)   │
└─────────────────┘      └──────────────────┘      └─────────────────┘
                                  ▲
                                  │ deletes
                         ┌───────┴───────┐
                         │ Window Manager │
                         │ (external)     │
                         └───────────────┘
```

**Implementation:**
```rescript
// The reducer is just a standard average reducer — simple!
let avgReducer = Reducer.make(
  ~initial = _ => Some((0.0, 0)),  // (sum, count)
  ~add = ((sum, count), value, _) => (sum +. value, count + 1),
  ~remove = ((sum, count), value, _) => 
    if count > 1 { Some((sum -. value, count - 1)) } else { None }
)

// Input collection: samples are keyed by (streamId, timestamp)
// Window manager deletes samples with timestamp < now - windowSize

let movingAvg = samples
  ->map((streamId, timestamp), value) => (streamId, value))  // drop timestamp from key
  ->reduce(avgReducer)
  ->map(((sum, count)) => if count > 0 { sum /. float(count) } else { 0.0 })
```

**External window manager (separate process or cron):**
```typescript
// Periodically evict old samples
async function evictOldSamples(broker, windowMs: number) {
  const cutoff = Date.now() - windowMs;
  const allSamples = await broker.getAll("samples", null);
  const toDelete = allSamples
    .filter(([key, _]) => key[1] < cutoff)  // key is (streamId, timestamp)
    .map(([key, _]) => [key, []]);  // empty values = delete
  await broker.update("samples", toDelete);
}
```

**Trade-offs:**
- ✅ Reducer is trivially well-formed (just average)
- ✅ Clean separation: Skip handles reactivity, external handles time
- ✅ Works for any window size without changing the reducer
- ❌ Requires external coordination
- ❌ Window boundaries are "eventually consistent" with wall-clock time

#### Solution 2: Count-Based Window with Structural Operators

For "last N samples" (count-based), use key ordering + `take`:

```rescript
// Key by (streamId, -timestamp) so newest samples come first
let orderedSamples = samples->map(((streamId, ts), value) => 
  ((streamId, -.float(ts)), value)
)

// For each stream, take the last N samples
// This requires per-stream operation, so use LazyCompute
let lastNCompute = LazyCompute.make((self, streamId, ctx, params) => {
  let n = params[0]
  let streamSamples = orderedSamples
    ->slice((streamId, neg_infinity), (streamId, infinity))
    ->take(n)
  let values = streamSamples->getAll->Array.map(((_, v)) => v)
  let sum = Array.reduce(values, 0.0, (+.))
  [sum /. float(Array.length(values))]
})
```

**Trade-offs:**
- ✅ No external process needed
- ✅ Exact N-sample window
- ❌ Recomputes on every query (lazy)
- ❌ Stores all samples, not just last N

#### Solution 3: Internal Buffer Reducer (Complex)

If you must bound memory AND avoid external processes:

```rescript
type windowState = {
  buffer: array<(Timestamp, float)>,  // sorted by timestamp
  windowSize: int,  // for count-based
  sum: float,
  count: int,
}

let windowReducer = Reducer.make(
  ~initial = params => Some({
    buffer: [],
    windowSize: params[0],
    sum: 0.0,
    count: 0,
  }),
  
  ~add = (state, (timestamp, value), _) => {
    // Add new sample
    let newBuffer = insertSorted(state.buffer, (timestamp, value))
    let newSum = state.sum +. value
    let newCount = state.count + 1
    
    // Evict oldest if over window size
    if newCount > state.windowSize {
      let (_, oldestValue) = newBuffer[0]
      {
        buffer: Array.sliceFrom(newBuffer, 1),
        windowSize: state.windowSize,
        sum: newSum -. oldestValue,
        count: newCount - 1,
      }
    } else {
      { ...state, buffer: newBuffer, sum: newSum, count: newCount }
    }
  },
  
  ~remove = (state, (timestamp, value), _) => {
    // Check if this sample is in our buffer
    let idx = Array.findIndex(state.buffer, ((t, _)) => t == timestamp)
    if idx >= 0 {
      // Removing a sample from buffer — need to adjust
      let newBuffer = Array.removeAt(state.buffer, idx)
      Some({
        ...state,
        buffer: newBuffer,
        sum: state.sum -. value,
        count: state.count - 1,
      })
    } else {
      // Sample wasn't in buffer (already evicted), no change
      Some(state)
    }
  }
)
```

**Trade-offs:**
- ✅ Bounded memory (windowSize samples)
- ✅ Self-contained (no external process)
- ⚠️ Complex implementation
- ⚠️ Assumes samples arrive roughly in order (eviction by count may behave unexpectedly with out-of-order arrivals)
- ❌ Not well-formed: `add` may evict old samples, violating `(a ⊕ v) ⊖ v = a`

#### Verdict

| Scenario | Best Solution |
|----------|---------------|
| Time-based window | Solution 1 (external eviction) |
| Count-based, query-time | Solution 2 (structural + lazy) |
| Count-based, bounded memory | Solution 3 (internal buffer) |

**The Skip idiom favors Solution 1**: let the reactive system handle aggregation, let external processes handle temporal concerns.

**Primitives needed:**
- Solution 1: `map`, `reduce` (standard average), external eviction
- Solution 2: `map`, `slice`, `take`, `LazyCompute`
- Solution 3: `reduce` (complex, not well-formed)

---

### Example 4.7: Text input with clear (FRP reset pattern)
**Classification: 🟡 Standard reducer with external reset**

When a clear event arrives, the accumulator resets. This could be modeled as a stateful reducer or as window logic.

---

## Section 5: History and Ordered-State Patterns

### Example 5.1: Elm-style undo/redo history
**Classification: 🟣 Compute node (not reducer) — Fundamentally non-commutative**

```
Input:  commands : Unit × Command  // Command = Action(a) | Undo | Redo
Output: History : Unit → { past: array<State>, present: State, future: array<State> }
```

#### Requirements Analysis

Undo/redo maintains a linear history with three components:
- **past**: States before the current one (stack, most recent at end)
- **present**: Current state
- **future**: States after current (for redo, most recent at start)

Operations:
- **Action(a)**: Apply action to present, push old present to past, clear future
- **Undo**: Pop from past to present, push old present to future
- **Redo**: Pop from future to present, push old present to past

#### Why This Is NOT a Reducer

Reducers require **commutativity**: `(a ⊕ v₁) ⊕ v₂ = (a ⊕ v₂) ⊕ v₁`

But undo/redo is **order-dependent**:
```
Action("draw") then Undo  →  state is initial
Undo then Action("draw")  →  state has the drawing
```

These are fundamentally different outcomes. **No encoding as a reducer is possible.**

#### Why This Doesn't Fit Skip's Model

Skip collections are **unordered multisets**. The order in which entries arrive is not preserved. But undo/redo requires a **sequential command stream**.

Even if we add sequence numbers to commands:
```
commands : Unit × (seqNum: int, Command)
```

A reducer would need to process commands in sequence-number order, which violates commutativity.

#### Solution 1: External State Machine — SIMPLEST

Keep the history state outside Skip; use Skip only for derived views.

```typescript
// External state machine (not in Skip)
class HistoryManager {
  private past: State[] = [];
  private present: State = initialState;
  private future: State[] = [];
  
  apply(cmd: Command): void {
    switch (cmd.type) {
      case 'action':
        this.past.push(this.present);
        this.present = applyAction(this.present, cmd.action);
        this.future = [];
        break;
      case 'undo':
        if (this.past.length > 0) {
          this.future.unshift(this.present);
          this.present = this.past.pop()!;
        }
        break;
      case 'redo':
        if (this.future.length > 0) {
          this.past.push(this.present);
          this.present = this.future.shift()!;
        }
        break;
    }
    // Publish current state to Skip collection
    skipBroker.update("currentState", [[null, [this.present]]]);
  }
}

// Skip service just exposes the current state
const service: SkipService = {
  initialData: { currentState: [[null, [initialState]]] },
  resources: { currentState: CurrentStateResource },
  createGraph: (inputs) => inputs,
};
```

**Trade-offs:**
- ✅ Simple, correct
- ✅ History logic is clear and testable outside Skip
- ❌ State is not reactive within Skip
- ❌ Skip is just a pass-through for the current state

#### Solution 2: Sequence-Indexed Collection + LazyCompute

Store commands with sequence numbers; compute history on demand by replaying:

```rescript
// Commands stored with sequence numbers
// commands : Unit × array<(seqNum, Command)>  — accumulates all commands

// LazyCompute replays commands to compute current history
let historyCompute = LazyCompute.make((self, _, ctx, _) => {
  let allCommands = commands->getAll  // Get all commands
  
  // Sort by sequence number
  let sorted = allCommands
    ->Array.flatMap(((_, cmds)) => cmds)
    ->Array.sortBy(((seq, _)) => seq)
  
  // Replay to compute history
  let history = Array.reduce(sorted, initialHistory, (hist, (_, cmd)) => {
    switch cmd {
    | Action(a) => {
        past: Array.concat(hist.past, [hist.present]),
        present: applyAction(hist.present, a),
        future: [],
      }
    | Undo => 
        switch Array.pop(hist.past) {
        | Some((newPast, oldPresent)) => {
            past: newPast,
            present: oldPresent,
            future: Array.concat([hist.present], hist.future),
          }
        | None => hist
        }
    | Redo =>
        switch hist.future {
        | [next, ...rest] => {
            past: Array.concat(hist.past, [hist.present]),
            present: next,
            future: rest,
          }
        | [] => hist
        }
    }
  })
  
  [history]
})
```

**Trade-offs:**
- ✅ All state in Skip
- ✅ Reactive to new commands
- ❌ O(n) replay on every query
- ❌ Must store all commands forever (no garbage collection)
- ❌ Complex implementation

#### Solution 3: Hybrid — Checkpoint + Recent Commands

Store periodic checkpoints of history state, plus recent commands:

```rescript
// Two collections:
// checkpoints : Unit × HistorySnapshot  (latest checkpoint)
// recentCommands : Unit × array<(seqNum, Command)>  (since last checkpoint)

// LazyCompute replays only recent commands from checkpoint
let historyCompute = LazyCompute.make((self, _, ctx, _) => {
  let checkpoint = checkpoints->getUnique(())
  let recent = recentCommands->getArray(())
  
  // Replay recent commands from checkpoint
  let sorted = recent->Array.sortBy(((seq, _)) => seq)
  let history = Array.reduce(sorted, checkpoint, replayCommand)
  
  [history]
})

// External process periodically:
// 1. Reads current history
// 2. Writes new checkpoint
// 3. Clears recentCommands
```

**Trade-offs:**
- ✅ Bounded replay cost
- ✅ Can garbage-collect old commands
- ⚠️ Requires external checkpointing process

#### Verdict

**Undo/redo is fundamentally outside the reducer fragment.** It requires:
- Sequential processing (non-commutative)
- State that depends on operation order

**Recommended approach**: Solution 1 (external state machine) for simplicity, or Solution 3 (checkpoint + replay) if reactivity within Skip is required.

**Primitives needed:** `LazyCompute` for on-demand replay, or external state management

---

### Example 5.2: Redux-like time-travel state
**Classification: 🟣 Compute node**

Same as 5.1.

---

### Example 5.3: Svelte-style undoable store
**Classification: 🟣 Compute node**

Same pattern.

---

### Example 5.4: FRP-style resettable accumulator
**Classification: 🟡 Standard reducer with epoch key — SIMPLEST**

```
Input:  events : KeyId × Event
        resets : KeyId × Unit  // Reset signal per key
Output: accumulated : KeyId → AccumulatorState
```

#### Requirements Analysis

This pattern appears in FRP systems (Elm, Yampa, reactive-banana) where:
- Events accumulate into a state (e.g., keystrokes → text, clicks → count)
- A "reset" signal clears the accumulator back to initial state
- After reset, accumulation continues from zero

Example: Text input with a "Clear" button
- Each keystroke appends to the current text
- Clicking "Clear" resets text to empty string

#### Why This Seems Tricky

At first glance, reset seems to require special handling:
- Events and resets are **two different input streams**
- Reset must "undo" all previous events

But there's a simple transformation that makes this a standard reducer problem.

#### Solution 1: Epoch-Based Keys — SIMPLEST

**Key insight**: Instead of "resetting" an accumulator, **start a new accumulator** for each epoch.

```
epoch[k] = count of resets for key k
Effective key = (k, epoch[k])
```

Each reset increments the epoch, and accumulation happens independently per (key, epoch) pair.

**Implementation:**
```rescript
// Step 1: Maintain epoch counter per key (count of resets)
let epochs = resets->reduce(countReducer)  // epochs : KeyId → int

// Step 2: Tag events with their epoch
let taggedEvents = events->map((key, event, ctx) => {
  let epoch = epochs->getUnique(key, ~ifNone=0)
  ((key, epoch), event)  // New key includes epoch
})

// Step 3: Standard reducer per (key, epoch)
let accumulated = taggedEvents->reduce(eventAccumulator)

// Step 4: Project to current epoch only
let currentAccumulated = accumulated->map(((key, epoch), acc, ctx) => {
  let currentEpoch = epochs->getUnique(key, ~ifNone=0)
  if epoch == currentEpoch {
    [(key, acc)]  // This is the current epoch
  } else {
    []  // Old epoch, don't emit
  }
})
```

**How it works:**
1. `epochs` counts resets per key: `{k1: 0, k2: 2, ...}`
2. Events for `k1` get tagged as `(k1, 0)`, events for `k2` as `(k2, 2)`
3. When a reset arrives for `k2`, `epochs[k2]` becomes 3
4. New events for `k2` get tagged as `(k2, 3)` — a fresh accumulator
5. Old `(k2, 2)` entries remain but are filtered out by step 4

**Trade-offs:**
- ✅ All reducers are standard, well-formed
- ✅ No special "reset" primitive needed
- ✅ Natural fit for Skip's reactive model
- ⚠️ Old epochs remain in storage (could garbage-collect separately)

#### Solution 2: External Reset via Deletion

Use Skip's normal add/remove semantics: a reset **deletes all events** for that key.

```typescript
// External reset handler
async function handleReset(broker, key) {
  // Get all events for this key
  const events = await broker.getArray("events", key, null);
  // Delete them by setting to empty
  await broker.update("events", [[key, []]]);
}
```

```rescript
// Reducer is completely standard
let accumulated = events->reduce(eventAccumulator)
```

**Trade-offs:**
- ✅ Simplest reducer (no epoch logic)
- ✅ Storage is cleaned up on reset
- ❌ Reset is O(n) in number of events to delete
- ❌ Requires external coordination

#### Solution 3: Reset as "Negative Sum" Event

If the accumulator supports additive inverses, model reset as an event that cancels previous state:

```rescript
// For numeric accumulation (e.g., sum)
// Reset emits a "negative current sum" event
let resetAsNegation = resets->map((key, _, ctx) => {
  let currentSum = accumulated->getUnique(key, ~ifNone=0)
  (key, -.currentSum)  // Emit negation
})

let allEvents = events->merge([resetAsNegation])
let accumulated = allEvents->reduce(sumReducer)
```

**Trade-offs:**
- ✅ Clean algebraic model
- ❌ Only works for invertible accumulators (sum, not min/max/string)
- ❌ Creates a dependency cycle (accumulated depends on resetAsNegation which depends on accumulated)

**This approach has a cycle and won't work directly in Skip.**

#### Verdict

**Solution 1 (epoch-based keys)** is the recommended approach:
- Transforms reset semantics into standard per-key aggregation
- Well-formed reducers throughout
- No external coordination beyond counting resets

**Pattern**: When you need "reset" semantics, **version your keys** with an epoch/generation counter.

**Primitives needed:**
- `reduce` (count) for epoch tracking
- `map` (tag with epoch, filter to current)
- `reduce` (standard) for accumulation

---

## Section 6: Graph and Relational Incremental Maintenance

### Example 6.1: DBToaster-style incremental SQL view
**Classification: 🟡 Standard reducers (sum) + join via map**

```
Input:  Orders(orderId, customerId, amount)
        Customers(customerId, region)
Output: RegionTotals : region → Money
```

**Implementation:**
```rescript
// Step 1: Sum orders per customer
let orderContrib = orders
  ->map(order => (order.customerId, order.amount))
  ->reduce(sumReducer)

// Step 2: Join with customers (via map + lookup)
let regionTotals = orderContrib
  ->map((customerId, amount) => {
    let region = customers.getUnique(customerId).region
    (region, amount)
  })
  ->reduce(sumReducer)
```

**Primitives needed:** `map`, `reduce` (sum), context lookup for join

#### DBToaster's higher-order delta processing in Skip (sketch)

The [DBToaster system](http://vldb.org/pvldb/vol5/p968_yanifahmad_vldb2012.pdf) (VLDB 2012) introduced *viewlet transforms*: a technique that recursively materializes higher-order delta views to achieve efficient incremental maintenance. The key insight is that delta queries (how a view changes when base data changes) can themselves be materialized and maintained incrementally.

This subsection sketches how a few canonical DBToaster examples can be expressed with current Skip primitives. It is meant as evidence that the **patterns** are compatible, not as a full equivalence result between DBToaster's formal calculus and the Skip runtime.

**DBToaster's canonical example: `count(R × S)`**

Instead of recomputing the product on each update, DBToaster materializes:
- `Q = |R| × |S|` (0th order — the query result)
- `ΔR Q = |S|` (1st order — delta when one tuple is added to R)
- `ΔS Q = |R|` (1st order — delta when one tuple is added to S)
- `ΔR(ΔS Q) = 1` (2nd order — constant, independent of data)

Update rule: When a tuple is inserted into R, compute `Q_new = Q_old + |S|` using only *addition*.

**Skip equivalent using current primitives:**

```rescript
// Materialize counts (analogous to DBToaster's 1st-order delta views)
let countR = r->reduce(countReducer)  // EagerCollection with single entry ("total", |R|)
let countS = s->reduce(countReducer)  // EagerCollection with single entry ("total", |S|)

// Compute product with reactive dependency on both counts
let product = countR->map(("total", rCount, _ctx) => {
  let sCount = countS->getUnique("total")
  ("result", rCount * sCount)
})
```

**How Skip achieves O(1) updates:**
- **R insert:** `countR` reducer updates incrementally (adds 1) → `product` mapper re-runs once → O(1)
- **S insert:** `countS` updates → reactive dependency triggers `product` re-run → O(1)

**Skip primitives used:**
- `reduce` with `countReducer` — maintains aggregate incrementally
- `map` with `getUnique` lookup — creates reactive dependency on `countS`
- Reactive dependency graph — automatically propagates changes

**More complex example: `sum(R.a * S.b)` over join `R(a, key) ⋈ S(key, b)`**

DBToaster maintains per-key partial aggregates and composes them:

```rescript
// Per-key partial sums (DBToaster's "delta views")
let sumAByKey = r->reduce(sumReducer)  // key → Σ{a | (a, key) ∈ R}
let sumBByKey = s->reduce(sumReducer)  // key → Σ{b | (key, b) ∈ S}

// Per-key contribution to result
let contributions = sumAByKey->map((key, sumA, _ctx) => {
  let sumB = sumBByKey->get(key)->Option.getOr(0)
  ("result", sumA * sumB)
})

// Final aggregation
let result = contributions->reduce(sumReducer)
```

**Update complexity analysis:**
- R adds `(a₀, k₀)`: `sumAByKey[k₀]` updates (O(1)) → only mapper for `k₀` re-runs (O(1)) → `result` reducer updates (O(1))
- S adds `(k₀, b₀)`: `sumBByKey[k₀]` updates → reactive dependency triggers re-run of mapper for keys that looked up `k₀` → O(1) per affected key

**Comparison: DBToaster vs Skip**

| DBToaster Concept | Skip Primitive | Mechanism |
|-------------------|----------------|-----------|
| Materialized aggregate view | `reduce` | Incremental reducer maintains running total |
| 1st-order delta (ΔR Q) | Reactive `map` | Mapper re-runs when input key changes |
| Higher-order delta (Δ²Q) | Reducer incrementality | Reducer's `add`/`remove` handle deltas directly |
| Delta propagation | Reactive dependencies | `getUnique`/`getArray` lookups create dependencies |
| Ring operations (F-IVM) | Custom reducer | User-defined `add`/`remove` over ring structure |

**What Skip handles well:**
- Standard SQL aggregation queries (SUM, COUNT, AVG over joins)
- Incremental aggregate maintenance via reducers
- Join maintenance via reactive lookups

**Potential limitations vs DBToaster (current status):**
- **Scope of examples:** We only analyze simple join+aggregate patterns (`count(R×S)`, `sum(R.a * S.b)` and close relatives). We do **not** yet handle the full DBToaster query fragment (nested queries, longer join chains, complex polynomials, etc.).
- **Compile-time vs runtime optimization:** DBToaster derives delta expressions symbolically and simplifies them (e.g., recognizing `Δ²Q = constant`). Skip relies on runtime reactivity; it is plausible but unproven that the runtime always realizes the same bounded per-update work for a suitably defined fragment.
- **Complex polynomial factoring:** DBToaster can factor common subexpressions across delta levels; Skip requires manual structuring of factorized state as explicit collections and reducers.
- **Deletes and mixed updates:** The sketches above implicitly assume insert-only workloads. Handling deletes and mixed update patterns with the same asymptotic guarantees requires a more careful treatment of reducer `remove` and dependency invalidation.

**Takeaway and future work:** For the specific patterns above, we can realize the same state structure and per-update work as the corresponding DBToaster view programs using `reduce` + reactive `map` + lookups. Extending this to:
- a precisely defined DBToaster/F-IVM-style query fragment,
- a mechanical translation into Skip graphs, and
- a proof (or counterexamples) that Skip matches the claimed asymptotic update complexity for that fragment

is left as future work.

---

### Example 6.2: F-IVM-style ring-based analytics
**Classification: 🟡 Standard reducer (ring add/subtract)**

Same as sum reducer, but over a ring (could be numbers, polynomials, etc.).

---

### Example 6.3: Dynamic acyclic join (Yannakakis)
**Classification: 🟢 Structural (map with lookups)**

```
Input:  R : A × B          // Relation R(A, B)
        S : B × C          // Relation S(B, C)
        T : C × D          // Relation T(C, D)
Output: Q : (A,B,C,D) × Unit  // Join result Q = R ⋈ S ⋈ T
```

#### Yannakakis-style optimal algorithm (batch view)

An acyclic join is one where the hypergraph of relations (relations as hyperedges, attributes as nodes) forms a tree. For the chain

```
R(A,B) ⋈ S(B,C) ⋈ T(C,D)
```

the Yannakakis algorithm proceeds in two phases:

1. **Semi-join reduction (bottom‑up and top‑down):**
   - Bottom‑up:
     - Replace `S` by `S ⋉ T` (keep only tuples in `S` whose `C` appears in `T`)
     - Replace `R` by `R ⋉ S` (keep only tuples in `R` whose `B` appears in the reduced `S`)
   - Top‑down:
     - Optionally further prune `S` and `T` using reduced `R` (for deeper trees).

   After this phase, every tuple in `R`, `S`, and `T` participates in **at least one** final join result—no dead tuples remain.

2. **Join enumeration (top‑down):**
   - Traverse the join tree, e.g. from `R` outward:
     - For each `(a,b) ∈ R`, enumerate `c` such that `(b,c) ∈ S`, then `d` such that `(c,d) ∈ T`.

For acyclic joins, Yannakakis achieves **worst‑case optimal** complexity

```
O(|R| + |S| + |T| + |Q|)
```

where `Q` is the output, by ensuring that semi‑join reduction never materializes intermediate results larger than the final join.

#### Idiomatic Skip solution: driver relation + indexed lookups

Skip does not (today) expose Yannakakis’ semi‑join phases as primitives. The idiomatic pattern is:

- pick one relation as a **driver** (often the smallest or most selective), and
- perform indexed lookups into the other relations via `getArray` inside a `map`.

Assuming we have eager collections:

- `r : (A,B) → unit`
- `sByB : B → C` (index of `S` on `B`)
- `tByC : C → D` (index of `T` on `C`)

we can express the join as:

```rescript
// Driver-on-R nested-loop join with index lookups into S and T.
let joinResult =
  r->map((a, b, _ctx) => {
    let cs = sByB->getArray(b)         // all c with S(b,c)
    cs->Array.flatMap(c => {
      let ds = tByC->getArray(c)       // all d with T(c,d)
      ds->Array.map(d => ((a, b, c, d), ()))
    })
  })
```

In Skip’s execution model, `getArray` used in a mapper like this creates **reactive dependencies** on `sByB` and `tByC` in addition to the direct dependency on `r`. Intuitively:

- changes to `R` trigger recomputation of only the affected driver tuples; and
- changes to `S` or `T` at keys looked up during previous runs cause the relevant driver tuples to be re‑evaluated.

This realizes a dynamic, **incremental** nested‑loop join: updates to any of `R`, `S`, or `T` only recompute the pieces of `Q` that actually depend on the updated tuples.

#### Why this is not Yannakakis‑optimal

The Skip pattern above is **semantically correct**—it computes exactly `R ⋈ S ⋈ T` and maintains it incrementally—but it does **not** implement Yannakakis’ asymptotically optimal algorithm:

- **No global semi‑join pruning.**
  - Yannakakis performs global semi‑join reduction before any enumeration, guaranteeing that each base relation contains only tuples that appear in the output.
  - The Skip join enumerates from the full (possibly unpruned) `R`, and only *locally* skips when `sByB->getArray(b)` or `tByC->getArray(c)` are empty.

- **Complexity characteristics.**
  - Yannakakis: `O(|R| + |S| + |T| + |Q|)` worst‑case for acyclic joins.
  - Skip pattern: behaves like an **indexed nested‑loop join** driven by `R`. With reasonable indexes, each output tuple is still produced in `O(1)` amortized time, but:
    - if `R` is much larger than the reduced `R ⋉ S ⋉ T`, we still pay a cost proportional to the size of the *unreduced* `R`;
    - there is no global guarantee matching Yannakakis’s tight worst‑case bound.

- **Incremental vs batch focus.**
  - Yannakakis is a **batch** algorithm optimized for one‑shot evaluation.
  - The Skip idiom is optimized for **incremental maintenance** under small updates, leaning on reactivity and indices rather than a global semi‑join phase.

In summary:
- use Yannakakis to reason about optimality for acyclic joins in the abstract;  
- in Skip, the practical pattern is “driver relation + reactive indexed lookups via `map`”, which is structurally simple and incrementally efficient, but not Yannakakis‑optimal in the classical worst‑case sense.

---

### Example 6.4: Counting and DRed-style materialized views
**Classification: 🟡 Standard reducer (count) for non-recursive; 🟣 Compute node for recursive**

```
Input:  Base relations (e.g., Edge(src, dst))
Output: Derived view (e.g., TC(x, y) for transitive closure)
```

#### Requirements Analysis

**Counting-based maintenance** is a technique for incrementally maintaining derived relations:
- Each derived tuple has a **count** of how many ways it can be derived
- Insert: increment count (add new derivation)
- Delete: decrement count; if count reaches 0, remove the tuple
- Works for non-recursive and recursive (with care) rules

**DRed (Delete and Re-derive)** handles recursive rules by:
1. Over-delete: remove anything that *might* be invalidated
2. Re-derive: recompute from remaining base facts
3. Re-insert: restore tuples that are still derivable

#### Case 1: Non-Recursive Rules (Joins, Projections)

For non-recursive views, counting is straightforward.

**Example**: `V(x, y) :- R(x, z), S(z, y)` (join on z)

```rescript
// Each R tuple and S tuple contributes derivations
// For R(x, z) and S(z, y), the derivation count for V(x, y) is:
//   count = (# of z values where both R(x,z) and S(z,y) exist)

// Step 1: Compute join contributions
let derivations = r->map((x, z, ctx) => {
  let sMatches = s->getArray(z)  // All y values
  sMatches->Array.map(y => ((x, y), 1))  // Each match is 1 derivation
})

// Step 2: Sum derivation counts per (x, y)
let viewWithCounts = derivations->reduce(sumReducer)

// Step 3: Filter to positive counts only
let view = viewWithCounts->map(((x, y), count) =>
  if count > 0 { [((x, y), ())] } else { [] }
)
```

**How counting handles deletes:**
- Delete R(x₀, z₀): The mapper no longer emits derivations for this tuple
- Skip's remove semantics subtract these from the sum
- If sum for (x₀, y) drops to 0, the filter removes it

**This is well-formed**: sum reducer is invertible.

#### Case 2: Recursive Rules (Transitive Closure)

**Example**: `TC(x, y) :- Edge(x, y) | (Edge(x, z), TC(z, y))`

This is more complex because:
- TC depends on itself
- A single edge deletion can invalidate many TC tuples
- Simple counting may "leak" (count > 0 but no valid derivation)

**Problem with naive counting:**
```
Edge: (a, b), (b, c)
TC:   (a, b) count=1, (b, c) count=1, (a, c) count=1

Delete Edge(b, c):
- TC(b, c) count becomes 0 ✓
- TC(a, c) count stays 1 (derived via (a,b), TC(b,c))
  But TC(b,c) no longer exists!
```

The count for TC(a, c) is stale — it references a now-invalid TC(b, c).

#### Solution for Recursive: Semi-Naive + DRed

**Approach 1: Full recompute (simple but expensive)**
```rescript
// On any Edge change, recompute TC from scratch
let tcCompute = LazyCompute.make((self, (x, y), ctx, _) => {
  // BFS/DFS from x to find all reachable nodes
  let reachable = computeReachability(edges, x)
  if Set.has(reachable, y) { [()] } else { [] }
})
```

**Approach 2: Stratified with explicit fixpoint**

For transitive closure, we can compute iteratively:
```rescript
// TC^0 = Edge
// TC^{n+1} = TC^n ∪ { (x, y) | Edge(x, z), TC^n(z, y) }
// Repeat until fixpoint

// This requires a fixpoint operator, which is a compute node, not a reducer
let tc = fixpoint(edges, (edges, tc_n) => {
  let direct = edges
  let indirect = edges->map((x, z, ctx) => {
    tc_n->getArray(z)->Array.map(y => ((x, y), ()))
  })
  direct->merge([indirect])
})
```

**Approach 3: Differential Dataflow / DBSP style**

Model changes as weighted deltas:
- +1 for insertion, -1 for deletion
- Iterate until weights stabilize
- Tuples with final weight 0 are not in the result

This is what systems like Materialize and Differential Dataflow do.

```rescript
// Each tuple has a weight (int)
// tc : (X, Y) → int

// Base case: edge weights
let tcBase = edges->map((x, y) => ((x, y), 1))

// Recursive case: propagate weights
let tcStep = (tc_n) => {
  let indirect = edges->map((x, z, ctx) => {
    // Sum of weights of TC tuples reachable via this edge
    let contributions = tc_n->getArray(z)
    contributions->Array.map(y => ((x, y), 1))  // Simplified; real impl sums weights
  })->reduce(sumReducer)
  
  tcBase->merge([indirect])->reduce(sumReducer)
}

// Iterate tcStep until fixpoint
let tc = fixpoint(tcStep, tcBase)
```

**This requires a `fixpoint` primitive** that iterates until no changes.

#### Verdict

| Rule Type | Solution | Classification |
|-----------|----------|----------------|
| Non-recursive (join, filter, project) | Counting via sum reducer | 🟡 Standard reducer |
| Linear recursive (single recursive call) | Counting may work with care | 🟠 Enriched |
| General recursive (transitive closure) | Fixpoint / differential | 🟣 Compute node |

**For non-recursive views**: Use `map` + `reduce(sum)` — derivation counting is just summation.

**For recursive views**: Need a `fixpoint` primitive or differential dataflow semantics.

**Primitives needed:**
- Non-recursive: `map`, `reduce` (sum)
- Recursive: `fixpoint` operator (new primitive)

---

### Example 6.5: Differential dataflow / DBSP weighted collections
**Classification: 🟡 Standard reducer (weighted sum)**

Each update is weighted (+1/-1). Reducer tracks sum of weights; zero weight → remove.

---

### Example 6.6: Incremental graph metrics (degree, rank)
**Classification: 🟡 Standard reducer**

Degree: count reducer
Rank contributions: sum reducer

---

### Example 6.7: Iterative graph algorithms with fixpoints
**Classification: 🟣 Compute node (requires iteration) — Fundamentally not a reducer**

```
Input:  edges : EdgeId × (src: NodeId, dst: NodeId, weight?: float)
        seeds : NodeId × InitialValue  (e.g., source node for SSSP)
Output: state : NodeId → Value  (e.g., shortest distance from source)
```

#### Requirements Analysis

Many graph algorithms are iterative:
- **SSSP (Single-Source Shortest Path)**: Propagate minimum distances until stable
- **PageRank**: Propagate rank fractions until convergence
- **Label Propagation**: Propagate labels until communities stabilize
- **BFS**: Propagate "reached" status level by level

These share a common structure:
1. Initialize node states (e.g., distance = ∞ except source = 0)
2. Repeatedly update: `state'[v] = f(state[u] for u in neighbors(v))`
3. Stop when `state' = state` (fixpoint)

#### Why This Is Not a Reducer

A reducer folds a **multiset** into a value:
```
reduce([v₁, v₂, v₃], init, ⊕) = ((init ⊕ v₁) ⊕ v₂) ⊕ v₃
```

Graph algorithms require **iteration over the same data** until convergence:
```
iterate(state₀, step) = state₀ if step(state₀) = state₀
                      = iterate(step(state₀), step) otherwise
```

The "input" to each step is the **previous state**, not a multiset of values. This is fundamentally different from a fold.

#### Solution 1: LazyCompute with Recursion (Per-Query)

For on-demand queries, use `LazyCompute` that recursively explores:

```rescript
// SSSP: compute shortest path from source to target on demand
let shortestPath = LazyCompute.make((self, (source, target), ctx, _) => {
  if source == target {
    [0.0]  // Distance to self is 0
  } else {
    // Find all edges into target
    let inEdges = edgesByDst->getArray(target)
    
    if Array.length(inEdges) == 0 {
      [infinity]  // No path
    } else {
      // Min over all predecessors
      let distances = inEdges->Array.map(((src, weight)) => {
        let srcDist = self->getUnique((source, src), ~ifNone=infinity)
        srcDist +. weight
      })
      [Array.reduce(distances, infinity, min)]
    }
  }
})
```

**Problem**: This can have infinite recursion for graphs with cycles!

For DAGs, this works. For general graphs, need cycle detection or bounded iteration.

#### Solution 2: Bounded Iteration with Explicit Rounds

Model iteration explicitly with round numbers:

```rescript
// state[round][node] = best known value at round r
// Final answer is state[maxRounds][node]

// Round 0: initial state
let state0 = seeds  // source node has distance 0, others have infinity

// Round r+1: one step of relaxation
let relaxStep = (stateR: Collection<NodeId, float>) => {
  // For each edge (u, v, w), emit candidate distance for v
  let candidates = edges->map((_, (src, dst, weight), ctx) => {
    let srcDist = stateR->getUnique(src, ~ifNone=infinity)
    (dst, srcDist +. weight)
  })
  
  // Merge with previous state and take min
  let withPrev = candidates->merge([stateR])
  withPrev->reduce(minReducer)
}

// Apply relaxStep N times (N = number of nodes for Bellman-Ford)
let state1 = relaxStep(state0)
let state2 = relaxStep(state1)
// ... manually unroll or use a helper
let stateN = relaxStep(stateN-1)
```

**Trade-offs:**
- ✅ Works for any graph (with enough rounds)
- ✅ Each round is a standard Skip computation
- ❌ Must know maximum rounds in advance
- ❌ Does N rounds even if converged earlier
- ❌ Creates N copies of state collection

#### Solution 3: External Fixpoint Driver

Use an external process to drive iteration:

```typescript
async function computeFixpoint(broker, maxIters: number) {
  let changed = true;
  let iter = 0;
  
  while (changed && iter < maxIters) {
    // Read current state
    const state = await broker.getAll("nodeState", null);
    
    // Compute one relaxation step externally
    const newState = computeRelaxationStep(state, edges);
    
    // Check for convergence
    changed = !statesEqual(state, newState);
    
    if (changed) {
      // Write new state back to Skip
      await broker.update("nodeState", newState);
    }
    
    iter++;
  }
}
```

**Trade-offs:**
- ✅ Flexible: can implement any convergence criterion
- ✅ Skip handles reactive propagation within each step
- ❌ Iteration logic is outside Skip
- ❌ Round-trips between Skip and external process

#### Solution 4: Native Fixpoint Primitive (Hypothetical)

If Skip had a native `fixpoint` operator:

```rescript
// Hypothetical fixpoint primitive
let finalState = fixpoint(
  ~initial = seeds,
  ~step = (stateR) => {
    let candidates = edges->map((_, (src, dst, weight), ctx) => {
      let srcDist = stateR->getUnique(src, ~ifNone=infinity)
      (dst, srcDist +. weight)
    })
    candidates->merge([stateR])->reduce(minReducer)
  },
  ~converged = (stateR, stateR') => stateR == stateR'
)
```

This would require:
- Skip to iterate internally
- Convergence detection
- Handling of non-termination (max iterations)

#### Solution 5: Differential Dataflow / Timely Dataflow

Systems like Differential Dataflow handle iteration natively:
- Each "timestamp" is (round, time)
- Updates propagate through rounds automatically
- Convergence is detected when no updates for higher rounds

This is the most powerful approach but requires a different execution model.

#### Case Study: PageRank

```rescript
// PageRank: rank[v] = (1-d)/N + d * sum(rank[u]/degree[u] for u → v)

// Step function
let pageRankStep = (ranks: Collection<NodeId, float>, d: float, n: int) => {
  // Each node distributes its rank equally to outgoing neighbors
  let contributions = edges->map((_, (src, dst), ctx) => {
    let srcRank = ranks->getUnique(src, ~ifNone=1.0 /. float(n))
    let srcDegree = outDegree->getUnique(src, ~ifNone=1)
    (dst, srcRank /. float(srcDegree))
  })
  
  // Sum contributions per node
  let sumContribs = contributions->reduce(sumReducer)
  
  // Apply damping factor
  sumContribs->map((node, contrib) => (node, (1.0 -. d) /. float(n) +. d *. contrib))
}

// Need to iterate pageRankStep until convergence
```

#### Verdict

**Iterative graph algorithms fundamentally require a fixpoint/iteration primitive** that Skip's current model doesn't provide as a built-in.

**Options in decreasing order of Skip integration:**

| Approach | Integration | Complexity | Flexibility |
|----------|-------------|------------|-------------|
| LazyCompute (DAGs only) | High | Low | Limited |
| Bounded iteration | High | Medium | Fixed rounds |
| External driver | Medium | Medium | Full |
| Native fixpoint primitive | Would be high | Would be low | Full |

**Recommendation for the calculus**: Add a `fixpoint` primitive:
```
fixpoint : (Collection K V → Collection K V) → Collection K V → Collection K V
```

This allows expressing iterative algorithms while keeping them within the reactive framework.

**Primitives needed:** `fixpoint` (new), or `LazyCompute` for DAG-only cases

---

## Section 7: Business Metrics and UI-Composed Summaries

### Example 7.1: Business KPIs
**Classification: 🟡 Standard reducers (count, sum)**

All three KPIs are map + sum/count reducers.

---

### Example 7.2: Streaming analytics dashboard
**Classification: 🟡 Standard + 🟠 Enriched reducers**

- Throughput: count reducer
- Error counts: map (filter) + count reducer  
- Error rates: enriched (errors, total) reducer + map (project ratio)

---

### Example 7.3: UI-derived business metrics
**Classification: 🟡/🟠 Standard/enriched reducers**

- Cart totals: sum reducer
- Average rating: enriched (sum, count) reducer

---

### Example 7.4: Composite metrics and conversion funnels
**Classification: 🟠 Enriched reducer OR 🟢 Structural + arithmetic**

Per-stage counts could be:
- Distinct count reducer per stage, OR
- Structural: group by stage, then count (if each user appears once per stage)

Funnel ratios: map over the per-stage counts to compute division.

---

## Summary Table (Revised After Detailed Analysis)

| Category | Examples | 🟢 Structural | 🟡 Standard | 🟠 Enriched | 🔴 Partial | 🟣 Compute |
|----------|----------|---------------|-------------|-------------|------------|------------|
| **1. Simple Per-Key** | 13 | 0 | 10 | 0 | 2 (min/max) | 0 |
| **2. Enriched-State** | 9 | 1 (top-K)† | 1 | 5 | 2 | 0 |
| **3. Set/Index** | 4 | 2 | 0 | 2 | 0 | 0 |
| **4. Windowed/Session** | 7 | 1 (count-based)† | 5 | 0 | 1 | 0 |
| **5. History/Undo** | 4 | 0 | 2 (epoch-based)† | 0 | 0 | 2 |
| **6. Graph/Relational** | 7 | 1 (joins)† | 4 | 0 | 0 | 2 |
| **7. Business/UI** | 4 | 0 | 3 | 1 | 0 | 0 |
| **TOTAL** | 48 | **5** | **25** | **8** | **5** | **4** |

† = reclassified after detailed analysis (simpler solution found)

---

## Key Findings (Revised)

### 1. Many "complex" examples have simple solutions

After detailed analysis, several examples originally classified as complex turned out to have simpler solutions:

| Example | Original | Revised | Key Insight |
|---------|----------|---------|-------------|
| Top-K | 🔴 Partial | 🟢 Structural | Use key ordering, no reducer needed |
| Acyclic joins | 🟣 Compute | 🟢 Structural | `map` with context lookups |
| Resettable accumulator | 🟣 Compute | 🟡 Standard | Epoch-based keys |
| Sliding window avg | 🔴 Partial | 🟡 Standard | External eviction (Skip idiom) |

**Pattern**: Before reaching for complex primitives, check if the problem can be transformed into a simpler one.

### 2. Standard reducers cover >50% of examples

**~52% of examples** use only **standard reducers** (count, sum). These are:
- Fully invertible: `add(acc, v)` and `remove(acc, v) = add(acc, -v)`
- No state beyond a single value
- Perfect candidates for built-in reducer primitives in the calculus

### 3. Structural operators are more powerful than expected

**~10% of examples** can be solved with **structural operators only** (`map`, `slice`, `take`, `merge`):
- Inverted indices (re-keying)
- Top-K (key ordering + take)
- Joins (map with lookups)
- Count-based windows (slice + take)

**Key insight**: Skip's key ordering (`≤₍json₎`) and multi-valued collections provide powerful query capabilities without reducers.

### 4. Enriched reducers follow clear patterns

The **~17%** of examples needing enriched state cluster around a few patterns:
- `(sum, count)` for average/weighted average
- `Map<V, int>` for frequency/distinct count/histogram
- `(min, second, count)` for robust min/max

**Pattern**: The calculus should provide combinators to build these from primitives.

### 5. True compute nodes are rare but necessary

Only **~8%** of examples genuinely require compute nodes:
- **Undo/redo history**: Sequential, non-commutative
- **Recursive queries**: Transitive closure, fixpoint algorithms

These share a characteristic: **they cannot be expressed as commutative folds**.

**Pattern**: The calculus needs a `fixpoint` primitive for recursive queries, but undo/redo may be best handled outside the reactive system.

### 6. The Skip idiom: external processes for temporal concerns

Several examples (sliding windows, session management, undo/redo) are simplest when:
- Skip handles the **reactive aggregation**
- An external process handles **temporal concerns** (eviction, epochs, command ordering)

This separation of concerns keeps reducers simple and well-formed.

---

## Proposed Calculus Primitives (Revised)

Based on the detailed analysis, the calculus should include:

### Tier 1: Structural Operators (no reducer needed)

These are surprisingly powerful and should be the first tool considered.

```
map      : Collection K V → (K × Values V × Context → [(K', V')]) → Collection K' V'
slice    : Collection K V → K → K → Collection K V
slices   : Collection K V → [(K, K)] → Collection K V
take     : Collection K V → int → Collection K V
merge    : [Collection K V] → Collection K V

// Derived operations (can be built from above)
filter   : Collection K V → (K × V → bool) → Collection K V        // map that conditionally emits
rekey    : Collection K V → (K × V → K') → Collection K' V          // map that changes key
project  : Collection K V → (V → V') → Collection K V'              // map that changes value
lookup   : Collection K V → K → Values V                            // context access in mappers
```

**Key insight from analysis**: Many "aggregation" problems are actually **key design** problems:
- Top-K → Key by `(group, -score, id)`, use `take`
- Inverted index → Swap key and value with `rekey`
- Joins → `map` with `lookup` into other collections

### Tier 2: Standard Reducers (built-in, well-formed)

```
count    : WFReducer V int
sum      : WFReducer Number Number
```

These two cover >50% of examples. They are:
- Trivially well-formed (commutative, invertible)
- Should be built-in primitives

```
min      : Reducer Ord Ord    // NOT well-formed without enrichment
max      : Reducer Ord Ord    // NOT well-formed without enrichment
```

**Decision**: Classify min/max as `PartialReducer` or require enriched versions.

### Tier 3: Reducer Combinators (preserve well-formedness)

```
product  : WFReducer V₁ A₁ → WFReducer V₂ A₂ → WFReducer (V₁, V₂) (A₁, A₂)
// (r₁ × r₂).add((a₁,a₂), (v₁,v₂)) = (r₁.add(a₁,v₁), r₂.add(a₂,v₂))

mapInput : (V' → V) → WFReducer V A → WFReducer V' A
// Precompose input transformation

mapOutput : (A → B) → WFReducer V A → WFReducer V B
// Postcompose output transformation (for projection only, not in the reducer itself)

groupBy  : (V → K') → WFReducer V A → WFReducer V (Map K' A)
// Per-bucket aggregation within each key
```

**Derivation of average:**
```
average = mapOutput((sum, count) => sum / count, product(sum, count))
```

### Tier 4: Enriched State Patterns (derived from Tier 3)

```
average      = product(sum, count) + projection
weightedAvg  = product(sumWeights, sumWeightedValues) + projection
freqMap      = groupBy(identity, count)              // Map<V, int>
histogram    = groupBy(bucket, count)                // Map<BucketId, int>
distinctCount = freqMap + mapOutput(Map.size)

// Enriched min/max (partially well-formed)
enrichedMin  : WFReducer Ord (Ord, Ord, int)  // (min, secondMin, countOfMin)
// Still partial if all min values removed AND no secondMin exists
```

### Tier 5: Non-Reducer Primitives

```
// On-demand computation (for complex per-key logic)
lazyCompute  : (Self × K × Context → [V]) → LazyCollection K V

// Iteration to fixpoint (for recursive queries)
fixpoint     : (Collection K V → Collection K V) → Collection K V → Collection K V

// External state (for temporal/sequential concerns)
external     : ExternalResource → Collection K V
```

**When to use each:**
| Primitive | Use Case |
|-----------|----------|
| `lazyCompute` | Complex per-key computation (e.g., SSSP on DAG) |
| `fixpoint` | Recursive queries (transitive closure, PageRank) |
| `external` | Temporal logic (window eviction), sequential operations (undo/redo) |

---

## Design Principles (from Analysis)

### 1. Prefer structural solutions

Before using a reducer, check:
- Can the problem be solved by **choosing the right key structure**?
- Can `slice`/`take` provide the filtering needed?
- Does Skip's multi-valued collection model already give the answer?

### 2. The Skip idiom for time

Skip excels at **reactive aggregation**. For **temporal concerns**:
- External process manages time (eviction, epochs)
- Skip manages reactivity (aggregation, propagation)
- Communication via collection updates

### 3. Epoch-based keys for reset semantics

When "reset" is needed, **don't reset the accumulator**—start a new one:
```
key = (originalKey, epoch)
epoch = count of resets
```

### 4. Joins are maps with lookups

Skip's reactive model makes joins natural:
```
join = baseRelation->map((key, value, ctx) => {
  otherRelation->lookup(joinKey)->map(...)
})
```

### 5. Reserve compute nodes for true non-commutativity

Only use `lazyCompute`/`fixpoint` when:
- Order matters (undo/redo) — consider external state machine
- Iteration is required (recursive queries) — use `fixpoint`
- Per-query computation is complex — use `lazyCompute`

---

## Next Steps

1. **Formalize Tier 2 reducers** (count, sum) with well-formedness proofs
2. **Prove combinator closure** (Tier 3): product, mapInput, mapOutput preserve WF
3. **Implement enriched patterns** (Tier 4) as library code using combinators
4. **Design fixpoint semantics** for recursive queries (Tier 5)
5. **Document the Skip idiom** for temporal concerns (external + reactive)
6. **Implement example services** using only Tier 1-4 to validate expressiveness
