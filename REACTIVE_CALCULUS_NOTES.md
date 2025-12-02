# Towards a Reactive Calculus

This note sketches a possible “reactive calculus” that could sit underneath Skip’s combinators for building reactive views.
Reducers are the most algebraically subtle part of this story, so they get most of the attention here, but the intent is not to express everything as a reducer—only to make the complex pieces *good by construction* rather than something users or authors must prove case‑by‑case.

It is intentionally informal and future‑looking; the goal is to capture design directions, not to fix a concrete formal system yet.

## 1. Core vision

- A small, typed calculus of *reactive combinators* for building views:
  - collections as first‑class values, and
  - reducers as structured, reusable update operators on those collections.
- Well‑formedness of reducers is enforced by typing rules and algebraic closure properties.
  - Every reducer term that type‑checks in the calculus either:
    - is guaranteed to satisfy the Skip well‑formedness law, or
    - is explicitly classified as partial / “fallback to recompute”.
- The calculus plays the same role for reactive views that:
  - relational algebra plays for SQL, and
  - change structures / incremental λ‑calculus play for derivative‑based incrementalization.

## 2. Basic semantic types

At the semantic level, the calculus works with the same objects as the paper:

- `Multiset V` (`𝓜(V)`): finite multisets over values `V`, with union `⊎` and multiset difference.
- `Collection K V`: functions `K → 𝓜(V)`; this is the semantic type for Skip collections.
- `Reducer V A`: triples `R = (ι, ⊕, ⊖)` with:
  - `ι : A` – initial accumulator,
  - `⊕ : A × V → A` – add,
  - `⊖ : A × V → A` or partial `A × V → A + {⊥}` – remove.

A reducer is *well‑formed* when its operations satisfy the Skip laws:

- **pairwise commutativity** of add/remove steps:
  `(a ⊕ v₁) ⊕ v₂ = (a ⊕ v₂) ⊕ v₁`,
  `(a ⊖ v₁) ⊖ v₂ = (a ⊖ v₂) ⊖ v₁`,
  `(a ⊕ v₁) ⊖ v₂ = (a ⊖ v₂) ⊕ v₁`
  (order‑independence of folding adds/removes);
- **invertibility law**:
  `(a ⊕ v) ⊖ v = a`
  (removing a just‑added value restores the previous state).

Section 4 turns these semantic properties into explicit typing judgements (`WFReducer` vs `PartialReducer`).

Additional standard type constructors:

- Products `A₁ × A₂`, sums, and perhaps function spaces as needed.
- Simple collection‑level operators: `map`, `slice`, `merge`, etc., which are algebraically straightforward.

## 3. Core reactive building blocks

Before focusing on reducers, we surface the building blocks exposed in the Skip bindings (`EagerCollection`, `LazyCollection`, `Mapper`, `Reducer`, `LazyCompute`, external resources).
The calculus should make these first‑class and encourage a simple rule: use the simplest tool that works; reach for reducers only when necessary.

### 3.1 Structural collection operators

At the collection level, many common view patterns need no per‑key state at all; they are purely structural.
In the Skip bindings, keys `K` are JSON values (`Json` in the TypeScript API):

- booleans, numbers, strings,
- arrays of JSON or `null`,
- objects mapping string keys to JSON or `null` values.

For the calculus and examples, we fix some lightweight notation:

- finite JSON arrays are written `[v₁, …, vₙ]`, where each `vᵢ` is a JSON value or `null`;
- JSON objects are finite maps from strings to JSON, written either
  `{k₁ ↦ v₁, …, kₙ ↦ vₙ}` or `{"k₁": v₁, …, "kₙ": vₙ}`,
  with the understanding that object keys are always strings.

For the calculus we assume a fixed total order `≤₍json₎` on JSON values in order to talk about ranges and prefixes.

The order `≤₍json₎` is defined as follows:
- Values are partitioned by JSON type (shape): `null <₍json₎ booleans <₍json₎ numbers <₍json₎ strings <₍json₎ arrays <₍json₎ objects`.
- Within each type:
  - `null`: there is a single value `null`.
  - Booleans: `false <₍json₎ true`.
  - Numbers: ordered by numeric value (standard `<` on ℝ).
  - Strings: ordered lexicographically.
  - Arrays: ordered lexicographically by comparing elements from left to right; shorter arrays precede longer arrays when one is a prefix of the other.
  - Objects: ordered lexicographically by comparing key‑value pairs `(k, v)` where keys are compared first (as strings), then values; objects with fewer keys precede objects with more keys when one's keys are a subset of the other's.

**Comparison with JavaScript sorting.** Operations like `getAll`, `slice`, and `take` return entries ordered by `≤₍json₎`. JavaScript has no built‑in total order on JSON values:
- `Array.sort()` with no comparator coerces elements to strings, so `[1, 10, 2]` sorts as `[1, 10, 2]` (string order), not `[1, 2, 10]`.
- Mixed types have inconsistent behaviour: `null < 0` is `false`, `true < 2` is `true` (coerces to `1 < 2`).
- Arrays and objects cannot be compared with `<`; they coerce to strings.

In practice, JS developers work around this by sorting homogeneous data (all numbers, all strings) or writing custom comparators for specific object shapes. Libraries like Lodash provide `_.sortBy(collection, iteratee)` to sort by a derived key, but not a general‑purpose total order on arbitrary JSON.

The one exception in the web platform is **IndexedDB**, which defines a key ordering: `number < Date < string < binary < array` (with arrays compared lexicographically). This is similar in spirit to `≤₍json₎`, though the type ordering and supported types differ.

> **Known issue (to be fixed):** The current WASM binding serializes booleans as numbers (0/1) when exporting to JavaScript. This does not affect the runtime's internal ordering or key identity—only the JavaScript representation.

- `map : Collection K V → Collection K' V'` (entry‑wise transformation): apply a mapping function to each `(key, values)` group, possibly changing keys and values.
- `slice : Collection K V × K × K → Collection K V` (key range): given `start, end : K`, keep only entries whose keys lie between `start` and `end` in the runtime's key order.
- `slices : Collection K V × (K × K) list → Collection K V` (multi‑range): keep entries whose keys lie in at least one of a finite set of such ranges.
- `take : Collection K V × int → Collection K V` (prefix): keep the first `n` entries in the runtime's key order.
- `merge : (Collection K V) list → Collection K V` (union): combine a finite family of collections so that at each key the values are the multiset union of values from all inputs.

These operators:

- are total and order‑insensitive by construction,
- do not maintain additional state beyond their inputs, and
- introduce no new well‑formedness obligations beyond typing.

In the calculus, they form the “always safe” fragment: compositional operators on `Collection K V` that can be freely combined without thinking about reducer laws.

### 3.2 Per‑key aggregation views

Per‑key aggregation is where `Reducer V A` enters the picture.
Given a collection `Collection K V`, a reducer accumulates all values at a given key into an accumulator of type `A`.
Skip's API exposes this via `EagerCollection.reduce` and `EagerCollection.mapReduce`.

Typical examples include:

- counts, sums, min/max, and other numeric aggregates,
- enriched accumulators like `(sum, count)` for averages, or `(min, secondMin, count)` for robust minima,
- small per‑key summaries (e.g. flags, bounded histograms) that can be updated incrementally.

At this level, a reducer is the triple `(ι, ⊕, ⊖)` used to fold per‑key multisets.
The key pragmatic principle:

- Express a view as a structural operator (`map`, `slice`, `merge`, …) plus a simple, standard reducer on a small accumulator.
- Use more exotic reducers only when simple ones are not expressive or efficient enough.

The more delicate algebraic laws (well‑formedness, complexity) are introduced in later sections.

### 3.3 Lazy and external compute nodes

Some views are not naturally expressed as a single per‑key reducer, even with enriched state:

- they may depend on global structure (graphs, fixpoints, cross‑key relationships), or
- they may be sourced from or delegated to external systems.

The bindings reflect this via:

- `LazyCollection` / `LazyCompute`: on‑demand views computed by a function `compute : (LazyCollection K V, key, context, params) → array V`, and
- `Context.useExternalResource`: eager collections backed by external services or APIs.

In the reactive calculus, these are best modelled as *compute nodes* in the graph rather than as reducers:

- they consume one or more collections and produce a new collection,
- they are specified by a semantic contract (“this node computes X from its inputs”) rather than reducer laws,
- they may internally run iterative or graph algorithms (as in the DCE case study).

The calculus distinguishes:

- the **reducer fragment**, where well‑formedness and incremental complexity are controlled algebraically, from
- the **compute fragment** for nodes specified relationally or operationally but not necessarily as invertible reducers.

### 3.4 “Simplest tool that works” hierarchy

Putting these pieces together suggests a pragmatic hierarchy for building reactive views:

1. **Structural operators on collections** (`map`, `slice`, `slices`, `take`, `merge`, key/value remapping).
2. **Standard per‑key reducers** (sum, count, min/max, simple enriched accumulators).
3. **Custom/enriched reducers** when the accumulator needs more structure for incremental performance or invertibility.
4. **Compute nodes and external resources** (lazy computes, graph algorithms, remote services) when the logic is global or not reducer‑like.

The rest of the note focuses on (2) and (3), developing an algebra and type system for reducers, but should be read in the context of this wider toolkit.
In practice, most Skip views are built from (1) and (2), reserving (3) and (4) for more complex cases.

## 4. Well‑formedness as a typing judgement

In the paper, well‑formedness is a semantic property (the laws from Section 2).
In the calculus, this becomes an explicit typing judgement:

- `Γ ⊢ R : Reducer V A` – `R` is syntactically a reducer.
- `Γ ⊢ R : WFReducer V A` – `R` is well‑formed; it satisfies the semantic correctness law.
- Optionally, `Γ ⊢ R : PartialReducer V A` – `R` may fall back to recomputation.

The goal is to arrange the rules so that:

- Base primitives are declared well‑formed by assumption.
- Combinators on reducers *preserve* well‑formedness, so complex reducers built from well‑formed pieces remain well‑formed automatically.

These judgements are specific to the reducer fragment.
Structural collection operators (Section 3.1) and compute nodes (Section 3.3) are constrained by their own semantic contracts and do not need to satisfy the Skip reducer laws.

## 5. Algebra of reducers

Within the broader reactive calculus, we can turn common constructions on reducers into typed combinators, along lines such as:

- **Product of reducers**
  - Given `Γ ⊢ R₁ : WFReducer V A₁` and `Γ ⊢ R₂ : WFReducer V A₂`,
  - define `R₁ ⊗ R₂ : WFReducer V (A₁ × A₂)` with
    - `(ι₁, ⊕₁, ⊖₁)` and `(ι₂, ⊕₂, ⊖₂)` combined componentwise.
  - The calculus includes a rule stating that `⊗` preserves well‑formedness.

- **Mapping value types**
  - Given a function `f : V' → V` and `Γ ⊢ R : WFReducer V A`,
  - define `mapValue f R : WFReducer V' A`, which simply pre‑composes inputs with `f`.

- **State enrichment / refinement**
  - E.g., going from `min` over `ℝ` to a reducer over richer state `(min, secondMin, count)` that makes the remove operation invertible.
  - Generic combinators could pair a reducer with auxiliary state, with closure rules tracking whether invertibility is preserved.

Each such operation comes with a small metatheorem: if the premises are well‑formed, the result is well‑formed. Together, they give a “good by construction” algebra of reducers.

## 6. Complexity annotations

In the current paper, well‑formedness implies a complexity contract: under the Skip semantics, well‑formed reducers admit `O(1)` per‑key updates.

The calculus could refine the typing judgement to track complexity:

- `Γ ⊢ R : WFReducer[V, A, O(1)]`
- `Γ ⊢ R : PartialReducer[V, A, fallback]`

and give rules such as:

- Product of two `O(1)` reducers is `O(1)`.
- Product of an `O(1)` reducer with a partial reducer is partial.

This turns the calculus into a discipline not just for correctness but also for incremental performance guarantees.

## 7. Expressivity and examples

A key research question is: how expressive can such a calculus be while keeping the rules simple and checkable?

Potential sources of “real” reducers to test expressivity:

- Existing Skip service graphs: per‑key metrics, dashboards, alerts.
- Streaming/windowed analytics: counts, sums, averages, histograms, per‑session stats.
- Domain‑specific examples: incremental graph metrics, per‑user quotas, shopping carts, etc.

The file `examples_all.tex` collects a concrete catalogue of such examples, organized into:

- **Simple per‑key aggregates** (counts, sums, min/max), which map directly to per‑key well‑formed reducers (`Reducer V A` plus grouping).
- **Enriched‑state views** (averages, min/max with witnesses, multi‑field KPIs) corresponding to the "state enrichment / refinement" patterns in Section 5.
- **Set/index views** (distinct counts, membership sets, secondary indexes) that highlight when reducers should be classified as partial (e.g. recomputing a set on delete) versus fully invertible.
- **Windowed/session views** that are algebraically simple once a window identifier is part of the key, but which rely on external “window management” logic to decide when keys appear or expire.
- **History/ordered‑state patterns** where accumulators store ordered structures (logs, top‑k, last‑N), often trading invertibility for expressive power and landing in the `PartialReducer` fragment.
- **Graph and relational incremental views** (joins, reachability, fixpoint‑style algorithms) that typically decompose into:
  - one or more invertible reducers over base collections (e.g. maintaining edge sets or adjacency maps), and
  - a higher‑level incremental algorithm or fixpoint scheduler.
- **Business/UI‑composed summaries** that combine multiple reducer‑backed resources with simple pointwise arithmetic or logical combinations.

The catalogue serves as a stress‑test for the calculus design:

- Most "everyday analytics" examples fall cleanly into the `WFReducer` fragment, possibly with enriched state.
- Windowing and history views suggest lightweight primitives at the key/type level (time buckets, sequence numbers) rather than fundamentally new reducer laws.
- Graph/relational and iterative examples (including reactive DCE, see Section 9) motivate a *layered* approach:
  - base collections and indices are maintained by well‑formed reducers, and
  - global algorithms are expressed as separate reactive nodes that consume these collections rather than as single monolithic reducers.

Most examples stay in the structural + standard‑reducer fragment (hierarchy from Section 3.4), with only a minority needing custom reducers or general compute nodes.

The hypothesis is that:

- A small set of primitive well‑formed reducers (sum, count, min/max with enriched state, average with (sum,count) state, etc.), plus algebraic combinators (product, mapping, grouping), may cover a large fraction of real‑world reducers used in reactive back‑ends.
- Systematically validating this hypothesis is future work.

## 8. User‑facing layer

The calculus is intended as a foundation, not necessarily the surface language.

Two possible user‑facing stories:

- **Embedded combinator library**
  - Export the calculus directly as a small set of combinators in ReScript/TypeScript (e.g., `Reducer.product`, `Reducer.mapValue`, etc.).
  - Developers build reducers using these combinators; the type system and library design ensure well‑formedness and known complexity where advertised.

- **Higher‑level “view query” DSL**
  - Define a more intuitive DSL for derived views, analogous to SQL over collections.
  - The compiler lowers this DSL into terms of the reactive calculus, choosing specific reducer constructions.
  - Correctness and complexity guarantees are inherited from the calculus, just as SQL inherits guarantees from relational algebra.

In both cases, the long‑term goal is that:

- Developers mostly compose *well‑formed* reducers using high‑level constructs.
- The runtime’s correctness theorem applies automatically to anything expressible in the calculus (or in the DSL compiled to it).
- Only a small, clearly marked “escape hatch” is needed for ad‑hoc reducers that fall outside the calculus, and those carry explicit “partial / may recompute” semantics.

## 9. Case study: reactive DCE and graph views

The LaTeX note `dce_reactive_view.tex` and Lean artefacts (`lean-formalisation/Reduce.lean`, `lean-formalisation/DCE.lean`) provide a worked example: online dead‑code elimination over a distributed program graph.

The design there is intentionally two‑layered:

- **Layer 1: graph aggregation as an invertible reducer.**
  - Each file contributes a fragment `(nodes, roots, edges)`; fragments live in a multiset.
  - A reducer over fragments maintains global multisets of nodes, roots, and edges:
    `G ⊕ f` adds the fragment componentwise; `G ⊖ f` subtracts it.
  - Using multisets makes `⊕`/`⊖` pairwise‑commutative and ensures `(G ⊕ f) ⊖ f = G`.
    This instantiates a `WFReducer` (Section 4) whose well‑formedness is proved in `reduce.tex` and the Lean files.

- **Layer 2: incremental liveness as a graph algorithm.**
  - Given the aggregated graph `G`, the view partitions nodes into live vs. dead.
  - An incremental algorithm maintains:
    - a live set, and
    - per‑node refcounts for incoming edges from live predecessors.
  - It updates on each graph delta by BFS‑style propagation and "cascade‑death" when refcounts hit zero.
  - This logic is *not* an invertible reducer: it relies on full graph state and involves fixpoint‑like propagation.
    Its state is specified relationally (reachability from roots) and proved delta‑bounded in Lean.
