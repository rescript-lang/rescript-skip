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

Additional standard type constructors:

- Products `A₁ × A₂`, sums, and perhaps function spaces as needed.
- Simple collection‑level operators: `map`, `slice`, `merge`, etc., which are algebraically straightforward.

## 3. Well‑formedness as a typing judgement

In the paper, well‑formedness is a semantic property of `R = (ι, ⊕, ⊖)`:

- `⊕` must be pairwise‑commutative (multiset fold is independent of order).
- `⊖` must be a left inverse of `⊕` on reachable accumulator states (the main theorem’s condition).

In the calculus, this can become an explicit judgement:

- `Γ ⊢ R : Reducer V A` – `R` is syntactically a reducer.
- `Γ ⊢ R : WFReducer V A` – `R` is well‑formed; it satisfies the semantic correctness law.
- Optionally, `Γ ⊢ R : PartialReducer V A` – `R` may fall back to recomputation.

The goal is to arrange the rules so that:

- Base primitives are declared well‑formed by assumption.
- Combinators on reducers *preserve* well‑formedness, so complex reducers built from well‑formed pieces remain well‑formed automatically.

## 4. Algebra of reducers

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
  - E.g., going from `min` over `ℝ` to a reducer over a richer state `(min, secondMin, count)` that makes the remove operation invertible.
  - The calculus could expose generic combinators for pairing a reducer with auxiliary state, where the corresponding closure rule tracks whether invertibility is preserved.

Each such operation comes with a small metatheorem: if the premises are well‑formed, the result is well‑formed. Together, they give a “good by construction” algebra of reducers.

## 5. Complexity annotations

In the current paper, well‑formedness implies a complexity contract: under the Skip semantics, well‑formed reducers admit `O(1)` per‑key updates.

The calculus could refine the typing judgement to track complexity:

- `Γ ⊢ R : WFReducer[V, A, O(1)]`
- `Γ ⊢ R : PartialReducer[V, A, fallback]`

and give rules such as:

- Product of two `O(1)` reducers is `O(1)`.
- Product of an `O(1)` reducer with a partial reducer is partial.

This turns the calculus into a discipline not just for correctness but also for incremental performance guarantees.

## 6. Expressivity and examples

A key research question is: how expressive can such a calculus be while keeping the rules simple and checkable?

Potential sources of “real” reducers to test expressivity:

- Existing Skip service graphs: per‑key metrics, dashboards, alerts.
- Streaming/windowed analytics: counts, sums, averages, histograms, per‑session stats.
- Domain‑specific examples: incremental graph metrics, per‑user quotas, shopping carts, etc.

The hypothesis is that:

- A small set of primitive well‑formed reducers (sum, count, min/max with enriched state, average with (sum,count) state, etc.), plus algebraic combinators (product, mapping, grouping), may cover a large fraction of real‑world reducers used in reactive back‑ends.
- Systematically validating this hypothesis is future work.

## 7. User‑facing layer

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
