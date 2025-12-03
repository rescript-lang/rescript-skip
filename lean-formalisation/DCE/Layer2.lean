/-
  DCE/Layer2.lean
  Entry module for Layer 2 (Incremental DCE).

  This file re-exports all Layer 2 modules:
  - Layer2.Spec: Basic definitions (Reachable, liveSet, deadSet, RefState, refcountSpec)
  - Layer2.Algorithm: Algorithm framework (IncrAlg, RefcountAlg, running deltas)
  - Layer2.Characterization: BFS characterization for add, cascade for remove
  - Layer2.Bounds: Delta bounds and end-to-end correctness theorems
-/

import DCE.Layer2.Spec
import DCE.Layer2.Algorithm
import DCE.Layer2.Characterization
import DCE.Layer2.Bounds
