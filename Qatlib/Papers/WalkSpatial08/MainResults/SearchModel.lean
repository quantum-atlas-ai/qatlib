/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.WalkSpatial08.MainResults.SearchDefs


set_option backward.isDefEq.respectTransparency false

/-!
# WalkSpatial08 — time-step model for two-dimensional spatial search

Fixed source: arXiv:0801.0497v2 (Avatar Tulsi, *Faster quantum walk algorithm for
the two dimensional spatial search*), §I p.1 (lattice, marking function, time-step
model) and §III p.3–5 (controlled walk and its complexity).

The paper places `N` items on the sites `|x,y⟩`, `x,y ∈ {0,…,√N−1}`, of a
`√N × √N` two-dimensional lattice, marks a unique item `m` by a binary oracle
`f`, and charges one time step for either one oracle query of the current site or
one move to a neighboring site. The main theorem (abstract, §I, §III) states that
the new ancilla-controlled discrete-time walk solves this problem in
`O(√(N log N))` time steps with constant success probability, an
`O(√(log N))` improvement over the previous `O(√N log N)` walk algorithms.

This module owns the cost model and the solvability predicate consumed by the
main theorem in `SourceMainResult.lean`. It deliberately keeps the quantum
walk itself in `ControlledWalkModel.lean` / `SpectralBounds.lean`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.WalkSpatial08.MainResults

namespace Qatlib.Papers.WalkSpatial08.MainResults

/-- A candidate lattice-search algorithm at lattice parameter `n`: its time-step
account and its success probability for the unique marked item. -/
structure LatticeSearchAlgorithm (n : ℕ) where
  /-- The algorithm's time-step account. -/
  account : TimeAccount
  /-- The probability of outputting the marked site on the unique-marked instance. -/
  successProbability : ℝ

/-- `SolvesWithin n T p`: some algorithm for the `n × n` lattice uses at most `T`
time steps and succeeds with probability at least `p`. This is the paper's
§III statement "the total complexity of algorithm is `O(√(N log N))`" with
"constant probability" of reading `|m⟩`. -/
def SolvesWithin (n : ℕ) (T p : ℝ) : Prop :=
  ∃ alg : LatticeSearchAlgorithm n,
    (alg.account.steps : ℝ) ≤ T ∧ p ≤ alg.successProbability

end Qatlib.Papers.WalkSpatial08.MainResults
