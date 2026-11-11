/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Definitions for quantum search applications

This module defines the local minimum predicate, grid indices, and Boolean matrix product
relation used in the applications surveyed in [Ambainis2005]. The scalar expressions
`LocalMinQueryLedger` and `LocalMinOptimalMemory` record the local search cost and its balancing
parameter.

## Main statements

* `IsLocalMinimum`: Requires that no single bit flip lowers the objective.
* `MatrixProductHolds`: Expresses Boolean matrix multiplication over ZMod 2.
* `LocalMinQueryLedger`: Records the scalar local minimum query estimate.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- A Boolean string is a local minimum when flipping any single bit does not decrease the
integer valued objective. -/
def IsLocalMinimum {n : ℕ} (f : (Fin n → Bool) → ℤ) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin n, f x ≤ f (Function.update x i (Bool.not (x i)))

/-- The type of cells in a d dimensional grid of side length n. -/
abbrev GridCell (d n : ℕ) := Fin d → Fin n

/-- Encodes a Boolean as zero or one in `ZMod 2`. -/
def bitToZMod2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- The entrywise assertion that A times B equals C after interpreting Boolean entries in `ZMod
2`. -/
def MatrixProductHolds {n : ℕ} (A B C : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i j : Fin n,
    (∑ k : Fin n, bitToZMod2 (A i k) * bitToZMod2 (B k j)) = bitToZMod2 (C i j)

/-- The scalar cost expression √m + 2^n√n/m for local minimum search. -/
def LocalMinQueryLedger (n : ℕ) (m : ℝ) : ℝ :=
  Real.sqrt m + (2 : ℝ) ^ n * Real.sqrt (n : ℝ) / m

/-- The balancing parameter 2^(2n/3)n^(1/3) for the local minimum cost expression. -/
def LocalMinOptimalMemory (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((2 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 3)

end Qatlib.Papers.QSearchSurvey05.MainResults
