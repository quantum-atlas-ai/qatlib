/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.UniversalMatching

def qmScore (N : ℕ) : ℝ :=
  1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
    (2 * Real.sqrt (N : ℝ) +
      ∑ k ∈ Finset.Icc 1 (N - 1),
        Real.sqrt (Nat.choose N k : ℝ) *
          Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)))

theorem qmScore_eq (N : ℕ) :
    qmScore N =
      1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
        (2 * Real.sqrt (N : ℝ) +
          ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k : ℝ) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) :=
  rfl

theorem universal_matching_POVM (N : ℕ)
    (kPlus kMinus : Fin (N + 1) → (Fin (N + 1) → ℂ))
    (hcomplete :
      (∑ k, vecMulVec (kPlus k) (star (kPlus k)))
        + (∑ k, vecMulVec (kMinus k) (star (kMinus k))) = 1) :
    (∑ k, vecMulVec (kPlus k) (star (kPlus k))).PosSemidef
      ∧ (∑ k, vecMulVec (kMinus k) (star (kMinus k))).PosSemidef
      ∧ (∑ k, vecMulVec (kPlus k) (star (kPlus k)))
          + (∑ k, vecMulVec (kMinus k) (star (kMinus k))) = 1 := by
  refine ⟨?_, ?_, hcomplete⟩
  · exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨N + 1, kPlus, rfl⟩
  · exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨N + 1, kMinus, rfl⟩

end Qatlib.Papers.QMatching02.MainResults.UniversalMatching
