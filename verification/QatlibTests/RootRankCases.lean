/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RationalRootFloor
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.RankFactorization
public import Mathlib.Tactic.NormNum.NatSqrt

@[expose] public section

/-! Boundary consumers for rational root rounding and complex matrix rank factorization. -/

set_option autoImplicit false

open scoped ComplexOrder

namespace QatlibTests.RootRankCases

open Qatlib.Foundations.ScaledSqrt.SqrtBounds
open Qatlib.Foundations.PPTMatrix.OperatorCones

example : rootCount 0 (7 / 3) = 0 := by norm_num [rootCount]

example : rootCount 5 0 = 0 := by norm_num [rootCount]

example : rootCount 5 1 = 5 := by norm_num [rootCount]

example : rootCount 5 (1 / 4) = 2 := by norm_num [rootCount]

example : signedCount true (rootCount 5 (1 / 4)) = -2 := by
  norm_num [signedCount, rootCount]

example : |(signedCount true (rootCount 5 (1 / 4)) : ℝ) -
    (5 : ℝ) * signedRoot true (1 / 4)| < 1 :=
  signedCount_error 5 (1 / 4) (by norm_num) true

example : (0 : Matrix (Fin 0) (Fin 3) ℂ).rank = 0 := by simp

example : ∃ (W : Matrix (Fin 0) (Fin 0) ℂ) (V : Matrix (Fin 0) (Fin 3) ℂ),
    (0 : Matrix (Fin 0) (Fin 3) ℂ) = W * V :=
  exists_mul_eq_of_rank_le (by simp)

example (a : Fin 2 → ℂ) (b : Fin 3 → ℂ) :
    (Matrix.vecMulVec a b).rank ≤ 1 :=
  rank_vecMulVec_le_one a b

example : ∃ (N : ℕ) (v : Fin N → Fin 2 → ℂ),
    (0 : Matrix (Fin 2) (Fin 2) ℂ) =
      ∑ k, Matrix.vecMulVec (v k) (star (v k)) :=
  exists_sum_vecMulVec_of_posSemidef (Matrix.PosSemidef.zero)

end QatlibTests.RootRankCases
