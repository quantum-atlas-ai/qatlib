/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-!
# An explicit comparison of quantum matching scores

This module studies the universal quantum matching score formula from [SasakiCarlini2002] and
proves that it exceeds one half for positive copy counts. For two copies, explicit
three-dimensional matrices provide the comparison value `Rtwo`.

The results evaluate both expressions exactly and establish the strict inequality
`strict_superiority_at_two` for this specified comparison value.

## Main statements

* `qmScore_gt_half`: the universal score exceeds one half for `N ≥ 1`.
* `Rtwo_eq`: the explicit comparison parameter is one eighth.
* `strict_superiority_at_two`: strict score comparison at two copies.

## References

* [Sasaki and Carlini, 2002][SasakiCarlini2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMatching02.MainResults.Comparison

/-- The universal matching score expressed by the endpoint and interior binomial square-root
terms. -/
def qmScore (N : ℕ) : ℝ :=
  1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
    (2 * Real.sqrt (N : ℝ) +
      ∑ k ∈ Finset.Icc 1 (N - 1),
        Real.sqrt (Nat.choose N k : ℝ) *
          Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)))

/-- For every `N ≥ 1`, the universal matching score is strictly greater than one half. See
[SasakiCarlini2002]. -/
theorem qmScore_gt_half (N : ℕ) (hN : 1 ≤ N) : qmScore N > 1 / 2 := by
  unfold qmScore
  have hc : 0 < Real.sqrt 2 / (2 : ℝ) ^ (N + 4) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsum :
      0 ≤ ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k : ℝ) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)) := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hb : 0 < 2 * Real.sqrt (N : ℝ) +
      ∑ k ∈ Finset.Icc 1 (N - 1),
        Real.sqrt (Nat.choose N k : ℝ) *
          Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)) := by
    have : 0 < 2 * Real.sqrt (N : ℝ) := by nlinarith [hsq]
    linarith
  have := mul_pos hc hb
  linarith

end Qatlib.Papers.QMatching02.MainResults.Comparison

open scoped ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.Comparison

/-- The square of `√2`, viewed as a complex number, is two. -/
theorem sqrt2c_sq' : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The square of the real number `√2` is two. -/
theorem sqrt2r_sq' : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
  rw [pow_two, Real.mul_self_sqrt (by norm_num)]

/-- The symmetric three-by-three matrix with `√2` on the adjacent off-diagonal entries and zero
elsewhere. -/
def qwMat2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (Real.sqrt 2 : ℂ), 0; (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
     0, (Real.sqrt 2 : ℂ), 0]

/-- The real-valued complex vector `(1 / 2, √2 / 2, 1 / 2)`. -/
def lamVec2 : Fin 3 → ℂ := ![1 / 2, (Real.sqrt 2 : ℂ) / 2, 1 / 2]

/-- The explicit three-by-three matrix representing the outer product of `lamVec2` with its
conjugate. -/
def lamMat2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 4, (Real.sqrt 2 : ℂ) / 4, 1 / 4;
     (Real.sqrt 2 : ℂ) / 4, 1 / 2, (Real.sqrt 2 : ℂ) / 4;
     1 / 4, (Real.sqrt 2 : ℂ) / 4, 1 / 4]

/-- The vector `lamVec2` is fixed by complex conjugation. -/
theorem star_lamVec2 : star lamVec2 = lamVec2 := by
  funext i; fin_cases i <;> simp [lamVec2]

/-- The matrix `lamMat2` equals the outer product of `lamVec2` with its conjugate. -/
theorem lamMat2_eq_vecMulVec : lamMat2 = Matrix.vecMulVec lamVec2 (star lamVec2) := by
  rw [star_lamVec2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamMat2, lamVec2, Matrix.vecMulVec]
  all_goals ring_nf
  all_goals try rw [sqrt2c_sq']
  all_goals norm_num

/-- The matrix `lamMat2` is positive semidefinite. See [SasakiCarlini2002]. -/
theorem lamMat2_posSemidef : lamMat2.PosSemidef := by
  rw [lamMat2_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star lamVec2

/-- The matrix `lamMat2` is idempotent. -/
theorem lamMat2_mul_self : lamMat2 * lamMat2 = lamMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamMat2, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> rw [sqrt2c_sq'] <;> norm_num

/-- Left multiplication by `qwMat2` scales `lamMat2` by two. -/
theorem qwMat2_mul_lamMat2 : qwMat2 * lamMat2 = 2 • lamMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qwMat2, lamMat2, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> rw [sqrt2c_sq'] <;> norm_num

/-- The trace of `lamMat2` is one. -/
theorem lamMat2_trace : lamMat2.trace = 1 := by
  simp [lamMat2, Matrix.trace, Fin.sum_univ_three]
  norm_num

/-- The two-copy comparison parameter formed from adjacent binomial weights and entries of
`lamMat2`. -/
def Rtwo : ℝ :=
  (1 / 2 ^ (2 + 1)) *
    (Real.sqrt ((Nat.choose 2 0 : ℝ) * (Nat.choose 2 1 : ℝ)) * (lamMat2 0 1).re
      + Real.sqrt ((Nat.choose 2 1 : ℝ) * (Nat.choose 2 2 : ℝ)) * (lamMat2 1 2).re)

/-- The explicit two-copy comparison parameter `Rtwo` equals one eighth. See
[SasakiCarlini2002]. -/
theorem Rtwo_eq : Rtwo = 1 / 8 := by
  simp only [Rtwo, lamMat2, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val']
  norm_num
  ring_nf
  rw [sqrt2r_sq']
  ring

/-- The universal matching score at two copies is `1 / 2 + (2 + √2) / 32`. -/
theorem qmScore_two : qmScore 2 = 1 / 2 + (2 + Real.sqrt 2) / 32 := by
  simp only [qmScore]
  norm_num
  ring_nf
  rw [sqrt2r_sq']
  ring

/-- At two copies, the universal matching score strictly exceeds `1 / 2 + Rtwo / √2`. See
[SasakiCarlini2002]. -/
theorem strict_superiority_at_two : qmScore 2 > 1 / 2 + Rtwo / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [qmScore_two, Rtwo_eq]
  rw [show (1 / 8 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 16 by
    field_simp
    nlinarith [h2]]
  nlinarith

/-- There exists a copy count whose universal matching score exceeds `1 / 2 + Rtwo / √2`. See
[SasakiCarlini2002]. -/
theorem universal_beats_semiclassical_at_two :
    ∃ N : ℕ, qmScore N > 1 / 2 + Rtwo / Real.sqrt 2 :=
  ⟨2, strict_superiority_at_two⟩

end Qatlib.Papers.QMatching02.MainResults.Comparison
