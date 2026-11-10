/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMatching02.MainResults.Comparison

def qmScore (N : ℕ) : ℝ :=
  1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
    (2 * Real.sqrt (N : ℝ) +
      ∑ k ∈ Finset.Icc 1 (N - 1),
        Real.sqrt (Nat.choose N k : ℝ) *
          Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)))

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

theorem sqrt2c_sq' : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem sqrt2r_sq' : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
  rw [pow_two, Real.mul_self_sqrt (by norm_num)]

def qwMat2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (Real.sqrt 2 : ℂ), 0; (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
     0, (Real.sqrt 2 : ℂ), 0]

def lamVec2 : Fin 3 → ℂ := ![1 / 2, (Real.sqrt 2 : ℂ) / 2, 1 / 2]

def lamMat2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 4, (Real.sqrt 2 : ℂ) / 4, 1 / 4;
     (Real.sqrt 2 : ℂ) / 4, 1 / 2, (Real.sqrt 2 : ℂ) / 4;
     1 / 4, (Real.sqrt 2 : ℂ) / 4, 1 / 4]

theorem star_lamVec2 : star lamVec2 = lamVec2 := by
  funext i; fin_cases i <;> simp [lamVec2]

theorem lamMat2_eq_vecMulVec : lamMat2 = Matrix.vecMulVec lamVec2 (star lamVec2) := by
  rw [star_lamVec2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamMat2, lamVec2, Matrix.vecMulVec]
  all_goals ring_nf
  all_goals try rw [sqrt2c_sq']
  all_goals norm_num

theorem lamMat2_posSemidef : lamMat2.PosSemidef := by
  rw [lamMat2_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star lamVec2

theorem lamMat2_mul_self : lamMat2 * lamMat2 = lamMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamMat2, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> rw [sqrt2c_sq'] <;> norm_num

theorem qwMat2_mul_lamMat2 : qwMat2 * lamMat2 = 2 • lamMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qwMat2, lamMat2, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> rw [sqrt2c_sq'] <;> norm_num

theorem lamMat2_trace : lamMat2.trace = 1 := by
  simp [lamMat2, Matrix.trace, Fin.sum_univ_three]
  norm_num

def Rtwo : ℝ :=
  (1 / 2 ^ (2 + 1)) *
    (Real.sqrt ((Nat.choose 2 0 : ℝ) * (Nat.choose 2 1 : ℝ)) * (lamMat2 0 1).re
      + Real.sqrt ((Nat.choose 2 1 : ℝ) * (Nat.choose 2 2 : ℝ)) * (lamMat2 1 2).re)

theorem Rtwo_eq : Rtwo = 1 / 8 := by
  simp only [Rtwo, lamMat2, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val']
  norm_num
  ring_nf
  rw [sqrt2r_sq']
  ring

theorem qmScore_two : qmScore 2 = 1 / 2 + (2 + Real.sqrt 2) / 32 := by
  simp only [qmScore]
  norm_num
  ring_nf
  rw [sqrt2r_sq']
  ring

theorem strict_superiority_at_two : qmScore 2 > 1 / 2 + Rtwo / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [qmScore_two, Rtwo_eq]
  rw [show (1 / 8 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 16 by
    field_simp
    nlinarith [h2]]
  nlinarith

theorem universal_beats_semiclassical_at_two :
    ∃ N : ℕ, qmScore N > 1 / 2 + Rtwo / Real.sqrt 2 :=
  ⟨2, strict_superiority_at_two⟩

end Qatlib.Papers.QMatching02.MainResults.Comparison
