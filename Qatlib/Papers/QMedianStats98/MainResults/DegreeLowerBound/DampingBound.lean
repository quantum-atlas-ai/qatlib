/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound

theorem source_damping_factor {C x : ℝ} (hC : 0 < C) (hxC : C ≤ |x|)
    (hx1 : |x| ≤ 1) (d1 : ℕ) :
    (1 - x ^ 2) ^ d1 ≤ Real.exp (-(C ^ 2 * (d1 : ℝ))) := by
  have hx2le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx1]
  have hC2le : C ^ 2 ≤ x ^ 2 := by
    have hsq : C ^ 2 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x, hxC]
    simpa only [sq_abs] using hsq
  have hnonneg : 0 ≤ 1 - x ^ 2 := by linarith
  have h1 : 1 - x ^ 2 ≤ Real.exp (-(x ^ 2)) := by
    have h := Real.add_one_le_exp (-(x ^ 2))
    linarith
  have h2 : Real.exp (-(x ^ 2)) ≤ Real.exp (-(C ^ 2)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : 1 - x ^ 2 ≤ Real.exp (-(C ^ 2)) := h1.trans h2
  have h4 : (1 - x ^ 2) ^ d1 ≤ (Real.exp (-(C ^ 2))) ^ d1 :=
    pow_le_pow_left₀ hnonneg h3 d1
  have h5 : (Real.exp (-(C ^ 2))) ^ d1 = Real.exp (-(C ^ 2 * (d1 : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [h5] at h4

theorem source_damping_exp_of_six {C : ℝ} {d1 d : ℕ}
    (h : 6 * (d : ℝ) ≤ C ^ 2 * (d1 : ℝ)) :
    Real.exp (-(C ^ 2 * (d1 : ℝ))) ≤ Real.exp (-(6 * (d : ℝ))) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem source_shifted_algebraic_bound {C x : ℝ} {d1 d : ℕ}
    (hC : 0 < C) (hxC : C ≤ |x|) (hx1 : |x| ≤ 1)
    (hd1 : 6 * (d : ℝ) ≤ C ^ 2 * (d1 : ℝ)) (hd : 1 ≤ d) :
    (4 / 3 : ℝ) * (2 : ℝ) ^ d * (1 - x ^ 2) ^ d1 ≤ 1 := by
  have hdamp := source_damping_factor hC hxC hx1 d1
  have he := source_damping_exp_of_six (C := C) (d1 := d1) (d := d) hd1
  have hdamp' : (1 - x ^ 2) ^ d1 ≤ Real.exp (-(6 * (d : ℝ))) := hdamp.trans he
  have h2d : (2 : ℝ) ^ d ≤ Real.exp (5 * (d : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 5 := by
      have h := Real.add_one_le_exp (5 : ℝ)
      linarith
    have hpos : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hp := pow_le_pow_left₀ hpos h2 d
    rw [← Real.exp_nat_mul] at hp
    simpa only [mul_comm] using hp
  have hdamp_nonneg : (0 : ℝ) ≤ (1 - x ^ 2) ^ d1 := by
    have hx2le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx1]
    have : 0 ≤ 1 - x ^ 2 := by linarith
    positivity
  have hstep : (4 / 3 : ℝ) * (2 : ℝ) ^ d * (1 - x ^ 2) ^ d1 ≤
      (4 / 3 : ℝ) * Real.exp (5 * (d : ℝ)) * Real.exp (-(6 * (d : ℝ))) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left h2d (by norm_num)
    · exact hdamp'
    · exact hdamp_nonneg
    · positivity
  have heq : (4 / 3 : ℝ) * Real.exp (5 * (d : ℝ)) * Real.exp (-(6 * (d : ℝ))) =
      (4 / 3 : ℝ) * Real.exp (-(d : ℝ)) := by
    have h1 : Real.exp (5 * (d : ℝ)) * Real.exp (-(6 * (d : ℝ))) = Real.exp (-(d : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hexp_le : (4 / 3 : ℝ) * Real.exp (-(d : ℝ)) ≤ 1 := by
    have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hexpd : Real.exp (-(d : ℝ)) ≤ Real.exp (-(1 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h4 : (4 / 3 : ℝ) * Real.exp (-(1 : ℝ)) ≤ 1 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hinv : Real.exp (-(1 : ℝ)) ≤ (1 / 2 : ℝ) := by
        rw [Real.exp_neg]
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
        exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr he1
      nlinarith
    calc (4 / 3 : ℝ) * Real.exp (-(d : ℝ))
        ≤ (4 / 3 : ℝ) * Real.exp (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexpd (by norm_num)
      _ ≤ 1 := h4
  linarith [hstep, hexp_le]

theorem source_claim_2_3_of_grid_norm {q : Polynomial ℝ} {c C : ℝ} {d d1 : ℕ}
    (hC : 0 < C) (hd : 1 ≤ d) (hd1 : 6 * (d : ℝ) ≤ C ^ 2 * (d1 : ℝ))
    (hnorm : ∀ y : ℝ, |q.eval y| ≤ (4 / 3 : ℝ) * (2 : ℝ) ^ d)
    (x : ℝ) (hxC : C ≤ |x|) (hx1 : |x| ≤ 1) :
    |q.eval (x + c) * (1 - x ^ 2) ^ d1| ≤ 1 := by
  have hdamp := source_shifted_algebraic_bound (d := d) (d1 := d1) hC hxC hx1 hd1 hd
  have hq := hnorm (x + c)
  have hnonneg : (0 : ℝ) ≤ (1 - x ^ 2) ^ d1 := by
    have hx2le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx1]
    have : 0 ≤ 1 - x ^ 2 := by linarith
    positivity
  rw [abs_mul, abs_of_nonneg hnonneg]
  exact (mul_le_mul hq le_rfl hnonneg (by positivity)).trans hdamp

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
