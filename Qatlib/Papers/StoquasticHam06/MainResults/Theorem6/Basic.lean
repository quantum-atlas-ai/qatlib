/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem6

open Matrix

theorem trace_separation_yes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (L : ℕ) (mu : ℝ)
    (hmu : ∃ i, hG.eigenvalues i = mu) (hmax : ∀ i, hG.eigenvalues i ≤ mu)
    (hnonneg : ∀ i, 0 ≤ hG.eigenvalues i) :
    mu ^ L ≤ (G ^ L).trace :=
  trace_pow_lower_bound G hG L mu hmu hmax hnonneg

theorem trace_separation_no {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (L : ℕ) (mu : ℝ)
    (hmu : 0 ≤ mu) (hbound : ∀ i, |hG.eigenvalues i| ≤ mu) :
    (G ^ L).trace ≤ (Fintype.card ι : ℝ) * mu ^ L :=
  trace_pow_upper_bound G hG L mu hmu hbound

theorem log_gap_trace_ratio (muP muM : ℝ) (n p : ℕ) (hp : 0 < p)
    (hM : 0 < muM) (hP : 0 < muP)
    (hgap : 1 / (p : ℝ) ≤ Real.log muP - Real.log muM) :
    (2 : ℝ) ^ (2 * n) * muM ^ (2 * n * p) ≤ muP ^ (2 * n * p) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  have hqpos : 0 < muP / muM := div_pos hP hM

  have hlog : 1 / (p : ℝ) ≤ Real.log (muP / muM) := by
    rw [Real.log_div hP.ne' hM.ne']
    exact hgap

  have hexp_le : Real.exp (1 / (p : ℝ)) ≤ muP / muM := by
    rw [← Real.exp_log hqpos]
    exact Real.exp_le_exp.mpr hlog

  have hpow_le : Real.exp (1 / (p : ℝ)) ^ (2 * n * p) ≤ (muP / muM) ^ (2 * n * p) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexp_le _

  have hexp_eq : Real.exp (1 / (p : ℝ)) ^ (2 * n * p) = Real.exp (2 * n : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

  have hexp2 : Real.exp (2 * n : ℝ) = Real.exp 2 ^ n := by
    rw [show (2 : ℝ) * (n : ℝ) = (n : ℝ) * 2 by ring, Real.exp_nat_mul]
  have hexp2ge : (4 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h]
    have h1 := Real.exp_one_gt_two
    nlinarith [h1, Real.exp_pos 1]
  have htwo_pow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hexp_ge : (2 : ℝ) ^ (2 * n) ≤ Real.exp (2 * n : ℝ) := by
    rw [htwo_pow, hexp2]
    exact pow_le_pow_left₀ (by norm_num) hexp2ge n

  have hMk : muM ^ (2 * n * p) ≠ 0 := pow_ne_zero _ hM.ne'
  calc (2 : ℝ) ^ (2 * n) * muM ^ (2 * n * p)
      ≤ Real.exp (2 * n : ℝ) * muM ^ (2 * n * p) := by
        gcongr
    _ = Real.exp (1 / (p : ℝ)) ^ (2 * n * p) * muM ^ (2 * n * p) := by
        rw [hexp_eq]
    _ ≤ (muP / muM) ^ (2 * n * p) * muM ^ (2 * n * p) := by
        gcongr
    _ = muP ^ (2 * n * p) := by
        rw [div_pow]
        field_simp

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem6
