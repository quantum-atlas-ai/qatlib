/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real

noncomputable section

lemma abs_sin_div_sqrtTwo_le (k : ℝ) :
    |Real.sin k / Real.sqrt 2| ≤ 1 / Real.sqrt 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [abs_div, abs_of_pos hpos]
  gcongr
  exact Real.abs_sin_le_one k

lemma sin_div_sqrtTwo_mem_Ioo (k : ℝ) :
    Real.sin k / Real.sqrt 2 ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlt : (1 : ℝ) / Real.sqrt 2 < 1 := by
    rw [div_lt_one hpos]
    exact Real.one_lt_sqrt_two
  have habs := abs_sin_div_sqrtTwo_le k
  have hge : -(1 : ℝ) < Real.sin k / Real.sqrt 2 := by
    have := (abs_lt.mp (lt_of_le_of_lt habs hlt)).1
    linarith
  have hle : Real.sin k / Real.sqrt 2 < 1 := by
    have := (abs_lt.mp (lt_of_le_of_lt habs hlt)).2
    linarith
  exact ⟨hge, hle⟩

lemma sin_div_sqrtTwo_mem_Icc (k : ℝ) :
    Real.sin k / Real.sqrt 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := sin_div_sqrtTwo_mem_Ioo k
  exact ⟨le_of_lt h1, le_of_lt h2⟩

theorem sin_dispersion (k : ℝ) : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := by
  unfold dispersion
  exact Real.sin_arcsin (sin_div_sqrtTwo_mem_Ioo k).1.le (sin_div_sqrtTwo_mem_Ioo k).2.le

theorem cos_dispersion (k : ℝ) :
    Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 := by
  unfold dispersion
  rw [Real.cos_arcsin]
  have key : (1 : ℝ) - (Real.sin k / Real.sqrt 2) ^ 2
      = (1 + Real.cos k ^ 2) / 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have htrig : Real.sin k ^ 2 + Real.cos k ^ 2 = 1 := Real.sin_sq_add_cos_sq k
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    field_simp
    nlinarith [hsq, htrig]
  rw [key, Real.sqrt_div' (1 + Real.cos k ^ 2) (by norm_num)]

theorem hasDerivAt_dispersion (k : ℝ) :
    HasDerivAt dispersion (Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) k := by
  have hinner : HasDerivAt (fun k : ℝ => Real.sin k / Real.sqrt 2)
      (Real.cos k / Real.sqrt 2) k := by
    simpa using (Real.hasDerivAt_sin k).div_const (Real.sqrt 2)
  have hmem := sin_div_sqrtTwo_mem_Ioo k
  have houter := Real.hasDerivAt_arcsin
    (x := Real.sin k / Real.sqrt 2) (ne_of_lt hmem.1).symm (ne_of_lt hmem.2)
  have hcomp := houter.comp k hinner
  have hkey : (1 : ℝ) - (Real.sin k / Real.sqrt 2) ^ 2 = (1 + Real.cos k ^ 2) / 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have htrig : Real.sin k ^ 2 + Real.cos k ^ 2 = 1 := Real.sin_sq_add_cos_sq k
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    field_simp
    nlinarith [hsq, htrig]
  have hval : 1 / Real.sqrt (1 - (Real.sin k / Real.sqrt 2) ^ 2) *
        (Real.cos k / Real.sqrt 2) = Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) := by
    rw [hkey, Real.sqrt_div' (1 + Real.cos k ^ 2) (by norm_num)]
    have h1 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have h2 : Real.sqrt (1 + Real.cos k ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
  have hmain : HasDerivAt (fun k : ℝ => Real.arcsin (Real.sin k / Real.sqrt 2))
      (Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) k := hcomp.congr_deriv hval
  exact hmain

lemma dispersion_mem_Icc (k : ℝ) : dispersion k ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩

lemma sqrt_one_add_cos_sq_pos (k : ℝ) : 0 < Real.sqrt (1 + Real.cos k ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith [sq_nonneg (Real.cos k)])

theorem hasDerivAt_cosDivSqrt (k : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos x / Real.sqrt (1 + Real.cos x ^ 2))
      (-Real.sin k / (Real.sqrt (1 + Real.cos k ^ 2)) ^ 3) k := by
  have hpos : (0 : ℝ) < Real.sqrt (1 + Real.cos k ^ 2) := sqrt_one_add_cos_sq_pos k
  have hinner : HasDerivAt (fun x : ℝ => 1 + Real.cos x ^ 2)
      (2 * Real.cos k * -Real.sin k) k := by
    have h1 : HasDerivAt (fun x : ℝ => Real.cos x ^ 2)
        (2 * Real.cos k ^ (2 - 1) * -Real.sin k) k :=
      (Real.hasDerivAt_cos k).pow 2
    have h2 := h1.const_add 1
    simpa [add_comm] using h2
  have hd : HasDerivAt (fun x : ℝ => Real.sqrt (1 + Real.cos x ^ 2))
      ((2 * Real.cos k * -Real.sin k) / (2 * Real.sqrt (1 + Real.cos k ^ 2))) k := by
    have h :=
        (Real.hasDerivAt_sqrt (x := 1 + Real.cos k ^ 2) (by nlinarith [sq_nonneg (Real.cos k)])).comp k hinner
    simpa [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm] using! h
  have hq := (Real.hasDerivAt_cos k).div hd (ne_of_gt hpos)
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (Real.cos k)])
  convert! hq using 1
  try field_simp
  rw [hsq]
  ring_nf

theorem hasDerivAt_phaseK (α k : ℝ) :
    HasDerivAt (fun x : ℝ => phaseK x α)
      (-(Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) + α)) k := by
  have h2 : HasDerivAt (fun x : ℝ => α * x) α k := by
    simpa using (hasDerivAt_id k).const_mul α
  have h : HasDerivAt (fun x : ℝ => dispersion x + α * x)
      (Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) + α) k :=
    (hasDerivAt_dispersion k).add h2
  have := h.neg
  unfold phaseK
  exact this

theorem hasDerivAt_phaseK_deriv (α k : ℝ) :
    HasDerivAt (fun x : ℝ => -(Real.cos x / Real.sqrt (1 + Real.cos x ^ 2) + α))
      (Real.sin k / (Real.sqrt (1 + Real.cos k ^ 2)) ^ 3) k := by
  have h2 : HasDerivAt (fun x : ℝ => -(Real.cos x / Real.sqrt (1 + Real.cos x ^ 2)) - α)
      (Real.sin k / (Real.sqrt (1 + Real.cos k ^ 2)) ^ 3) k := by
    simpa [neg_div] using (hasDerivAt_cosDivSqrt k).neg.sub_const α
  convert! h2 using 1
  funext x
  ring

theorem hasDerivAt_phaseK_second_deriv (k : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin x / (Real.sqrt (1 + Real.cos x ^ 2)) ^ 3)
      (2 * Real.cos k * (1 + Real.sin k ^ 2)
        / (Real.sqrt (1 + Real.cos k ^ 2)) ^ 5) k := by
  have hpos : (0 : ℝ) < Real.sqrt (1 + Real.cos k ^ 2) := sqrt_one_add_cos_sq_pos k

  have hinner : HasDerivAt (fun x : ℝ => 1 + Real.cos x ^ 2)
      (2 * Real.cos k * -Real.sin k) k := by
    have h1 : HasDerivAt (fun x : ℝ => Real.cos x ^ 2)
        (2 * Real.cos k ^ (2 - 1) * -Real.sin k) k :=
      (Real.hasDerivAt_cos k).pow 2
    have h2 := h1.const_add 1
    simpa [add_comm] using h2
  have hd : HasDerivAt (fun x : ℝ => Real.sqrt (1 + Real.cos x ^ 2))
      ((2 * Real.cos k * -Real.sin k) / (2 * Real.sqrt (1 + Real.cos k ^ 2))) k := by
    have h :=
        (Real.hasDerivAt_sqrt (x := 1 + Real.cos k ^ 2) (by nlinarith [sq_nonneg (Real.cos k)])).comp k hinner
    simpa [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm] using! h
  have hd3 : HasDerivAt (fun x : ℝ => (Real.sqrt (1 + Real.cos x ^ 2)) ^ 3)
      (3 * (Real.sqrt (1 + Real.cos k ^ 2)) ^ (3 - 1)
        * ((2 * Real.cos k * -Real.sin k) / (2 * Real.sqrt (1 + Real.cos k ^ 2)))) k :=
    hd.pow 3
  have hq := (Real.hasDerivAt_sin k).div hd3 (pow_ne_zero 3 (ne_of_gt hpos))
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (Real.cos k)])
  have hsq4 : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 4 = (1 + Real.cos k ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hsin2 : Real.sin k ^ 2 = 1 - Real.cos k ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq k]
  convert! hq using 1
  try field_simp
  rw [hsq4, hsq]
  ring_nf
  rw [hsin2]
  ring

end

end Qatlib.Papers.QWalkLine00.MainResults
