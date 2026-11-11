/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPair
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Scales

The original physical grid range gives a sufficiently small actual weak excitation for full-loss separation.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence

/-- The original physical grid range gives a sufficiently small actual weak excitation for full-loss separation. -/
theorem original_weak_quarter (N : ℕ) (hN : 256≤N) : 128/((N : ℝ)^2)≤1/4 := by
  have hn : (256 : ℝ)≤N := by exact_mod_cast hN
  have hp : 0<(N : ℝ)^2 := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith [sq_nonneg ((N : ℝ)-256)]

/-- A primary certified bound on pi supplies the original physical scale comparison. -/
theorem original_pi_square_lt_ten : Real.pi^2<10 := by
  have h := mul_pos (sub_pos.mpr Real.pi_lt_d2) (by linarith [Real.pi_pos] : 0<(3.15 : ℝ)+Real.pi)
  nlinarith

/-- The actual source's two spin means are separated enough to pay both estimation tolerance and full velocity nuisance. -/
theorem original_physical_threshold_gap (N d : ℕ) (hN : 256≤N) (hd : d≤3) :
    3*(N : ℝ)^2+(d : ℝ)/(2*Real.pi/N)^2<
      (2*(N : ℝ)^2/(2*Real.pi/N)^2)*(128/((N : ℝ)^2))*(1-128/((N : ℝ)^2))*(3/4) := by
  have hn : 0<(N : ℝ) := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hdn : (d : ℝ)≤3 := by exact_mod_cast hd
  let h : ℝ := 2*Real.pi/N
  let b : ℝ := 128/((N : ℝ)^2)
  let G : ℝ := 2*(N : ℝ)^2/h^2
  have hh : 0<h^2 := by dsimp [h]; positivity
  have hb : b≤1/4 := original_weak_quarter N hN
  have hleft : (G*b*(1-b)*(3/4))*h^2=192*(1-b) := by
    dsimp [G,b,h]
    field_simp [ne_of_gt hn,Real.pi_ne_zero]
    ring
  have hright : (3*(N : ℝ)^2+(d : ℝ)/h^2)*h^2=12*Real.pi^2+(d : ℝ) := by
    dsimp [h]
    field_simp [ne_of_gt hn,Real.pi_ne_zero]
    ring
  change 3*(N : ℝ)^2+(d : ℝ)/h^2<G*b*(1-b)*(3/4)
  apply (mul_lt_mul_iff_left₀ hh).mp
  rw [hleft,hright]
  nlinarith [original_pi_square_lt_ten]

/-- The real period-four and constant fields have a strict original full-loss gap greater than twice eta. -/
theorem original_dense_loss_gap (N : ℕ) (hN : 256≤N) :
    2*(N : ℝ)^2<(2*(N : ℝ)^2/(2*Real.pi/N)^2)*(2*(128/((N : ℝ)^2))*(1-128/((N : ℝ)^2))) := by
  have h := original_physical_threshold_gap N 0 hN (by decide)
  norm_num at h
  nlinarith [sq_nonneg (N : ℝ)]

/-- The original N and dimension range makes the bad-prior exponent at least twice the confidence crossover scale. -/
theorem original_bad_exponent_scale (N d : ℕ) (hN : 256≤N) (hd : d=2 ∨ d=3) :
    2≤(81/(262144*(d : ℝ)^2))*(N : ℝ)^2 := by
  have hn : (256 : ℝ)≤N := by exact_mod_cast hN
  have hn2 : (65536 : ℝ)≤(N : ℝ)^2 := by nlinarith [sq_nonneg ((N : ℝ)-256)]
  rcases hd with rfl | rfl <;> norm_num <;> nlinarith

/-- The actual McDiarmid exponent at the original full physical parameters dominates the source's stated bad-prior exponent. -/
theorem original_spin_exponent_lower (N d : ℕ) (M : ℝ) (hN : 256≤N) (hd : d=2 ∨ d=3) (hM : 0≤M) :
    (81/(262144*(d : ℝ)^2))*M≤
      M*((N : ℝ)^2)^2/(64*(d : ℝ)^2*(2*(N : ℝ)^2/(2*Real.pi/N)^2)^2*(128/((N : ℝ)^2))^2) := by
  have hn : (N : ℝ)≠0 := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hdn : (d : ℝ)≠0 := by rcases hd with rfl | rfl <;> norm_num
  have he : M*((N : ℝ)^2)^2/(64*(d : ℝ)^2*(2*(N : ℝ)^2/(2*Real.pi/N)^2)^2*(128/((N : ℝ)^2))^2)=
      (M/(262144*(d : ℝ)^2))*Real.pi^4 := by
    field_simp [hn,hdn,Real.pi_ne_zero]
    ring
  have hpi : (81 : ℝ)≤Real.pi^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤3) Real.pi_gt_three.le 4
    norm_num at h
    exact h
  rw [he]
  calc
    _ = (M/(262144*(d : ℝ)^2))*81 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpi (div_nonneg hM (by positivity))

/-- The actual bad-prior bound is paid by every original confidence value in the collision regime, without a confidence truncation. -/
theorem original_bad_prior_paid (N d : ℕ) (M δ : ℝ) (hN : 256≤N) (hd : d=2 ∨ d=3)
    (hM : 0≤M) (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤M/(N : ℝ)^2) :
    2*Real.exp (-(81/(262144*(d : ℝ)^2))*M)≤δ := by
  have hn : (N : ℝ)≠0 := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  let c : ℝ := 81/(262144*(d : ℝ)^2)
  have hs := original_bad_exponent_scale N d hN hd
  change 2≤c*(N : ℝ)^2 at hs
  have hx := mul_le_mul_of_nonneg_right hs (div_nonneg hM (sq_nonneg (N : ℝ)))
  have he : (c*(N : ℝ)^2)*(M/(N : ℝ)^2)=c*M := by field_simp [hn]
  rw [he] at hx
  have hcm : 2*Real.log (1/δ)≤c*M := (mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ)≤2)).trans hx
  have hexp : Real.exp (-2*Real.log (1/δ))=δ^2 := by
    calc
      _ = Real.exp (Real.log δ+Real.log δ) := by rw [one_div,Real.log_inv]; congr 1; ring
      _ = _ := by simp only [Real.exp_add,Real.exp_log hδ,pow_two]
  calc
    _ ≤ 2*Real.exp (-2*Real.log (1/δ)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by change -c*M≤_; linarith)) (by norm_num)
    _ = 2*δ^2 := by rw [hexp]
    _ ≤ δ := by nlinarith [mul_nonneg hδ.le (by linarith : 0≤1-2*δ)]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
