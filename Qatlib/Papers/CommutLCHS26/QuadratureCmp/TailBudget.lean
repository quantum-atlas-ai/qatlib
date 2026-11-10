/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
import Qatlib.Concepts.QsvtCore.ApproxToolkit.EffectiveNearOptimalSignWindow
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Real Set MeasureTheory
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
open Qatlib.Concepts.QsvtCore.ApproxToolkit (erf one_sub_erf_eq one_sub_erf_le)

def tailConstant (n : ℕ) (b c d : ℝ) : ℝ :=
  c / Real.sqrt Real.pi * ((b + 1) / b) ^ n * Real.exp (d - 1 / (4 * c ^ 2))

theorem mass_zero (n : ℕ) (b c d : ℝ) : mass n b c d 0 0 = tailConstant n b c d := by
  unfold mass tailConstant
  rw [div_pow]
  simp only [sub_zero, zero_pow two_ne_zero, zero_sub, zero_mul, one_mul, add_zero]
  congr 1
  congr 1
  ring

theorem tailConstant_pos (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    0 < tailConstant n b c d := by unfold tailConstant; positivity

theorem gaussian_tail_erfc {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (∫ x in Ioi R, Real.exp (-x ^ 2 / (4 * c ^ 2))) =
      c * Real.sqrt Real.pi * (1 - erf (R / (2 * c))) := by
  have he : (fun t : ℝ => Real.exp (-(2 * c * t) ^ 2 / (4 * c ^ 2))) =
      (fun t : ℝ => Real.exp (-t ^ 2)) := by
    funext t
    congr 1
    field_simp
    ring
  have hr : 2 * c * (R / (2 * c)) = R := by field_simp
  have hs := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x ^ 2 / (4 * c ^ 2)))
    (R / (2 * c)) (b := 2 * c) (by positivity)
  rw [he, hr, smul_eq_mul] at hs
  rw [one_sub_erf_eq _ (div_pos hR (by positivity)), hs]
  field_simp [hc.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']

theorem continuousTail_le_erfc (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {R : ℝ} (hR : 0 < R) :
    continuousTail n b c d R ≤ tailConstant n b c d * (1 - erf (R / (2 * c))) := by
  have hp (x : ℝ) : ‖coefficient n b c d (x : ℂ)‖ ≤
      amplitude n b c d 0 0 * Real.exp (-x ^ 2 / (4 * c ^ 2)) := by
    have h := coefficient_growth_le n b c d hb (ρ := 0) (K := 0) (by norm_num)
      (Or.inr hb) (by norm_num) (z := (x : ℂ)) (by simp)
    simpa only [Complex.ofReal_im, Complex.ofReal_re, max_self, zero_mul,
      Real.exp_zero, mul_one] using! h
  calc
    _ ≤ 2 * (∫ x in Ioi R, amplitude n b c d 0 0 *
        Real.exp (-x ^ 2 / (4 * c ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact integral_mono (real_norm_integrable n b c d hb hc).integrableOn
        ((gaussian_integrable hc).const_mul _).integrableOn hp
    _ = (amplitude n b c d 0 0 * (2 * c * Real.sqrt Real.pi)) *
        (1 - erf (R / (2 * c))) := by
      rw [integral_const_mul, gaussian_tail_erfc hc hR]
      ring
    _ = _ := by rw [amplitude_mul_gaussian, mass_zero]

theorem mass_pos (n : ℕ) (b c d ρ K : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) : 0 < mass n b c d ρ K := by
  have hpow : 0 < (b - ρ) ^ n := by
    rcases hbn with rfl | hbn
    · simp
    · exact pow_pos (sub_pos.mpr hbn) _
  unfold mass
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ
  positivity

def meshLog (M ε : ℝ) : ℝ := Real.log (1 + 2 * M / ε)

def tailLog (C ε : ℝ) : ℝ := max 1 (Real.log (C / ε))

def meshStep (c ρ M ε : ℝ) : ℝ := min 1 (min (2 * c) (2 * Real.pi * ρ / meshLog M ε))

def tailRadius (c C ε : ℝ) : ℝ := 2 * c * Real.sqrt (tailLog C ε)

theorem meshLog_pos {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) : 0 < meshLog M ε := by
  apply Real.log_pos
  have hp : 0 < 2 * M / ε := by positivity
  linarith

theorem meshStep_pos {c ρ M ε : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hε : 0 < ε) : 0 < meshStep c ρ M ε := by
  have hl := meshLog_pos hM hε
  unfold meshStep
  positivity

theorem mesh_budget_of_step {ρ M ε h : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hh : 0 < h) (hs : h ≤ 2 * Real.pi * ρ / meshLog M ε) :
    2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) ≤ ε := by
  have hl := meshLog_pos hM hε
  have he : meshLog M ε ≤ 2 * Real.pi * ρ / h := by
    apply (le_div_iff₀ hh).mpr
    have h := (le_div_iff₀ hl).mp hs
    nlinarith
  have hx : Real.exp (meshLog M ε) = 1 + 2 * M / ε :=
    Real.exp_log (by positivity)
  have hd := Real.exp_le_exp.mpr he
  rw [hx] at hd
  have hp : 0 < Real.exp (2 * Real.pi * ρ / h) - 1 := by
    have hpos : 0 < 2 * M / ε := by positivity
    linarith
  apply (div_le_iff₀ hp).mpr
  have hmul := mul_le_mul_of_nonneg_left hd hε.le
  have heps : ε * (2 * M / ε) = 2 * M := by field_simp
  rw [mul_add, mul_one, heps] at hmul
  nlinarith

theorem mesh_budget {c ρ M ε : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hε : 0 < ε) :
    2 * M / (Real.exp (2 * Real.pi * ρ / meshStep c ρ M ε) - 1) ≤ ε := by
  exact mesh_budget_of_step hM hε (meshStep_pos hc hρ hM hε)
    ((min_le_right _ _).trans (min_le_right _ _))

theorem erfc_le_exp {u : ℝ} (hu : 1 ≤ u) : 1 - erf u ≤ Real.exp (-u ^ 2) := by
  have hp : 1 ≤ Real.sqrt Real.pi := by
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    simpa using! Real.sqrt_le_sqrt hpi
  have hd : 1 ≤ u * Real.sqrt Real.pi := by nlinarith
  exact (one_sub_erf_le u (by linarith)).trans (div_le_self (Real.exp_pos _).le hd)

theorem exp_tailLog_budget {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    C * Real.exp (-tailLog C ε) ≤ ε := by
  have he : Real.exp (-tailLog C ε) ≤ (C / ε)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (C / ε)) :=
        Real.exp_le_exp.mpr (neg_le_neg (le_max_right (1 : ℝ) (Real.log (C / ε))))
      _ = _ := by rw [Real.exp_neg, Real.exp_log (div_pos hC hε)]
  have hm := mul_le_mul_of_nonneg_left he hC.le
  have hi : C * (C / ε)⁻¹ = ε := by field_simp
  simpa only [hi] using! hm

theorem tail_budget {c C ε : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) :
    C * (1 - erf (tailRadius c C ε / (2 * c))) ≤ ε := by
  have hl : 1 ≤ tailLog C ε := le_max_left _ _
  have hu : 1 ≤ Real.sqrt (tailLog C ε) := by simpa using! Real.sqrt_le_sqrt hl
  have hr : tailRadius c C ε / (2 * c) = Real.sqrt (tailLog C ε) := by
    unfold tailRadius
    field_simp
  rw [hr]
  apply (mul_le_mul_of_nonneg_left (erfc_le_exp hu) hC.le).trans
  rw [Real.sq_sqrt (by linarith : 0 ≤ tailLog C ε)]
  exact exp_tailLog_budget hC hε

theorem inv_meshStep_le {c ρ M ε : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hε : 0 < ε) :
    1 / meshStep c ρ M ε ≤ 1 + 1 / (2 * c) + meshLog M ε / (2 * Real.pi * ρ) := by
  have hl := meshLog_pos hM hε
  have hc' : 0 ≤ 1 / (2 * c) := by positivity
  have hq : 0 ≤ meshLog M ε / (2 * Real.pi * ρ) := by positivity
  unfold meshStep
  rcases min_choice (1 : ℝ) (min (2 * c) (2 * Real.pi * ρ / meshLog M ε)) with he | he
  · rw [he, one_div_one]
    linarith
  · rw [he]
    rcases min_choice (2 * c) (2 * Real.pi * ρ / meshLog M ε) with he' | he'
    · rw [he']
      linarith
    · rw [he']
      have hi : 1 / (2 * Real.pi * ρ / meshLog M ε) = meshLog M ε / (2 * Real.pi * ρ) := by
        field_simp
      rw [hi]
      linarith

theorem node_count_le {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h) :
    ((Finset.Icc (-(cutoff R h : ℤ)) (cutoff R h)).card : ℝ) ≤ 2 * R / h + 3 := by
  have hn : (cutoff R h : ℝ) < R / h + 1 := Nat.ceil_lt_add_one (div_nonneg hR hh.le)
  rw [node_count]
  push_cast
  rw [mul_div_assoc]
  linarith

theorem budget_node_count (c ρ M C εm εt : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hεm : 0 < εm) :
    ((Finset.Icc (-(cutoff (tailRadius c C εt) (meshStep c ρ M εm) : ℤ))
      (cutoff (tailRadius c C εt) (meshStep c ρ M εm))).card : ℝ) ≤
      4 * (1 + (1 + c) * Real.sqrt (tailLog C εt) +
        (c / ρ) * Real.sqrt (tailLog C εt) * meshLog M εm) := by
  have hl := meshLog_pos hM hεm
  have hh := meshStep_pos hc hρ hM hεm
  have hR : 0 ≤ tailRadius c C εt := by unfold tailRadius; positivity
  have hn := node_count_le hR hh
  have hmul := mul_le_mul_of_nonneg_left (inv_meshStep_le hc hρ hM hεm)
    (show 0 ≤ 2 * tailRadius c C εt by positivity)
  have hbound : ((Finset.Icc (-(cutoff (tailRadius c C εt) (meshStep c ρ M εm) : ℤ))
      (cutoff (tailRadius c C εt) (meshStep c ρ M εm))).card : ℝ) ≤
      3 + (4 * c + 2) * Real.sqrt (tailLog C εt) +
        (2 / Real.pi) * ((c / ρ) * Real.sqrt (tailLog C εt) * meshLog M εm) := by
    apply hn.trans
    calc
      _ ≤ 2 * tailRadius c C εt * (1 + 1 / (2 * c) + meshLog M εm / (2 * Real.pi * ρ)) + 3 := by
        simpa only [div_eq_mul_inv, one_div, one_mul] using!
            _root_.add_le_add hmul (le_refl (3 : ℝ))
      _ = _ := by unfold tailRadius; field_simp; ring
  have hpi : 2 / Real.pi ≤ (4 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hp := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ (c / ρ) * Real.sqrt (tailLog C εt) * meshLog M εm by positivity)
  nlinarith [Real.sqrt_nonneg (tailLog C εt)]

theorem meshStep_le_scaled_min {c ρ M ε : ℝ} (hc : 0 < c) :
    meshStep c ρ M ε ≤ 2 * Real.pi * min 1 (min (2 * c) (ρ / meshLog M ε)) := by
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rcases min_choice (1 : ℝ) (min (2 * c) (ρ / meshLog M ε)) with he | he
  · rw [he, mul_one]
    exact (min_le_left _ _).trans hp
  · rw [he]
    rcases min_choice (2 * c) (ρ / meshLog M ε) with he' | he'
    · rw [he']
      have hs : meshStep c ρ M ε ≤ 2 * c := (min_le_right _ _).trans (min_le_left _ _)
      nlinarith
    · rw [he']
      have hs : meshStep c ρ M ε ≤ 2 * Real.pi * ρ / meshLog M ε :=
        (min_le_right _ _).trans (min_le_right _ _)
      convert! hs using 1
      ring

theorem budget_radius (c ρ M C εm εt : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hεm : 0 < εm) :
    radius (tailRadius c C εt) (meshStep c ρ M εm) ≤
      2 * Real.pi * (c * Real.sqrt (tailLog C εt) + min 1 (min (2 * c) (ρ / meshLog M εm))) := by
  have hh := meshStep_pos hc hρ hM hεm
  have hR : 0 ≤ tailRadius c C εt := by unfold tailRadius; positivity
  have hscale : tailRadius c C εt ≤ 2 * Real.pi * (c * Real.sqrt (tailLog C εt)) := by
    unfold tailRadius
    have hp := mul_nonneg hc.le (Real.sqrt_nonneg (tailLog C εt))
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ tailRadius c C εt + meshStep c ρ M εm := (radius_lt_add hR hh).le
    _ ≤ 2 * Real.pi * (c * Real.sqrt (tailLog C εt)) +
        2 * Real.pi * min 1 (min (2 * c) (ρ / meshLog M εm)) :=
      _root_.add_le_add hscale (meshStep_le_scaled_min hc)
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem operator_error_le_erfc (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 < R) :
    operatorTruncationError n b c d T H L R ≤
      tailConstant n b c d * (1 - erf (R / (2 * c))) :=
  (operatorTruncationError_le n b c d hb hc H L hH hL hT hR.le).trans
    (continuousTail_le_erfc n b c d hb hc hR)

theorem tailRadius_pos (c C ε : ℝ) (hc : 0 < c) : 0 < tailRadius c C ε := by
  have hl : 0 < tailLog C ε := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  unfold tailRadius
  positivity

theorem selected_error_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ εm εt : ℝ} (hT : 0 ≤ T) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (hbn : n = 0 ∨ ρ < b) (hεm : 0 < εm) (hεt : 0 < εt) :
    let M := mass n b c d ρ (T * ‖L‖)
    let C := tailConstant n b c d
    let h := meshStep c ρ M εm
    let R := tailRadius c C εt
    ‖(∫ x : ℝ, integrand n b c d T H L (x : ℂ)) -
      finiteIdeal n b c d T h H L (cutoff R h)‖ ≤ εm + εt := by
  (try dsimp only)
  have hM := mass_pos n b c d ρ (T * ‖L‖) hb hc hρ hbn
  have hC := tailConstant_pos n b c d hb hc
  have hh := meshStep_pos hc hρ₀ hM hεm
  have hR := tailRadius_pos c (tailConstant n b c d) εt hc
  apply (finite_error_le_continuousTail n b c d hb hc H L hH hL hT hρ₀ hρ hbn hh _).trans
  exact _root_.add_le_add (mesh_budget hc hρ₀ hM hεm)
    ((continuousTail_le_erfc n b c d hb hc hR).trans (tail_budget hc hC hεt))

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
