/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.SignedClock.ClockSpectral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset

def heatKernel {ι : Type*} [Fintype ι] (p lam : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ l, p l * Real.exp (-(lam l * t))

theorem heatKernel_nonneg {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (t : ℝ) : 0 ≤ heatKernel p lam t :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (Real.exp_pos _).le

theorem heatKernel_single_le {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (j : ι) (t : ℝ) :
    p j * Real.exp (-(lam j * t)) ≤ heatKernel p lam t := by
  unfold heatKernel
  exact Finset.single_le_sum
    (f := fun l : ι => p l * Real.exp (-(lam l * t)))
    (fun l _ => mul_nonneg (hp l) (Real.exp_pos _).le) (Finset.mem_univ j)

theorem heatKernel_le_of_supp {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (hmass : ∑ l, p l = 1) (mu : ℝ)
    (hsupp : ∀ l, 0 < p l → mu ≤ lam l) (t : ℝ) (ht : 0 ≤ t) :
    heatKernel p lam t ≤ Real.exp (-(mu * t)) := by
  unfold heatKernel
  have hterm : ∀ l : ι, p l * Real.exp (-(lam l * t)) ≤ p l * Real.exp (-(mu * t)) := by
    intro l
    rcases lt_or_eq_of_le (hp l) with hl | hl
    · have hlam : mu ≤ lam l := hsupp l hl
      have hmono : -(lam l * t) ≤ -(mu * t) := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono) (le_of_lt hl)
    · rw [← hl]
      simp
  calc ∑ l, p l * Real.exp (-(lam l * t))
      ≤ ∑ l, p l * Real.exp (-(mu * t)) := Finset.sum_le_sum fun l _ => hterm l
    _ = (∑ l, p l) * Real.exp (-(mu * t)) := by rw [Finset.sum_mul]
    _ = Real.exp (-(mu * t)) := by rw [hmass, one_mul]

theorem heat_decay_forces_lower {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (mu C t : ℝ) (j : ι) (hj : 0 < p j)
    (hdecay : heatKernel p lam t ≤ C * Real.exp (-(mu * t))) :
    Real.exp (-(lam j * t)) ≤ (C / p j) * Real.exp (-(mu * t)) := by
  have hle : p j * Real.exp (-(lam j * t)) ≤ C * Real.exp (-(mu * t)) :=
    le_trans (heatKernel_single_le p lam hp j t) hdecay
  have hle' : Real.exp (-(lam j * t)) * p j ≤ C * Real.exp (-(mu * t)) := by
    calc Real.exp (-(lam j * t)) * p j = p j * Real.exp (-(lam j * t)) := mul_comm _ _
      _ ≤ C * Real.exp (-(mu * t)) := hle
  rw [div_mul_eq_mul_div, le_div_iff₀ hj]
  exact hle'

theorem residual_of_two_sided {c w mu nu t : ℝ}
    (hlow : w * Real.exp (-(mu * t)) ≤ c)
    (hup : c ≤ w * Real.exp (-(mu * t)) + Real.exp (-(nu * t))) :
    |c - w * Real.exp (-(mu * t))| ≤ Real.exp (-(nu * t)) := by
  have hpos : 0 < Real.exp (-(nu * t)) := Real.exp_pos _
  rw [abs_le]
  constructor <;> linarith

theorem mu_corrected_pos : 0 < (4 : ℝ) - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  linarith

theorem nu_gt_mu_corrected {M : ℕ} (hM : 3 ≤ M) :
    (4 : ℝ) - 2 * Real.sqrt 2 <
      4 - 2 * Real.sqrt 2 * Real.cos (Real.pi / M) := by
  have hcos : Real.cos (Real.pi / M) < 1 :=
    Qatlib.Papers.BQPMixSparse06.SignedClock.cos_pi_div_lt_one hM
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  nlinarith

theorem heat_T_threshold {M eta mu nu : ℝ} (hM : 0 < M) (heta : 0 < eta)
    (hnu : mu < nu) :
    Real.exp (-((nu - mu) * (Real.log (M / eta) / (nu - mu)))) = eta / M := by
  have hratio : 0 < M / eta := div_pos hM heta
  have hne : nu - mu ≠ 0 := ne_of_gt (sub_pos.mpr hnu)
  rw [mul_div_cancel₀ _ hne, Real.exp_neg, Real.exp_log hratio]
  field_simp

def heatTest (C mu T x : ℝ) : ℝ := Real.exp (-(C * x - mu) * T)

theorem heatTest_le_one {C mu T x : ℝ} (hC : 0 < C) (hT : 0 ≤ T)
    (hx : mu / C ≤ x) : heatTest C mu T x ≤ 1 := by
  unfold heatTest
  rw [Real.exp_le_one_iff]
  have hcx : mu ≤ C * x := by
    have h := (div_le_iff₀ hC).mp hx
    linarith
  nlinarith

theorem expNeg_lipschitz :
    LipschitzOnWith 1 (fun u : ℝ => Real.exp (-u)) (Set.Ici (0 : ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ)
    (s := Set.Ici (0 : ℝ)) (f := fun u : ℝ => Real.exp (-u)) (C := 1)
  · intro x hx
    exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).differentiableAt
  · intro x hx
    have hderiv : deriv (fun u : ℝ => Real.exp (-u)) x = -Real.exp (-x) := by
      simpa using! ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).deriv
    rw [hderiv, nnnorm_neg]
    rw [Real.nnnorm_of_nonneg (Real.exp_pos (-x)).le]
    have hx0 : (0 : ℝ) ≤ x := hx
    have hle : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact_mod_cast hle
  · exact convex_Ici (0 : ℝ)

theorem abs_expNeg_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  have h := expNeg_lipschitz.dist_le_mul u hu v hv
  simpa [Real.dist_eq] using h

theorem heatTest_lipschitz {C mu T : ℝ} (hC : 0 < C) (hT : 0 ≤ T)
    {x y : ℝ} (hx : mu / C ≤ x) (hy : mu / C ≤ y) :
    |heatTest C mu T x - heatTest C mu T y| ≤ C * T * |x - y| := by
  have hux : 0 ≤ (C * x - mu) * T := by
    have : 0 ≤ C * x - mu := by
      have := (div_le_iff₀ hC).mp hx
      linarith
    exact mul_nonneg this hT
  have hvy : 0 ≤ (C * y - mu) * T := by
    have : 0 ≤ C * y - mu := by
      have := (div_le_iff₀ hC).mp hy
      linarith
    exact mul_nonneg this hT
  have hstep : |heatTest C mu T x - heatTest C mu T y| ≤
      |(C * x - mu) * T - (C * y - mu) * T| := by
    unfold heatTest
    have h := abs_expNeg_sub_le hux hvy
    convert h using 2 <;> ring_nf
  have hval : |(C * x - mu) * T - (C * y - mu) * T| = C * T * |x - y| := by
    have hrew : (C * x - mu) * T - (C * y - mu) * T = T * (C * (x - y)) := by ring
    rw [hrew, abs_mul, abs_mul, abs_of_pos hC, abs_of_nonneg hT]
    ring
  rw [hval] at hstep
  exact hstep

end Qatlib.Papers.BQPMixSparse06.MainResults
