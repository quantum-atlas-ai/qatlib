/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs

/-!
# Logarithmic estimates for multiproduct coefficients

This module translates `FactorialLowerBound` and `EtaMaxProperty` into logarithmic inequalities
for the coefficient proof. It also bounds the numerical constants arising at interior and
endpoint indices by log √2. See [ChildsWiebe2012] for the multiproduct and linear-combination
simulation framework.

## Main statements

* `multiproduct_factorial_log_lower`: Assuming `FactorialLowerBound` and n > 0, log(n!) is at
  least log(2πn) / 2 + n log n − n − 1 / 13.
* `multiproduct_eta_log_ratio`: Assuming η > 0, `EtaMaxProperty η`, and 0 < p < K, bounds 2K log
  p − ((K + p) log(K + p) + (K − p) log(K − p)) by K log η.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Assuming `FactorialLowerBound` and n > 0, log(n!) is at least log(2πn) / 2 + n log n − n − 1
/ 13. -/
theorem multiproduct_factorial_log_lower (hF : FactorialLowerBound) (n : ℕ) (hn : 0 < n) :
    Real.log (2*Real.pi*(n : ℝ))/2 + (n : ℝ)*Real.log n - n - 1/13 ≤
      Real.log (n.factorial : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < 2*Real.pi*(n : ℝ) := by positivity
  have hp : 0 < Real.sqrt (2*Real.pi*(n : ℝ)) * (n : ℝ)^(n : ℝ) *
      Real.exp (-((n : ℝ)+1/13)) := by positivity
  have h := Real.log_le_log hp (hF n)
  rw [Real.log_mul (ne_of_gt (mul_pos (Real.sqrt_pos.mpr hs) (Real.rpow_pos_of_pos hnR _)))
      (ne_of_gt (Real.exp_pos _)),
    Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr hs)) (ne_of_gt (Real.rpow_pos_of_pos hnR _)),
    Real.log_sqrt hs.le, Real.log_rpow hnR, Real.log_exp] at h
  linarith

/-- Assuming η > 0, `EtaMaxProperty η`, and 0 < p < K, bounds 2K log p − ((K + p) log(K + p) +
(K − p) log(K − p)) by K log η. -/
theorem multiproduct_eta_log_ratio (η K p : ℝ) (_hη : 0 < η)
    (hE : EtaMaxProperty η) (hK : 0 < K) (hp : 0 < p) (hpK : p < K) :
    2*K*Real.log p - ((K+p)*Real.log (K+p)+(K-p)*Real.log (K-p)) ≤ K*Real.log η := by
  let lam := p/K
  have hl0 : 0 < lam := div_pos hp hK
  have hl1 : lam < 1 := (div_lt_one hK).mpr hpK
  have hplus : 0 < 1+lam := by linarith
  have hminus : 0 < 1-lam := by linarith
  have hden : 0 < (1+lam)^(1+lam : ℝ)*(1-lam)^(1-lam : ℝ) := by positivity
  have hratio : 0 < lam^2/((1+lam)^(1+lam : ℝ)*(1-lam)^(1-lam : ℝ)) := by positivity
  have h := Real.log_le_log hratio (hE lam hl0.le hl1)
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos hl0)) (ne_of_gt hden), Real.log_pow,
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hplus _))
      (ne_of_gt (Real.rpow_pos_of_pos hminus _)),
    Real.log_rpow hplus, Real.log_rpow hminus] at h
  have h1 : 1+lam = (K+p)/K := by dsimp [lam]; field_simp
  have h2 : 1-lam = (K-p)/K := by dsimp [lam]; field_simp
  have hL : Real.log lam = Real.log p - Real.log K := Real.log_div hp.ne' hK.ne'
  have hLP : Real.log (1+lam) = Real.log (K+p)-Real.log K := by
    rw [h1, Real.log_div (by linarith : K+p ≠ 0) hK.ne']
  have hLM : Real.log (1-lam) = Real.log (K-p)-Real.log K := by
    rw [h2, Real.log_div (by linarith : K-p ≠ 0) hK.ne']
  rw [hL, hLP, hLM] at h
  have hm := mul_le_mul_of_nonneg_left h hK.le
  have hlK : K*lam = p := by dsimp [lam]; field_simp
  norm_num at hm
  have he : K*(2*(Real.log p-Real.log K) -
      ((1+lam)*(Real.log (K+p)-Real.log K)+(1-lam)*(Real.log (K-p)-Real.log K))) =
      2*K*Real.log p - ((K+K*lam)*Real.log (K+p)+(K-K*lam)*Real.log (K-p)) := by ring
  rw [he, hlK] at hm
  exact hm

/-- The constant 2 log 2 − log(2π) + 2 / 13 is at most log √2. -/
theorem multiproduct_interior_log_constant :
    2*Real.log 2 - Real.log (2*Real.pi) + 2/13 ≤ Real.log (Real.sqrt 2) := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ := Real.pi_gt_three
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 2*Real.pi)
  have hl2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow] at hlo
  norm_num at hl2 hlo
  linarith

/-- The constant 2 log 2 − log(4π) / 2 + 1 / 13 is at most log √2. -/
theorem multiproduct_endpoint_log_constant :
    2*Real.log 2 - Real.log (4*Real.pi)/2 + 1/13 ≤ Real.log (Real.sqrt 2) := by
  have hπ := Real.pi_gt_three
  have hx : (0 : ℝ) < Real.pi/2 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hi : (Real.pi/2)⁻¹ ≤ (2/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hx).mpr
    linarith
  have hlog : Real.log (4*Real.pi) = 3*Real.log 2 + Real.log (Real.pi/2) := by
    rw [show 4*Real.pi = (2 : ℝ)^3*(Real.pi/2) by ring,
      Real.log_mul (by norm_num) hx.ne', Real.log_pow]
    norm_num
  rw [hlog, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- If η > 1 / 4, then log η is at least −2 log 2. -/
theorem multiproduct_eta_log_lower (η : ℝ) (hη : 1/4 < η) :
    -(2*Real.log 2) ≤ Real.log η := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1/4) hη.le
  have he : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
  rwa [he] at h

end Qatlib.Papers.HamLCUSim12.Multiproduct
