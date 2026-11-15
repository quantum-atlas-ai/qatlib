/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LaurentPolys.ProfileFftBound.PositiveLaurentAnnulus

open scoped BigOperators
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- For a positive radius between the reciprocal of `r` and `r`, each power through `m` differs
from one by at most `r^m-1`. -/
private theorem real_power_radial_bound {m : ℕ} (r t : ℝ)
    (hr : 1 ≤ r) (ht : 0 < t) (htl : r⁻¹ ≤ t) (htu : t ≤ r)
    (k : ℕ) (hk : k ≤ m) : |t ^ k - 1| ≤ r ^ m - 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hmono : r ^ k ≤ r ^ m := pow_le_pow_right₀ hr hk
  have hupper : t ^ k ≤ r ^ m :=
    (pow_le_pow_left₀ ht.le htu k).trans hmono
  have hlowerK : (r ^ k)⁻¹ ≤ t ^ k := by
    simpa only [inv_pow] using
      (pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) htl k)
  have hlower : (r ^ m)⁻¹ ≤ t ^ k :=
    ((inv_le_inv₀ (pow_pos hr0 m) (pow_pos hr0 k)).mpr hmono).trans hlowerK
  have hrecip : 2 - r ^ m ≤ (r ^ m)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (pow_pos hr0 m)).mpr
    nlinarith [sq_nonneg (r ^ m - 1)]
  apply abs_le.mpr
  constructor <;> linarith

/-- Radially scaling a unit complex number within the specified annulus changes each power
through `m` by norm at most `r^m-1`. -/
private theorem norm_power_radial_bound {m : ℕ} (r t : ℝ)
    (hr : 1 ≤ r) (ht : 0 < t) (htl : r⁻¹ ≤ t) (htu : t ≤ r)
    (u : ℂ) (hu : ‖u‖ = 1) (k : ℕ) (hk : k ≤ m) :
    ‖((t : ℂ) * u) ^ k - u ^ k‖ ≤ r ^ m - 1 := by
  rw [mul_pow]
  have he : (t : ℂ) ^ k * u ^ k - u ^ k =
      ((t ^ k - 1 : ℝ) : ℂ) * u ^ k := by
    rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one]
    ring
  rw [he, norm_mul, norm_pow, hu, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact real_power_radial_bound r t hr ht htl htu k hk

/-- For nonnegative Laurent coefficients, a positive unit circle lower bound extends to half
that bound on any annulus satisfying the stated radial variation budget. -/
theorem positive_profile_annulus
    (m : ℕ) (c : Fin (m + 1) → ℝ) (κ r : ℝ)
    (hc : ∀ i, 0 ≤ c i) (_hκ : 0 < κ) (hr : 1 < r)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → κ ≤ (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re) :
    let M := c 0 + 2 * ∑ i : Fin (m + 1), if i.val = 0 then 0 else c i
    M * (r ^ m - 1) ≤ κ / 2 →
    ∀ z : ℂ, r⁻¹ ≤ ‖z‖ → ‖z‖ ≤ r →
      ‖Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z - Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c (z / (‖z‖ : ℂ))‖ ≤ M * (r ^ m - 1) ∧
      κ / 2 ≤ (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re := by
  classical
  (try dsimp only)
  intro hbudget z hzl hzh
  let M := c 0 + 2 * ∑ i : Fin (m + 1), if i.val = 0 then 0 else c i
  let A := r ^ m - 1
  let t := ‖z‖
  let u := z / (‖z‖ : ℂ)
  change M * A ≤ κ / 2 at hbudget
  change ‖Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z - Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c u‖ ≤ M * A ∧
    κ / 2 ≤ (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have ht : 0 < t := lt_of_lt_of_le (inv_pos.mpr hr0) hzl
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self ht.ne'
  have hzu : z = (t : ℂ) * u := by
    dsimp only [u, t]
    exact (mul_div_cancel₀ z htC).symm
  have hitl : r⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hr0 ht).mpr hzh
  have hith : t⁻¹ ≤ r := by
    have hi := (inv_le_inv₀ ht (inv_pos.mpr hr0)).mpr hzl
    simpa only [inv_inv] using hi
  have hA : 0 ≤ A := sub_nonneg.mpr (one_le_pow₀ hr.le)
  have hpos (k : ℕ) (hk : k ≤ m) : ‖z ^ k - u ^ k‖ ≤ A := by
    rw [hzu]
    exact norm_power_radial_bound r t hr.le ht hzl hzh u hu k hk
  have hneg (k : ℕ) (hk : k ≤ m) : ‖(z⁻¹) ^ k - (u⁻¹) ^ k‖ ≤ A := by
    have he : z⁻¹ = ((t⁻¹ : ℝ) : ℂ) * u⁻¹ := by
      rw [hzu, mul_inv, ← Complex.ofReal_inv]
    rw [he]
    exact norm_power_radial_bound r t⁻¹ hr.le (inv_pos.mpr ht) hitl hith
      u⁻¹ (by simp only [norm_inv, hu, inv_one]) k hk
  have hterm (i : Fin (m + 1)) :
      ‖(if i.val = 0 then (c i : ℂ)
          else (c i : ℂ) * (z ^ (i.val : ℤ) + z ^ (-(i.val : ℤ)))) -
        (if i.val = 0 then (c i : ℂ)
          else (c i : ℂ) * (u ^ (i.val : ℤ) + u ^ (-(i.val : ℤ))))‖ ≤
        (if i.val = 0 then 0 else 2 * c i) * A := by
    by_cases hi : i.val = 0
    · simp only [hi, ite_true, sub_self, norm_zero, zero_mul, le_refl]
    · simp only [hi, ite_false]
      have hik : i.val ≤ m := by have hiLt := i.isLt; omega
      have hpair :
          ‖(z ^ (i.val : ℤ) + z ^ (-(i.val : ℤ))) -
            (u ^ (i.val : ℤ) + u ^ (-(i.val : ℤ)))‖ ≤ 2 * A := by
        have he :
            (z ^ (i.val : ℤ) + z ^ (-(i.val : ℤ))) -
              (u ^ (i.val : ℤ) + u ^ (-(i.val : ℤ))) =
            (z ^ i.val - u ^ i.val) + ((z⁻¹) ^ i.val - (u⁻¹) ^ i.val) := by
          simp only [_root_.zpow_neg, zpow_natCast, ← inv_pow]
          ring
        rw [he]
        calc
          _ ≤ ‖z ^ i.val - u ^ i.val‖ + ‖(z⁻¹) ^ i.val - (u⁻¹) ^ i.val‖ :=
            norm_add_le _ _
          _ ≤ A + A := add_le_add (hpos i.val hik) (hneg i.val hik)
          _ = 2 * A := by ring
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc i)]
      calc
        _ ≤ c i * (2 * A) := mul_le_mul_of_nonneg_left hpair (hc i)
        _ = (2 * c i) * A := by ring
  have hmass :
      (∑ i : Fin (m + 1), if i.val = 0 then 0 else 2 * c i) =
        2 * ∑ i : Fin (m + 1), if i.val = 0 then 0 else c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val = 0 <;> simp [hi]
  have hdiff : ‖Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z - Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c u‖ ≤ M * A := by
    unfold Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (m + 1),
          ‖(if i.val = 0 then (c i : ℂ)
              else (c i : ℂ) * (z ^ (i.val : ℤ) + z ^ (-(i.val : ℤ)))) -
            (if i.val = 0 then (c i : ℂ)
              else (c i : ℂ) * (u ^ (i.val : ℤ) + u ^ (-(i.val : ℤ))))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin (m + 1), (if i.val = 0 then 0 else 2 * c i) * A :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (2 * ∑ i : Fin (m + 1), if i.val = 0 then 0 else c i) * A := by
        rw [← Finset.sum_mul, hmass]
      _ ≤ M * A := by
        apply mul_le_mul_of_nonneg_right ?_ hA
        dsimp only [M]
        linarith [hc 0]
  refine ⟨hdiff, ?_⟩
  have hre : |(Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z).re - (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c u).re| ≤ M * A := by
    have hh :=
        Complex.abs_re_le_norm
        (Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c z - Qatlib.Concepts.OrderedOracle.TiSdpBridge.laurentEval c u)
    rw [Complex.sub_re] at hh
    exact hh.trans hdiff
  have hlower := (abs_le.mp hre).1
  have hgap := hcircle u hu
  linarith

end Qatlib.Concepts.LaurentPolys.ProfileFftBound.PositiveLaurentAnnulus
