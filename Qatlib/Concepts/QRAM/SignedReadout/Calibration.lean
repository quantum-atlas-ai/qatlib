/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.HeraldedInterference

@[expose] public section

/-!
# Interference with an estimated success probability

When a probability estimate calibrates the reference, the target and the
reference retain different masses. The accepted Hadamard output weights each
normalized branch by the square root of its mass divided by the mean mass.
The resulting coordinate error is bounded by the relative imbalance between
the two masses. This bound applies to complex target and reference states.
It extends the interference step of [KerenidisLandmanPrakash2020],
Appendix G, to unequal success masses.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath

variable {I : Type} [Fintype I] [DecidableEq I]

/-- With an estimated calibration, the two decoded amplitudes carry the square-root
weights of their own success masses relative to the mean mass. -/
theorem heralded_interference_calibrated_entry (target decoder reference : Matrix I I ℂ)
    (S : Finset I) (q : ℝ) (seed : I) (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ)
    (hReference : reference ∈ Matrix.unitaryGroup I ℂ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed)) S) (b : Bool) (i : I) :
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let m := (p + q) / 2
    let U := heraldedInterferencePreparation target decoder reference S q
    let ψ := ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S)
    let φ := ApplyGate reference (Ket seed)
    PostMeasure (ApplyGate U (Ket (false, false, seed)))
        (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I))) (b, true, i) =
      (if b then (Real.sqrt p : ℂ) * ψ i - (Real.sqrt q : ℂ) * φ i
        else (Real.sqrt p : ℂ) * ψ i + (Real.sqrt q : ℂ) * φ i) / (2 * (Real.sqrt m : ℂ)) := by
  intro p m U ψ φ
  have hMem : (b, true, i) ∈ Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I)) := by simp
  have hRaw : ApplyGate decoder (Collapse (ApplyGate target (Ket seed)) S) i = (Real.sqrt p : ℂ) * ψ i := by
    change _ = (Real.sqrt p : ℂ) * ApplyGate decoder
      (((Real.sqrt p : ℂ)⁻¹) • Collapse (ApplyGate target (Ket seed)) S) i
    simp only [ApplyGate, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact (mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp).ne') _).symm
  change PostMeasure (ApplyGate (heraldedInterferencePreparation target decoder reference S q) (Ket (false, false, seed)))
    (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I))) (b, true, i) = _
  rw [PostMeasure, collapse_apply, ite_eq_left hMem, heralded_interference_success _ _ _ _ _ _ hDecoder hReference hq,
    heraldedInterferencePreparation, interference_preparation_entry, marked_preparation_success_slice,
    marked_reference_slice, hRaw]
  cases b <;> simp [m, φ, div_eq_mul_inv, _root_.mul_inv_rev] <;> ring

/-- The normalized square-root scale error is at most the original relative mass error. -/
private theorem sqrt_ratio_error_le (a m : ℝ) (ha : 0 ≤ a) (hm : 0 < m) :
    |Real.sqrt a / Real.sqrt m - 1| ≤ |a - m| / m := by
  let r := Real.sqrt a
  let s := Real.sqrt m
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs : 0 < s := Real.sqrt_pos.2 hm
  have hss : s ^ 2 = m := Real.sq_sqrt hm.le
  have hrr : r ^ 2 = a := Real.sq_sqrt ha
  have hFactor : |r - s| * (r + s) = |a - m| := by
    rw [← abs_of_nonneg (add_nonneg hr hs.le), ← abs_mul]
    congr 1
    calc
      (r - s) * (r + s) = r ^ 2 - s ^ 2 := by ring
      _ = a - m := by rw [hrr, hss]
  have hDiff : |r - s| * s ≤ |a - m| :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hr) (abs_nonneg _)).trans_eq hFactor
  change |r / s - 1| ≤ |a - m| / m
  rw [← div_self hs.ne', ← sub_div, abs_div, abs_of_pos hs]
  apply (div_le_div_iff₀ hs hm).mpr
  calc
    |r - s| * m = (|r - s| * s) * s := by rw [mul_assoc, ← pow_two, hss]
    _ ≤ |a - m| * s := mul_le_mul_of_nonneg_right hDiff hs.le

/-- Both branch weights differ from one by at most the mass imbalance divided by total mass. -/
theorem interference_calibration_weights (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
    let m := (p + q) / 2
    max |Real.sqrt p / Real.sqrt m - 1| |Real.sqrt q / Real.sqrt m - 1| ≤ |p - q| / (p + q) := by
  intro m
  have hm : 0 < m := half_pos (add_pos_of_pos_of_nonneg hp hq)
  have hTarget : p - m = (p - q) / 2 := by dsimp [m]; ring
  have hReference : q - m = -((p - q) / 2) := by dsimp [m]; ring
  apply max_le
  · refine (sqrt_ratio_error_le p m hp.le hm).trans_eq ?_
    rw [hTarget, abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    change (|p - q| / 2) / ((p + q) / 2) = _
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  · refine (sqrt_ratio_error_le q m hq hm).trans_eq ?_
    rw [hReference, abs_neg, abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    change (|p - q| / 2) / ((p + q) / 2) = _
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

end Qatlib.Concepts.QRAM.SignedReadout
