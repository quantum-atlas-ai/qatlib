/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AuxRegulator
import Qatlib.Foundations.CbmdAnalysis.Core.FinitePoleBounds
import Mathlib.Analysis.PSeries
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open scoped BigOperators

theorem auxWeight_norm (s : Finset ℂ) {a : ℝ} (ha : 0 < a) (k : ℤ) :
    ‖auxWeight s a k‖ =
      (|Real.exp (-2 * Real.pi * a) - 1| * ∏ p ∈ s, ‖-Complex.I - p‖) /
        (2 * Real.pi * a *
          (‖(((k : ℝ) / a : ℝ) : ℂ) + Complex.I‖ *
            ∏ p ∈ s, ‖(((k : ℝ) / a : ℝ) : ℂ) - p‖)) := by
  simp only [auxWeight, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    abs_of_pos ha, auxRegulator_norm]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

def auxWeightTailConstant (s : Finset ℂ) (a : ℝ) : ℝ :=
  2 * a * |Real.exp (-2 * Real.pi * a) - 1| *
    (∏ p ∈ s, ‖-Complex.I - p‖) / Real.pi

theorem auxWeightTailConstant_nonneg (s : Finset ℂ) {a : ℝ} (ha : 0 < a) :
    0 ≤ auxWeightTailConstant s a := by
  unfold auxWeightTailConstant
  positivity

theorem auxWeight_norm_le_inv_sq (s : Finset ℂ) (hs : s.Nonempty) {a : ℝ} (ha : 0 < a)
    (k : ℤ) (hk : 2 * finitePoleRadius s ≤ |(k : ℝ) / a|) :
    ‖auxWeight s a k‖ ≤ auxWeightTailConstant s a * (1 / (k : ℝ) ^ 2) := by
  let x : ℝ := (k : ℝ) / a
  let B := finitePoleRadius s
  let N := |Real.exp (-2 * Real.pi * a) - 1| * ∏ p ∈ s, ‖-Complex.I - p‖
  let D := ‖(x : ℂ) + Complex.I‖ * ∏ p ∈ s, ‖(x : ℂ) - p‖
  have hB : 1 ≤ B := finitePoleRadius_ge_one s
  have hx : 2 * B ≤ |x| := hk
  have hxpos : 0 < |x| := by linarith
  have hxne : x ≠ 0 := abs_pos.mp hxpos
  have hkne : (k : ℝ) ≠ 0 := by
    intro h
    exact hxne (by simp [x, h])
  have hD : x ^ 2 / 4 ≤ D := by
    have hl := finite_pole_denominator_lower s hs B hB
      (norm_le_finitePoleRadius s) (x : ℂ)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using! (show B + 1 ≤ |x| by linarith))
    simp only [Complex.norm_real, Real.norm_eq_abs] at hl
    dsimp only [D]
    nlinarith [sq_abs x, sq_nonneg (|x| / 2 - B)]
  have hx2 : 0 < x ^ 2 / 4 := by positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hbase : 0 < 2 * Real.pi * a := by positivity
  rw [auxWeight_norm s ha]
  change N / (2 * Real.pi * a * D) ≤ _
  calc
    _ ≤ N / (2 * Real.pi * a * (x ^ 2 / 4)) :=
      div_le_div_of_nonneg_left hN (mul_pos hbase hx2)
        (mul_le_mul_of_nonneg_left hD hbase.le)
    _ = auxWeightTailConstant s a * (1 / (k : ℝ) ^ 2) := by
      dsimp [N, x, auxWeightTailConstant]
      field_simp
      ring

theorem auxWeight_norm_le_inv_sq_eventually (s : Finset ℂ) (hs : s.Nonempty)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℤ in Filter.cofinite,
      ‖auxWeight s a k‖ ≤ auxWeightTailConstant s a * (1 / (k : ℝ) ^ 2) := by
  let N : ℕ := ⌈2 * a * finitePoleRadius s⌉₊
  have hN : 2 * a * finitePoleRadius s ≤ (N : ℝ) := Nat.le_ceil _
  filter_upwards [(Finset.Icc (-(N : ℤ)) (N : ℤ)).finite_toSet.compl_mem_cofinite] with k hk
  apply auxWeight_norm_le_inv_sq s hs ha k
  have hki : (N : ℤ) < |k| := by
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, ← abs_le, not_le] using! hk
  have hkr : (N : ℝ) < |(k : ℝ)| := by exact_mod_cast hki
  rw [abs_div, abs_of_pos ha]
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem auxWeight_norm_summable (s : Finset ℂ) (hs : s.Nonempty) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => ‖auxWeight s a k‖) := by
  have hg := (Real.summable_one_div_int_pow.mpr (by omega : 1 < (2 : ℕ))).mul_left
    (auxWeightTailConstant s a)
  apply hg.of_norm_bounded_eventually
  simpa only [norm_norm] using! auxWeight_norm_le_inv_sq_eventually s hs ha

theorem auxWeight_summable (s : Finset ℂ) (hs : s.Nonempty) {a : ℝ} (ha : 0 < a) :
    Summable (auxWeight s a) := (auxWeight_norm_summable s hs ha).of_norm

theorem auxWeight_smul_norm_summable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset ℂ) (hs : s.Nonempty) {a : ℝ} (ha : 0 < a)
    (U : ℂ → E) (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) :
    Summable (fun k : ℤ => ‖auxWeight s a k • U (((k : ℝ) / a : ℝ) : ℂ)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) (auxWeight_norm_summable s hs ha)
  rw [norm_smul]
  simpa only [mul_one] using!
    mul_le_mul_of_nonneg_left (hUreal ((k : ℝ) / a)) (norm_nonneg (auxWeight s a k))

theorem auxWeight_smul_summable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (s : Finset ℂ) (hs : s.Nonempty)
    {a : ℝ} (ha : 0 < a) (U : ℂ → E) (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) :
    Summable (fun k : ℤ => auxWeight s a k • U (((k : ℝ) / a : ℝ) : ℂ)) :=
  (auxWeight_smul_norm_summable s hs ha U hUreal).of_norm

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
