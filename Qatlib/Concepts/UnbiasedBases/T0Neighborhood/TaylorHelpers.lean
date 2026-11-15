/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open MeasureTheory Set

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood.Calculus

/-- Bounds the first-order Taylor remainder from zero to one by half a uniform bound on the
second derivative in a real Banach space. -/
theorem unit_interval_taylor_bound {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f v a : ℝ → E) (M : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hBound : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ M) :
    ‖f 1 - f 0 - v 0‖ ≤ M / 2 := by
  let g : ℝ → E := fun t => f t + (1 - t) • v t
  have hG : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g ((1 - t) • a t) t := by
    intro t ht
    have hWeight : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using! (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    convert! (hf t ht).add (hWeight.smul (hv t ht)) using 1
    try simp only [neg_one_smul]
    abel
  have hWeightContinuous : Continuous (fun t : ℝ => 1 - t) :=
    continuous_const.sub continuous_id
  have hIntegrable : IntervalIntegrable (fun t : ℝ => (1 - t) • a t) volume 0 1 :=
    (hWeightContinuous.continuousOn.smul ha).intervalIntegrable_of_Icc (by norm_num)
  have hIdentity : (∫ t in (0 : ℝ)..1, (1 - t) • a t) = f 1 - f 0 - v 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hG t (by simpa using ht)) hIntegrable
    simpa [g, sub_sub] using hFTC
  have hMajorant : IntervalIntegrable (fun t : ℝ => (1 - t) * M) volume 0 1 :=
    (hWeightContinuous.mul continuous_const).intervalIntegrable 0 1
  have hAffineIntegral : (∫ t in (0 : ℝ)..1, (1 - t) * M) = M / 2 := by
    have hPrimitive (t : ℝ) : HasDerivAt (fun s : ℝ => M * (s - s ^ 2 / 2))
        ((1 - t) * M) t := by
      convert! ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).const_mul M
        using 1
      try simp only [id_eq]
      ring
    calc
      _ = M * (1 - 1 ^ 2 / 2) - M * (0 - 0 ^ 2 / 2) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => M * (s - s ^ 2 / 2))
          (f' := fun t : ℝ => (1 - t) * M) (fun t _ => hPrimitive t) hMajorant
      _ = M / 2 := by ring
  rw [← hIdentity]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - t) * M := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ hMajorant
      exact Filter.Eventually.of_forall fun t ht => by
        have htClosed : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        exact mul_le_mul_of_nonneg_left (hBound t htClosed) (sub_nonneg.mpr ht.2)
    _ = M / 2 := hAffineIntegral

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood.Calculus
