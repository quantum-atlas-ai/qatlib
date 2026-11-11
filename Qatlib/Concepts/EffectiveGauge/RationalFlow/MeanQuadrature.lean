/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Left-endpoint quadrature for the source-curvature moment

This is the one-dimensional estimate used successively in the three
coordinate directions. The integral is the actual Lebesgue interval
integral, rather than an error field supplied by the caller.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The exact real left-endpoint sum whose finite rational samples will approximate. -/
def meanLeftSum (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range N, f ((k : ℝ)/(N : ℝ)))/(N : ℝ)

/-- A unit-interval left-endpoint sum of a Lipschitz function has error at
most `D/N`. This retains a conservative constant for tensor composition. -/
theorem meanLeftSum_error (N : ℕ) (hN : 0<N) (f : ℝ → ℝ) (hf : Continuous f)
    (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x-f y| ≤ D*|x-y|) :
    |(∫ x in (0 : ℝ)..1, f x)-meanLeftSum N f| ≤ D/(N : ℝ) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  let t := fun k : ℕ => (k : ℝ)/(N : ℝ)
  have hstep (k : ℕ) : t (k+1)-t k=1/(N : ℝ) := by dsimp [t]; push_cast; ring
  have hcell (k : ℕ) (hk : k<N) : 0 ≤ t k ∧ t (k+1) ≤ 1 := by
    constructor
    · dsimp [t]; positivity
    · dsimp [t]
      apply (div_le_one hn).mpr
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hmono (k : ℕ) : t k ≤ t (k+1) := by
    have hpos : 0 ≤ 1/(N : ℝ) := by positivity
    linarith [hstep k]
  have herr (k : ℕ) (hk : k<N) :
      |(∫ x in t k..t (k+1), f x)-(1/(N : ℝ))*f (t k)| ≤ (D/(N : ℝ))*(1/(N : ℝ)) := by
    have hc := hcell k hk
    have hnorm : ∀ x ∈ Ι (t k) (t (k+1)), ‖f x-f (t k)‖ ≤ D/(N : ℝ) := by
      intro x hx
      rw [uIoc_of_le (hmono k)] at hx
      have hxunit : x ∈ Icc (0 : ℝ) 1 := ⟨le_trans hc.1 hx.1.le,le_trans hx.2 hc.2⟩
      have htunit : t k ∈ Icc (0 : ℝ) 1 := ⟨hc.1,le_trans (hmono k) hc.2⟩
      have hd : |x-t k| ≤ 1/(N : ℝ) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
        linarith [hstep k,hx.2]
      have hp := (hLip x hxunit (t k) htunit).trans (mul_le_mul_of_nonneg_left hd hD)
      simpa [Real.norm_eq_abs,div_eq_mul_inv] using hp
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const] at hi
    rw [hstep k,Real.norm_eq_abs,smul_eq_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/(N : ℝ))] at hi
    exact hi
  have hsum : (∑ k ∈ Finset.range N, ∫ x in t k..t (k+1), f x)=∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (fun k (_hk : k<N) => hf.intervalIntegrable (t k) (t (k+1)))
    simpa [t,hn.ne'] using h
  have hsamples : (∑ k ∈ Finset.range N, (1/(N : ℝ))*f (t k))=meanLeftSum N f := by
    simp [meanLeftSum,t,Finset.mul_sum,div_eq_mul_inv,mul_comm]
  rw [← hsum,← hsamples,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range N, |(∫ x in t k..t (k+1), f x)-(1/(N : ℝ))*f (t k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, (D/(N : ℝ))*(1/(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact herr k (Finset.mem_range.mp hk)
    _ = D/(N : ℝ) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      field_simp

end Qatlib.Concepts.EffectiveGauge.RationalFlow
