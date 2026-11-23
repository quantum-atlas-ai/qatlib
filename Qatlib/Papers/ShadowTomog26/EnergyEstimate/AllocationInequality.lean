/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Qatlib.Foundations.GraphFraction.CoverLP.PowerAllocation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Optimal fixed-total allocations for power-weighted amplitude sums

For nonzero real coefficients `c` and strictly positive allocations `n` with fixed total
`T = ∑ i, n i`, the amplitude sum `|c i| / √(n i)` is minimized by allocating the
total proportionally to the coefficient masses `|c i|^(2/3)`. The minimum value is
`(C)^(3/2) / √T` for `C = ∑ i, |c i|^(2/3)`, and every other positive allocation of
the same total gives a sum at least this large.

Equation (68) of [XuEtAl2026] prints this comparison in the reverse direction for arbitrary
allocations; the lower bound proved here is the direction valid for all positive
allocations, and the distinguished allocation attains it.

## Main statements

* `magnitude_allocation_lower_bound`: the general lower bound at fixed total `T`.
* `magnitude_allocation_attains`: the proportional allocation attains that bound.
* `magnitude_allocation_min`: the minimum value equals `(C)^(3/2) / √T`, attained.

## References

* [XuEtAl2026], [arXiv:2608.08429v1](https://arxiv.org/abs/2608.08429v1)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ShadowTomog26.EnergyEstimate

open scoped BigOperators
open Qatlib.Foundations.GraphFraction.CoverLP

variable {V : Type*} [Fintype V]

/-- The total coefficient mass `∑ i, |c i|^(2/3)` used by optimal power allocations. -/
def coeffPowerSum (c : V → ℝ) : ℝ := ∑ i, |c i| ^ ((2:ℝ)/3)

/-- The proportional allocation of a budget `T` in the ratio `|c i|^(2/3)`; its
normalization `coeffPowerSum c` is positive whenever some coefficient is nonzero. -/
def powerAllocation (c : V → ℝ) (T : ℝ) : V → ℝ :=
  fun i => T * |c i| ^ ((2:ℝ)/3) / coeffPowerSum c

/-- The coefficient mass sum is nonnegative. -/
theorem coeffPowerSum_nonneg (c : V → ℝ) : 0 ≤ coeffPowerSum c := by
  unfold coeffPowerSum
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _

/-- On a nonempty coordinate type, a coefficient family with no zero entry has a
strictly positive coefficient mass sum. -/
theorem coeffPowerSum_pos [Nonempty V] (c : V → ℝ) (hc : ∀ i, c i ≠ 0) :
    0 < coeffPowerSum c := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty V)
  have h1 : 0 < |c i0| ^ ((2:ℝ)/3) :=
    Real.rpow_pos_of_pos (abs_pos.mpr (hc i0)) _
  exact lt_of_lt_of_le h1 (Finset.single_le_sum
    (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i0))

/-- A nonnegative real to the power `3/2` is the number times its square root. -/
theorem rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ ((3:ℝ)/2) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0), Real.sqrt_zero, mul_zero]
  have h12 : ((1:ℝ)/2) + 1 = (3:ℝ)/2 := by norm_num
  have hsqrt : x ^ ((1:ℝ)/2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  calc x ^ ((3:ℝ)/2) = x ^ (((1:ℝ)/2) + 1) := by rw [h12]
    _ = x ^ ((1:ℝ)/2) * x ^ (1:ℝ) := Real.rpow_add hx _ _
    _ = x * Real.sqrt x := by rw [hsqrt, Real.rpow_one, mul_comm]

/-- The square root of a nonnegative cube is the number to the power `3/2`. -/
theorem sqrt_cube_eq_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ 3) = x ^ ((3:ℝ)/2) := by
  have h : x ^ 3 = x ^ 2 * x := by ring
  rw [h, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx, rpow_three_halves x hx]

/-- Squared form of the optimal-allocation inequality: for nonnegative masses `r` and
strictly positive denominators `t`, `(r²)³ ≤ (r³/t)² · t²`. -/
theorem power_amplitude_sq_le [Nonempty V] (r : V → ℝ) (hr : ∀ i, 0 ≤ r i)
    (t : V → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, r i ^ 2) ^ 3 ≤ (∑ i, r i ^ 3 / t i) ^ 2 * ∑ i, t i ^ 2 := by
  set S : ℝ := ∑ i, r i ^ 2
  set U : ℝ := ∑ i, r i ^ 3 / t i
  set W : ℝ := ∑ i, t i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW : 0 < W := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty V)
    refine lt_of_lt_of_le (sq_pos_of_pos (ht i0))
      (Finset.single_le_sum (fun i _ => sq_nonneg (t i)) (Finset.mem_univ i0))
  set scale : ℝ := Real.sqrt S / Real.sqrt W
  have hpt : ∀ i, 2 * scale * r i ^ 2 ≤ r i ^ 3 / t i + scale ^ 2 * (r i * t i) := by
    intro i
    have hti : 0 < t i := ht i
    have hkey : r i ^ 3 / t i + scale ^ 2 * (r i * t i) - 2 * scale * r i ^ 2
        = r i * (r i - scale * t i) ^ 2 / t i := by
      field_simp [hti.ne']
      ring
    have hsq : 0 ≤ r i * (r i - scale * t i) ^ 2 / t i :=
      div_nonneg (mul_nonneg (hr i) (sq_nonneg _)) (le_of_lt hti)
    apply sub_nonneg.mp
    rw [hkey]
    exact hsq
  have hsum : 2 * scale * S ≤ U + scale ^ 2 * (∑ i, r i * t i) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpt i)
  have hCS : (∑ i, r i * t i) ^ 2 ≤ S * W :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r t
  have hP : 0 ≤ ∑ i, r i * t i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hr i) (le_of_lt (ht i))
  have hPt : (∑ i, r i * t i) ≤ Real.sqrt (S * W) := by
    simpa only [Real.sqrt_sq hP] using Real.sqrt_le_sqrt hCS
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hSS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hWW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hSW : Real.sqrt (S * W) = Real.sqrt S * Real.sqrt W := Real.sqrt_mul hS W
  have hscale : scale * Real.sqrt (S * W) = S := by
    rw [hSW]
    calc
      scale * (Real.sqrt S * Real.sqrt W) =
          Real.sqrt S * ((Real.sqrt S / Real.sqrt W) * Real.sqrt W) := by
        dsimp [scale]
        ring
      _ = S := by rw [div_mul_cancel₀ _ hsW.ne', ← pow_two, hSS]
  have hrew : 2 * scale * S - scale ^ 2 * Real.sqrt (S * W)
      = S * Real.sqrt S / Real.sqrt W := by
    rw [pow_two, mul_assoc scale scale, hscale]
    dsimp [scale]
    ring
  have hmain : S * Real.sqrt S / Real.sqrt W ≤ U := by
    rw [← hrew]
    exact sub_le_iff_le_add.mpr
      (hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hPt (sq_nonneg scale))))
  have hle : S * Real.sqrt S ≤ U * Real.sqrt W :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hW)).mp hmain
  have hsq2 : (S * Real.sqrt S) ^ 2 ≤ (U * Real.sqrt W) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hS (Real.sqrt_nonneg _)) hle 2
  rw [pow_succ S 2]
  simpa only [mul_pow, hSS, hWW] using hsq2

/-- The coefficient form of the squared optimal-allocation inequality. -/
theorem magnitude_allocation_sq [Nonempty V] (c : V → ℝ) (n : V → ℝ)
    (hn : ∀ i, 0 < n i) :
    coeffPowerSum c ^ 3 ≤ (∑ i, |c i| / Real.sqrt (n i)) ^ 2 * ∑ i, n i := by
  have hsq : ∀ i, Real.sqrt (n i) ^ 2 = n i := fun i => Real.sq_sqrt (le_of_lt (hn i))
  have := power_amplitude_sq_le (r := fun i => magnitudeRoot (c i))
    (fun i => by
      unfold magnitudeRoot
      exact Real.rpow_nonneg (abs_nonneg _) _)
    (t := fun i => Real.sqrt (n i)) (fun i => Real.sqrt_pos.mpr (hn i))
  simp_rw [magnitudeRoot_square, magnitudeRoot_cube, hsq] at this
  unfold coeffPowerSum
  exact this

/-- At every strictly positive allocation of fixed total `T`, the amplitude sum is at
least `(C)^(3/2) / √T`, where `C` is the total coefficient mass. -/
theorem magnitude_allocation_lower_bound [Nonempty V] (c : V → ℝ) (n : V → ℝ)
    (hn : ∀ i, 0 < n i) (T : ℝ) (hT : 0 < T) (hsum : ∑ i, n i = T) :
    coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T ≤ ∑ i, |c i| / Real.sqrt (n i) := by
  have hmin := magnitude_allocation_sq c n hn
  rw [hsum] at hmin
  have hC : 0 ≤ coeffPowerSum c := coeffPowerSum_nonneg c
  have hU : 0 ≤ ∑ i, |c i| / Real.sqrt (n i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hdiv : coeffPowerSum c ^ 3 / T ≤ (∑ i, |c i| / Real.sqrt (n i)) ^ 2 :=
    (div_le_iff₀ hT).mpr hmin
  have hsqrt : Real.sqrt (coeffPowerSum c ^ 3 / T)
      ≤ ∑ i, |c i| / Real.sqrt (n i) := by
    simpa only [Real.sqrt_sq hU] using Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_div (pow_nonneg hC 3) T, sqrt_cube_eq_rpow_three_halves _ hC] at hsqrt
  exact hsqrt

/-- Each coefficient over the square root of its proportional allocation equals
`|c i|^(2/3)` times the square root of `C / T`. -/
theorem magnitude_div_sqrt_power_alloc [Nonempty V] (c : V → ℝ)
    (hc : ∀ i, c i ≠ 0) (T : ℝ) (hT : 0 < T) (i : V) :
    |c i| / Real.sqrt (powerAllocation c T i)
      = |c i| ^ ((2:ℝ)/3) * Real.sqrt (coeffPowerSum c / T) := by
  have hC : 0 < coeffPowerSum c := coeffPowerSum_pos c hc
  set r : ℝ := magnitudeRoot (c i)
  have hr : 0 < r := by
    change 0 < |c i| ^ (1 / (3 : ℝ))
    exact Real.rpow_pos_of_pos (abs_pos.mpr (hc i)) _
  have hr2 : r ^ 2 = |c i| ^ ((2:ℝ)/3) := magnitudeRoot_square (c i)
  have hr3 : r ^ 3 = |c i| := magnitudeRoot_cube (c i)
  have halloc : powerAllocation c T i = T / coeffPowerSum c * r ^ 2 := by
    unfold powerAllocation
    rw [hr2]
    ring
  have hTc : 0 < T / coeffPowerSum c := div_pos hT hC
  have hsqrt : Real.sqrt (T / coeffPowerSum c * r ^ 2)
      = Real.sqrt (T / coeffPowerSum c) * r := by
    rw [Real.sqrt_mul (le_of_lt hTc), Real.sqrt_sq (le_of_lt hr)]
  have hprod : Real.sqrt (T / coeffPowerSum c) * Real.sqrt (coeffPowerSum c / T) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hTc)]
    have h : T / coeffPowerSum c * (coeffPowerSum c / T) = 1 := by
      field_simp [hT.ne', hC.ne']
    rw [h, Real.sqrt_one]
  rw [halloc, hsqrt]
  have hs0 : Real.sqrt (T / coeffPowerSum c) ≠ 0 := (Real.sqrt_pos.mpr hTc).ne'
  have hcx : |c i| ^ ((2:ℝ)/3) = r ^ 2 := hr2.symm
  calc |c i| / (Real.sqrt (T / coeffPowerSum c) * r)
      = r ^ 3 / (Real.sqrt (T / coeffPowerSum c) * r) := by rw [hr3]
    _ = r ^ 2 / Real.sqrt (T / coeffPowerSum c) := by
        rw [pow_succ, mul_div_mul_right _ _ (ne_of_gt hr)]
    _ = r ^ 2 * Real.sqrt (coeffPowerSum c / T) := by
        apply (div_eq_iff hs0).2
        rw [mul_assoc, mul_comm (Real.sqrt (coeffPowerSum c / T)), hprod, mul_one]
    _ = |c i| ^ ((2:ℝ)/3) * Real.sqrt (coeffPowerSum c / T) := by rw [hcx]

/-- The proportional allocation of total `T` is positive, has total `T`, and attains
the amplitude bound `(C)^(3/2) / √T`. -/
theorem magnitude_allocation_attains [Nonempty V] (c : V → ℝ) (hc : ∀ i, c i ≠ 0)
    (T : ℝ) (hT : 0 < T) :
    0 < coeffPowerSum c ∧ (∀ i, 0 < powerAllocation c T i) ∧
      (∑ i, powerAllocation c T i) = T ∧
      (∑ i, |c i| / Real.sqrt (powerAllocation c T i))
        = coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T := by
  have hC : 0 < coeffPowerSum c := coeffPowerSum_pos c hc
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro i
    exact div_pos (mul_pos hT (Real.rpow_pos_of_pos (abs_pos.mpr (hc i)) _)) hC
  · unfold powerAllocation coeffPowerSum
    rw [← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ _ hC.ne'
  · have hterm : ∀ i, |c i| / Real.sqrt (powerAllocation c T i)
        = |c i| ^ ((2:ℝ)/3) * Real.sqrt (coeffPowerSum c / T) :=
      magnitude_div_sqrt_power_alloc c hc T hT
    calc (∑ i, |c i| / Real.sqrt (powerAllocation c T i))
        = ∑ i, |c i| ^ ((2:ℝ)/3) * Real.sqrt (coeffPowerSum c / T) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = coeffPowerSum c * Real.sqrt (coeffPowerSum c / T) := by
          exact (Finset.sum_mul ..).symm
      _ = coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T := by
          rw [rpow_three_halves _ (le_of_lt hC), Real.sqrt_div (le_of_lt hC) T]
          ring

/-- The minimum amplitude sum over strictly positive allocations of total `T` equals
`(C)^(3/2) / √T`, attained by the proportional allocation. -/
theorem magnitude_allocation_min [Nonempty V] (c : V → ℝ) (hc : ∀ i, c i ≠ 0)
    (T : ℝ) (hT : 0 < T) :
    ((∀ n : V → ℝ, (∀ i, 0 < n i) → ∑ i, n i = T →
        coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T ≤ ∑ i, |c i| / Real.sqrt (n i)) ∧
      (∀ i, 0 < powerAllocation c T i) ∧ (∑ i, powerAllocation c T i) = T ∧
        (∑ i, |c i| / Real.sqrt (powerAllocation c T i))
          = coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T) := by
  obtain ⟨_, hpos, hsum, heq⟩ := magnitude_allocation_attains c hc T hT
  exact ⟨fun n hn hsum' => magnitude_allocation_lower_bound c n hn T hT hsum',
    hpos, hsum, heq⟩

end Qatlib.Papers.ShadowTomog26.EnergyEstimate
