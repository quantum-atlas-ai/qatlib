/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularRadial

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Global bounds for the regularized CK radial factors

Successive integration of the exact radial derivative equations
gives the cubic and quintic bounds, with the same constants as the
limits at the origin. These bounds do not depend on a lower cutoff
on either the radius or the frequency.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open scoped Topology

/-- A power bound on a continuous derivative gives the next power
bound on its primitive with zero initial value. -/
private theorem abs_primitive_le_power {F f : ℝ → ℝ} {A u : ℝ} (n : ℕ)
    (h₀ : F 0 = 0) (hf : Continuous f) (hD : ∀ x, HasDerivAt F (f x) x)
    (hb : ∀ x ≥ 0, |f x| ≤ A * x ^ n) (hu : 0 ≤ u) :
    |F u| ≤ A * u ^ (n + 1) / ((n : ℝ) + 1) := by
  have hInt : IntervalIntegrable f volume 0 u := hf.intervalIntegrable _ _
  have hAbs : IntervalIntegrable (fun x => |f x|) volume 0 u := hf.abs.intervalIntegrable _ _
  have hPow : IntervalIntegrable (fun x : ℝ => A * x ^ n) volume 0 u :=
    (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _
  have he : (∫ x in 0..u, f x) = F u := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) hInt, h₀, sub_zero]
  rw [← he]
  calc
    _ ≤ ∫ x in 0..u, |f x| := intervalIntegral.abs_integral_le_integral_abs hu
    _ ≤ ∫ x in 0..u, A * x ^ n :=
      intervalIntegral.integral_mono_on hu hAbs hPow (fun x hx => hb x hx.1)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
        sub_zero, mul_div_assoc]

/-- The first CK radial numerator is odd. -/
private theorem ckKernel_neg (u : ℝ) : ckKernel (-u) = -ckKernel u := by
  simp only [ckKernel, Real.sin_neg, Real.cos_neg]
  ring

/-- The first CK radial numerator grows at most cubically with
constant one third, including both signs of the radial argument. -/
theorem abs_ckKernel_le_cube (u : ℝ) : |ckKernel u| ≤ |u| ^ 3 / 3 := by
  have hPos (v : ℝ) (hv : 0 ≤ v) : |ckKernel v| ≤ v ^ 3 / 3 := by
    have h := abs_primitive_le_power (F := ckKernel) (f := fun x => x * Real.sin x)
      (A := 1) (u := v) 2 (by simp [ckKernel]) (continuous_id.mul Real.continuous_sin)
      hasDerivAt_ckKernel (fun x hx => by
        rw [abs_mul, abs_of_nonneg hx, one_mul, pow_two]
        exact mul_le_mul_of_nonneg_left ((Real.abs_sin_le_abs (x := x)).trans_eq (abs_of_nonneg hx)) hx)
      hv
    norm_num at h ⊢
    exact h
  by_cases hu : 0 ≤ u
  · simpa only [abs_of_nonneg hu] using hPos u hu
  · have hneg : 0 ≤ -u := neg_nonneg.mpr (le_of_not_ge hu)
    simpa only [ckKernel_neg, abs_neg, abs_of_neg (lt_of_not_ge hu)] using hPos (-u) hneg

/-- The second CK radial numerator grows at most quintically with
constant one fifteenth. -/
theorem abs_ckCurlNumerator_le_fifth (u : ℝ) :
    |u ^ 2 * Real.sin u - 3 * ckKernel u| ≤ |u| ^ 5 / 15 := by
  let G := fun v : ℝ => v ^ 2 * Real.sin v - 3 * ckKernel v
  have hGneg (v : ℝ) : G (-v) = -G v := by
    simp only [G, Real.sin_neg, ckKernel_neg]
    ring
  have hPos (v : ℝ) (hv : 0 ≤ v) : |G v| ≤ v ^ 5 / 15 := by
    have hc : Continuous ckKernel :=
      continuous_iff_continuousAt.2 fun x => (hasDerivAt_ckKernel x).continuousAt
    have h := abs_primitive_le_power (F := G) (f := fun x => -x * ckKernel x)
      (A := 1 / 3) (u := v) 4 (by simp [G, ckKernel]) (continuous_id.neg.mul hc)
      hasDerivAt_ckCurlNumerator (fun x hx => by
        rw [abs_mul, abs_neg, abs_of_nonneg hx]
        calc
          _ ≤ x * (x ^ 3 / 3) :=
            mul_le_mul_of_nonneg_left (by simpa only [abs_of_nonneg hx] using abs_ckKernel_le_cube x) hx
          _ = _ := by ring) hv
    convert h using 1
    ring
  by_cases hu : 0 ≤ u
  · simpa only [G, abs_of_nonneg hu] using hPos u hu
  · have hneg : 0 ≤ -u := neg_nonneg.mpr (le_of_not_ge hu)
    have h := hPos (-u) hneg
    rw [hGneg, abs_neg] at h
    simpa only [G, abs_of_neg (lt_of_not_ge hu)] using h

/-- The regular cubic radial factor has a uniform absolute bound at
all arguments, including the continuous value at zero. -/
theorem abs_ckRadialThree_le (u : ℝ) : |ckRadialThree u| ≤ 1 / 3 := by
  by_cases hu : u = 0
  · norm_num [ckRadialThree, hu]
  · rw [ckRadialThree, ite_eq_right hu, abs_div, abs_pow, div_le_iff₀ (pow_pos (abs_pos.mpr hu) _)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using abs_ckKernel_le_cube u

/-- The regular quintic radial factor has a uniform absolute bound. -/
theorem abs_ckRadialFive_le (u : ℝ) : |ckRadialFive u| ≤ 1 / 15 := by
  by_cases hu : u = 0
  · norm_num [ckRadialFive, hu]
  · rw [ckRadialFive, ite_eq_right hu, abs_div, abs_pow, div_le_iff₀ (pow_pos (abs_pos.mpr hu) _)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using abs_ckCurlNumerator_le_fifth u

/-- The coefficient in the derivative of the regular quintic
factor is bounded by the seventh power of the radial argument. -/
private theorem abs_ckSeventh_le (u : ℝ) :
    |-(u ^ 2) * ckKernel u - 5 * (u ^ 2 * Real.sin u - 3 * ckKernel u)| ≤ |u| ^ 7 / 105 := by
  let H := fun x : ℝ => x ^ 2 * Real.sin x - 3 * ckKernel x
  let J := fun x : ℝ => -(x ^ 2) * ckKernel x - 5 * H x
  have hDeriv (x : ℝ) : HasDerivAt J (-x * H x) x := by
    dsimp only [J, H]
    refine HasDerivAt.congr_deriv (((hasDerivAt_pow 2 x).neg.mul
      (hasDerivAt_ckKernel x)).sub ((hasDerivAt_ckCurlNumerator x).const_mul 5)) ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, Pi.neg_apply, pow_one]
    ring
  have hPos (v : ℝ) (hv : 0 ≤ v) : |J v| ≤ v ^ 7 / 105 := by
    have hc : Continuous H := continuous_iff_continuousAt.2
      fun x => (hasDerivAt_ckCurlNumerator x).continuousAt
    have h := abs_primitive_le_power (F := J) (f := fun x => -x * H x)
      (A := 1 / 15) (u := v) 6 (by simp [J, H, ckKernel]) (continuous_id.neg.mul hc)
      hDeriv (fun x hx => by
        rw [abs_mul, abs_neg, abs_of_nonneg hx]
        calc
          _ ≤ x * (x ^ 5 / 15) := mul_le_mul_of_nonneg_left
            (by simpa only [H, abs_of_nonneg hx] using abs_ckCurlNumerator_le_fifth x) hx
          _ = _ := by ring) hv
    convert h using 1
    ring
  have hJneg (v : ℝ) : J (-v) = -J v := by
    simp only [J, H, ckKernel_neg, Real.sin_neg]
    ring
  by_cases hu : 0 ≤ u
  · simpa only [J, H, abs_of_nonneg hu] using hPos u hu
  · have hneg : 0 ≤ -u := neg_nonneg.mpr (le_of_not_ge hu)
    have h := hPos (-u) hneg
    rw [hJneg, abs_neg] at h
    simpa only [J, H, abs_of_neg (lt_of_not_ge hu)] using h

/-- A continuous function with derivative bounded by a multiple of
the distance to zero has derivative zero at the puncture. -/
private theorem hasDerivAt_zero_of_linear_bound {F D : ℝ → ℝ} {c : ℝ}
    (hF : Continuous F) (hD : ∀ u ≠ 0, HasDerivAt F (D u) u)
    (hB : ∀ u ≠ 0, |D u| ≤ |u| * c) : HasDerivAt F 0 0 := by
  have hne : ∀ᶠ u : ℝ in 𝓝[≠] 0, u ≠ 0 := self_mem_nhdsWithin
  have hId : Tendsto (fun u : ℝ => u) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    continuous_id.continuousAt.tendsto
  have hDom : Tendsto (fun u : ℝ => |u| * c) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using (hId.abs.mul_const c)
  have hLim : Tendsto D (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    exact squeeze_zero' (Eventually.of_forall fun u => abs_nonneg (D u))
      (hne.mono fun u hu => hB u hu) hDom
  have hZero : Tendsto (fun u => F u - F 0) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [sub_self] using
      ((tendsto_nhdsWithin_of_tendsto_nhds (hF.continuousAt (x := 0)).tendsto).sub
        (tendsto_const_nhds (x := F 0)))
  have hSlope := HasDerivAt.lhopital_zero_nhdsNE
    (hne.mono fun u hu => (hD u hu).sub_const (F 0))
    (Eventually.of_forall hasDerivAt_id) (Eventually.of_forall fun _ => one_ne_zero)
    hZero hId (by simpa only [id_eq, div_one] using hLim)
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, id_eq, mul_comm] using hSlope

/-- The derivative coefficient of the radial cubic factor grows at most linearly. -/
private theorem abs_ckRadialThree_slope_le (u : ℝ) :
    |(u ^ 2 * Real.sin u - 3 * ckKernel u) / u ^ 4| ≤ |u| * (1 / 15) := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [abs_div, abs_pow, div_le_iff₀ (pow_pos (abs_pos.mpr hu) _)]
    convert abs_ckCurlNumerator_le_fifth u using 1
    ring

/-- The derivative coefficient of the radial quintic factor grows at most linearly. -/
private theorem abs_ckRadialFive_slope_le (u : ℝ) :
    |(-(u ^ 2) * ckKernel u - 5 * (u ^ 2 * Real.sin u - 3 * ckKernel u)) / u ^ 6| ≤
      |u| * (1 / 105) := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [abs_div, abs_pow, div_le_iff₀ (pow_pos (abs_pos.mpr hu) _)]
    convert abs_ckSeventh_le u using 1
    ring

/-- The derivative of the regular cubic coefficient is the curl
numerator divided by the fourth power, with value zero at the origin. -/
theorem hasDerivAt_ckRadialThree (u : ℝ) :
    HasDerivAt ckRadialThree ((u ^ 2 * Real.sin u - 3 * ckKernel u) / u ^ 4) u := by
  let D := fun v : ℝ => (v ^ 2 * Real.sin v - 3 * ckKernel v) / v ^ 4
  have hDeriv (v : ℝ) (hv : v ≠ 0) : HasDerivAt ckRadialThree (D v) v := by
    refine (HasDerivAt.congr_deriv
      ((hasDerivAt_ckKernel v).div (hasDerivAt_pow 3 v) (pow_ne_zero 3 hv)) ?_).congr_of_eventuallyEq ?_
    · dsimp only [D]
      push_cast
      field_simp [hv]
    · filter_upwards [isOpen_compl_singleton.mem_nhds hv] with w hw
      exact ite_eq_right hw
  change HasDerivAt ckRadialThree (D u) u
  by_cases hu : u = 0
  · subst u
    simpa only [D, zero_pow (by decide : 4 ≠ 0), div_zero] using
      hasDerivAt_zero_of_linear_bound continuous_ckRadialThree hDeriv
        (fun v _ => abs_ckRadialThree_slope_le v)
  · exact hDeriv u hu

/-- The derivative of the regular quintic coefficient has a
seventh-order numerator and value zero at the origin. -/
theorem hasDerivAt_ckRadialFive (u : ℝ) :
    HasDerivAt ckRadialFive
      ((-(u ^ 2) * ckKernel u - 5 * (u ^ 2 * Real.sin u - 3 * ckKernel u)) / u ^ 6) u := by
  let D := fun v : ℝ => (-(v ^ 2) * ckKernel v - 5 * (v ^ 2 * Real.sin v - 3 * ckKernel v)) / v ^ 6
  have hDeriv (v : ℝ) (hv : v ≠ 0) : HasDerivAt ckRadialFive (D v) v := by
    refine (HasDerivAt.congr_deriv
      ((hasDerivAt_ckCurlNumerator v).div (hasDerivAt_pow 5 v) (pow_ne_zero 5 hv)) ?_).congr_of_eventuallyEq ?_
    · dsimp only [D]
      push_cast
      field_simp [hv]
    · filter_upwards [isOpen_compl_singleton.mem_nhds hv] with w hw
      exact ite_eq_right hw
  change HasDerivAt ckRadialFive (D u) u
  by_cases hu : u = 0
  · subst u
    simpa only [D, zero_pow (by decide : 6 ≠ 0), div_zero] using
      hasDerivAt_zero_of_linear_bound continuous_ckRadialFive hDeriv
        (fun v _ => abs_ckRadialFive_slope_le v)
  · exact hDeriv u hu

/-- The derivative of the regular cubic factor has a global linear bound. -/
theorem abs_deriv_ckRadialThree_le (u : ℝ) : |deriv ckRadialThree u| ≤ |u| * (1 / 15) := by
  rw [(hasDerivAt_ckRadialThree u).deriv]
  exact abs_ckRadialThree_slope_le u

/-- The derivative of the regular quintic factor has a global linear bound. -/
theorem abs_deriv_ckRadialFive_le (u : ℝ) : |deriv ckRadialFive u| ≤ |u| * (1 / 105) := by
  rw [(hasDerivAt_ckRadialFive u).deriv]
  exact abs_ckRadialFive_slope_le u

end Qatlib.Papers.KnottedLight08.CurlEigenstate
