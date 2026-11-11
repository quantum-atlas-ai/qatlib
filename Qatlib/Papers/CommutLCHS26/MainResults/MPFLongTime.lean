/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFSegments
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Long-time accuracy of repeated multi-product formulas

This module defines the positive segment count `segments` and the repeated approximation
`evolve` for the simulation framework of [AftabAnTrivisa2026]. The root-based step choice keeps
the scaled slice within 1/2 and controls accumulated local error, including its multiplicative
growth.

For Hermitian generators and normalized weights satisfying the cancellation moments, the
full-time error is at most ε/4 when 0 < ε ≤ 1; the Chebyshev construction supplies a concrete
specialization.

## Main statements

* `slice_control`: bounds the scaled time per segment.
* `actual_error`: proves the full-time error budget.
* `chebyshev_error`: applies it to Chebyshev weights and nodes.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFLongTime

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open MPFRootProfile MPFRootBound MPFMomentSeries
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF
open Qatlib.Concepts.TrotterFormula.GeneralOrder
set_option warningAsError false

/-- If η ≥ 0, ε ≤ 1, and rη ≤ ε/(12π), the repeated-step growth factor (1 + η)^(r - 1) is at
most 3. -/
theorem growth_le_three (η ε : ℝ) (r : ℕ) (hη : 0 ≤ η) (hε : ε ≤ 1)
    (hb : (r : ℝ) * η ≤ ε / (12 * Real.pi)) : (1 + η) ^ (r - 1) ≤ 3 := by
  have hn : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have htotal : (r : ℝ) * η ≤ 1 := hb.trans (by
    apply (div_le_iff₀ (by positivity : 0 < 12 * Real.pi)).mpr
    nlinarith [Real.pi_gt_three])
  calc
    _ ≤ (Real.exp η) ^ (r - 1) := pow_le_pow_left₀ (by linarith)
      (by simpa only [add_comm] using! Real.add_one_le_exp η) _
    _ = Real.exp (((r - 1 : ℕ) : ℝ) * η) := (Real.exp_nat_mul η (r - 1)).symm
    _ ≤ Real.exp ((r : ℝ) * η) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn hη)
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr htotal
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- If η ≥ 0, 0 < ε ≤ 1, and rη ≤ ε/(12π), the accumulated error rη(1 + η)^(r - 1) is at most
ε/4. -/
theorem global_budget (η ε : ℝ) (r : ℕ) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : (r : ℝ) * η ≤ ε / (12 * Real.pi)) :
    (r : ℝ) * η * (1 + η) ^ (r - 1) ≤ ε / 4 := by
  have hsmall : ε / (12 * Real.pi) ≤ ε / 12 :=
    div_le_div_of_nonneg_left hε.le (by norm_num) (by nlinarith [Real.pi_gt_three])
  calc
    _ ≤ ((r : ℝ) * η) * 3 := mul_le_mul_of_nonneg_left
      (growth_le_three η ε r hη hε1 hb) (mul_nonneg (Nat.cast_nonneg r) hη)
    _ ≤ (ε / 12) * 3 := mul_le_mul_of_nonneg_right (hb.trans hsmall) (by norm_num)
    _ = _ := by ring

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]

/-- The root-based segment count formed from μ times absolute time, the absolute coefficient
mass, the tolerance, and the order. -/
def segments (xs : List (Matrix I I ℂ)) (a : K → ℝ) (m : ℕ) (T ε : ℝ) : ℕ :=
  MPFSegments.count (mu xs m * |T|) (∑ j, |a j|) ε m

/-- The actual multi-product formula at time T divided by the segment count, raised to that
count. -/
def evolve (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (m : ℕ) (T ε : ℝ) : Matrix I I ℂ :=
  actualMPF xs q a (T / segments xs a m T ε) ^ segments xs a m T ε

omit [DecidableEq I] in

/-- The chosen segment count is strictly positive. -/
theorem segments_pos (xs : List (Matrix I I ℂ)) (a : K → ℝ) (m : ℕ) (T ε : ℝ) :
    0 < segments xs a m T ε := MPFSegments.count_pos _ _ _ _

/-- For positive order and tolerance, μ times the absolute slice time is at most 1/2. -/
theorem slice_control (xs : List (Matrix I I ℂ)) (a : K → ℝ) (m : ℕ) (hm : 0 < m)
    (T ε : ℝ) (hε : 0 < ε) :
    mu xs m * |T / (segments xs a m T ε : ℝ)| ≤ 1 / 2 := by
  have hr : 0 < (segments xs a m T ε : ℝ) := by exact_mod_cast segments_pos xs a m T ε
  rw [abs_div, abs_of_pos hr, ← mul_div_assoc]
  exact MPFSegments.step_control _ _ ε m (mul_nonneg (mu_nonneg xs m hm) (abs_nonneg T))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) hε

/-- For Hermitian generators and normalized cancellation weights, the chosen repeated
multi-product approximation has full-time error at most ε/4 for 0 < ε ≤ 1. -/
theorem actual_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖evolve xs q a m T ε - NormedSpace.exp (T • ((-Complex.I) • xs.sum))‖ ≤ ε / 4 := by
  let r := segments xs a m T ε
  let A : ℝ := ∑ j, |a j|
  let z := mu xs m * |T|
  let η := (8 / 3 : ℝ) * A * (z / (r : ℝ)) ^ (2 * m + 1)
  have hr : 0 < r := segments_pos xs a m T ε
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hz : 0 ≤ z := mul_nonneg (mu_nonneg xs m hm) (abs_nonneg T)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have he : ‖actualMPF xs q a (T / r) - NormedSpace.exp ((T / r) • ((-Complex.I) • xs.sum))‖ ≤ η := by
    have h := actualMPF_root_error xs hxs q hq a ha m hm hmom (T / r)
      (slice_control xs a m hm T ε hε)
    simpa only [abs_div, abs_of_pos hrR, ← mul_div_assoc] using! h
  have hZ : ((-Complex.I) • xs.sum)ᴴ = -((-Complex.I) • xs.sum) := by
    simpa only [one_smul] using! BCHPerturbation.target_skew xs hxs 1
  have h := power_error _ _ (general_trotter_exp_unitary _ (T / r) hZ) η he r
  rw [target_power _ T r hr] at h
  exact h.trans (global_budget η ε r hη hε hε1
    (MPFSegments.accumulated_local z A ε m hm hz hA hε))

omit [Fintype K] in

/-- For Hermitian generators and positive order, the repeated Chebyshev multi-product
approximation has error at most ε/4 for 0 < ε ≤ 1. -/
theorem chebyshev_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖evolve xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε -
      NormedSpace.exp (T • ((-Complex.I) • xs.sum))‖ ≤ ε / 4 := by
  apply actual_error xs hxs _ (ChebyshevNodes.node_pos m hm) _ _ m hm _ T ε hε hε1
  · simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

end Qatlib.Papers.CommutLCHS26.MainResults.MPFLongTime
