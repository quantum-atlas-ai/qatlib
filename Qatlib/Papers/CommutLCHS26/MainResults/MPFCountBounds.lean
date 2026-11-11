/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFLongTime

/-!
# Segment and query bounds for Chebyshev formulas

This module combines harmonic weight estimates with the root-based segment choice to bound the
cost of Chebyshev multi-product simulation in [AftabAnTrivisa2026]. For scaled time at least one
and tolerance in (0, 1], the segment count and `queryFactor` satisfy explicit bounds involving
the 2m-th root of scaled time divided by tolerance.

## Main statements

* `segments_bound`: bounds the number of simulation segments.
* `query_factor_bound`: includes the Chebyshev weight and node costs.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFCountBounds

open scoped BigOperators Classical Matrix.Norms.L2Operator
open MPFSegments MPFRootProfile MPFLongTime
set_option warningAsError false

/-- For positive m, the m-th harmonic number is at most m. -/
theorem harmonic_le_order (m : ℕ) (hm : 0 < m) : (harmonic m : ℝ) ≤ (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  linarith [harmonic_le_one_add_log m, Real.log_le_sub_one_of_pos hmR]

/-- For positive m, the 2m-th root of 1 plus 8π times the Chebyshev weight mass is at most 1 +
16π. -/
theorem mass_root_bound (m : ℕ) (hm : 0 < m) :
    (1 + 8 * Real.pi * (∑ j : Fin m, |ChebyshevNodes.weight m j|)) ^
      (((2 * m : ℕ) : ℝ)⁻¹) ≤ 1 + 16 * Real.pi := by
  have hmass := (ChebyshevCondition.weight_mass_harmonic m hm).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_order m hm) (by norm_num : (0 : ℝ) ≤ 2))
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity)
    (show (0 : ℝ) < ((2 * m : ℕ) : ℝ) by positivity)).mpr
  rw [Real.rpow_natCast]
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 16 * Real.pi by linarith [Real.pi_pos]) (2 * m)
  push_cast at hb
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [Real.pi_pos]

/-- For z ≥ 1, A ≥ 0, and 0 < ε ≤ 1, the root factor is bounded by the product of the stated
coefficient-mass root and (z/ε)^(1/(2m)). -/
theorem rootFactor_le (z A ε : ℝ) (m : ℕ) (hz : 1 ≤ z) (hA : 0 ≤ A)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    rootFactor z A ε m ≤ (1 + 8 * Real.pi * A) ^ (((2 * m : ℕ) : ℝ)⁻¹) *
      (z / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹) := by
  have hratio : 1 ≤ z / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hbase : 1 + 8 * Real.pi * z * A / ε ≤ (1 + 8 * Real.pi * A) * (z / ε) := by
    calc
      _ = 1 + (8 * Real.pi * A) * (z / ε) := by ring
      _ ≤ z / ε + (8 * Real.pi * A) * (z / ε) := _root_.add_le_add hratio le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1 + 8 * Real.pi * A) * (z / ε)) ^ (((2 * m : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- For positive m, scaled time at least 1, and 0 < ε ≤ 1, the Chebyshev segment count is at
most (3 + 32π) times scaled time times its tolerance-dependent 2m-th root. -/
theorem segments_bound (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (T ε : ℝ) (hz : 1 ≤ mu xs m * |T|) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (segments xs (ChebyshevNodes.weight m) m T ε : ℝ) ≤
      (3 + 32 * Real.pi) * (mu xs m * |T|) *
        ((mu xs m * |T|) / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹) := by
  let z := mu xs m * |T|
  let A := ∑ j : Fin m, |ChebyshevNodes.weight m j|
  let w := (z / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹)
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw : 1 ≤ w := Real.one_le_rpow ((le_div_iff₀ hε).mpr (by linarith)) (by positivity)
  have hR : rootFactor z A ε m ≤ (1 + 16 * Real.pi) * w :=
    (rootFactor_le z A ε m hz hA hε hε1).trans
      (mul_le_mul_of_nonneg_right (mass_root_bound m hm) (by positivity))
  have hc := MPFSegments.count_upper z A ε m hz0 hA hε
  calc
    _ ≤ 2 * z * rootFactor z A ε m + 1 := hc
    _ ≤ 2 * z * ((1 + 16 * Real.pi) * w) + 1 :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left hR (show 0 ≤ 2 * z by positivity)) le_rfl
    _ ≤ 2 * z * ((1 + 16 * Real.pi) * w) + z * w := by
      gcongr
      exact one_le_mul_of_one_le_of_one_le hz hw
    _ = _ := by ring

/-- The Chebyshev segment count multiplied by the total absolute weight and total repetition
count. -/
def queryFactor (xs : List (Matrix I I ℂ)) (m : ℕ) (T ε : ℝ) : ℝ :=
  (segments xs (ChebyshevNodes.weight m) m T ε : ℝ) *
    (∑ j : Fin m, |ChebyshevNodes.weight m j|) * (∑ j : Fin m, (ChebyshevNodes.node m j : ℝ))

omit [DecidableEq I] in

/-- Under the stated order, time, and tolerance hypotheses, the Chebyshev query factor has the
explicit m² log²(m + 1) bound times scaled time and its tolerance-dependent root. -/
theorem query_factor_bound (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (T ε : ℝ) (hz : 1 ≤ mu xs m * |T|) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    queryFactor xs m T ε ≤
      ((3 + 32 * Real.pi) * (2 + 2 / Real.log 2) * (16 + 17 / Real.log 2)) *
        (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) ^ 2 * (mu xs m * |T|) *
          ((mu xs m * |T|) / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹) := by
  have hmass : 0 ≤ ∑ j : Fin m, |ChebyshevNodes.weight m j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnodes : 0 ≤ ∑ j : Fin m, (ChebyshevNodes.node m j : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcount : 0 ≤ (3 + 32 * Real.pi) * (mu xs m * |T|) *
      ((mu xs m * |T|) / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹) := by positivity
  have h := mul_le_mul (segments_bound xs m hm T ε hz hε hε1)
    (ChebyshevCondition.query_factor_bound m hm) (mul_nonneg hmass hnodes) hcount
  exact (show queryFactor xs m T ε ≤ _ by simpa only [queryFactor, mul_assoc] using! h).trans_eq
      (by ring)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFCountBounds
