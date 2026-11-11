/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Vertex probabilities and geometric averages

The functions `nodeProb` and `avgNodeProb` sum over coin coordinates to describe instantaneous
and time-averaged vertex weights. The geometric average `geomAvg` isolates the oscillatory
factor used to derive limiting distributions for the walks of [AharonovEtAl2001Walks].

## Main statements

* `norm_geomAvg_le`: bounds a nonconstant unit-modulus geometric average.
* `tendsto_geomAvg`: identifies its limit on the unit circle.

## References

* [Aharonov et al., 2001][AharonovEtAl2001Walks]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Core

open scoped BigOperators Matrix Topology
open Filter

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

/-- The vertex weight after `t` applications of `U`, obtained by summing squared coordinate
norms over the coin register. -/
def nodeProb (U : Matrix (Coin × V) (Coin × V) ℂ) (ψ : (Coin × V) → ℂ)
    (t : ℕ) (v : V) : ℝ :=
  ∑ a : Coin, Complex.normSq (((U ^ t) *ᵥ ψ) (a, v))

/-- The average of `nodeProb` over times `0, …, T - 1`, using the inverse of `T` as
normalization. -/
def avgNodeProb (U : Matrix (Coin × V) (Coin × V) ℂ) (ψ : (Coin × V) → ℂ)
    (T : ℕ) (v : V) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nodeProb U ψ t v

/-- The normalized finite geometric sum `T⁻¹ * ∑ t < T, z^t`. -/
def geomAvg (z : ℂ) (T : ℕ) : ℂ :=
  (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, z ^ t

/-- For a unit-modulus complex number different from one, the geometric average has norm at most
`2 / (T * ‖z - 1‖)`. -/
theorem norm_geomAvg_le (z : ℂ) (hz : ‖z‖ = 1) (h1 : z ≠ 1) (T : ℕ) :
    ‖geomAvg z T‖ ≤ 2 / ((T : ℝ) * ‖z - 1‖) := by
  rcases Nat.eq_zero_or_pos T with hT | hTpos
  · subst hT
    simp [geomAvg]
  · have hTpos' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
    have hgz : geomAvg z T = (T : ℂ)⁻¹ * ((z ^ T - 1) / (z - 1)) := by
      rw [geomAvg, geom_sum_eq h1]
    have hnormT : ‖(T : ℂ)‖ = (T : ℝ) := RCLike.norm_natCast T
    have hinvT : ‖(T : ℂ)⁻¹‖ = (T : ℝ)⁻¹ := by rw [norm_inv, hnormT]
    have hnum : ‖z ^ T - 1‖ ≤ 2 := by
      have hzT : ‖z ^ T‖ = 1 := by rw [norm_pow, hz, one_pow]
      calc ‖z ^ T - 1‖ ≤ ‖z ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hzT]; norm_num
    have hden : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    calc ‖geomAvg z T‖ = ‖(T : ℂ)⁻¹‖ * (‖z ^ T - 1‖ / ‖z - 1‖) := by
          rw [hgz, norm_mul, norm_div]
      _ = (T : ℝ)⁻¹ * (‖z ^ T - 1‖ / ‖z - 1‖) := by rw [hinvT]
      _ ≤ (T : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hnum hden.le
      _ = 2 / ((T : ℝ) * ‖z - 1‖) := by
          field_simp

/-- For unit-modulus `z`, the geometric average tends to one when `z = 1` and to zero otherwise. -/
theorem tendsto_geomAvg (z : ℂ) (hz : ‖z‖ = 1) :
    Tendsto (fun T : ℕ => geomAvg z T) atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases h1 : z = 1
  · subst h1
    rw [if_pos rfl]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have hT0 : (T : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hT)
    simp only [geomAvg, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    field_simp
  · rw [if_neg h1]
    have hbound : ∀ T : ℕ, ‖geomAvg z T‖ ≤ 2 / ((T : ℝ) * ‖z - 1‖) :=
      norm_geomAvg_le z hz h1
    have hlim0 : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun T : ℕ => (2 / ‖z - 1‖) * ((T : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlim0
    have hlim' : Tendsto (fun T : ℕ => 2 / ((T : ℝ) * ‖z - 1‖)) atTop (𝓝 0) :=
      Tendsto.congr (fun T => by field_simp) hlim
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _) hbound hlim'

end Qatlib.Papers.QWalkGraphs00.MainResults.Core
