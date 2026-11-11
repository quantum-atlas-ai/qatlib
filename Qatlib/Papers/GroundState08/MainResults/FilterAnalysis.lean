/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundState08.MainResults.MomentumInnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Energy-filter overlap and success bounds

This module defines an energy band `inBand` and the squared-amplitude sum `filterOverlap` used
in the filter analysis of [PoulinWocjan2009]. Under explicit amplitude and support assumptions,
it proves overlap lower bounds, an inverse-square-root bound, and concentration of the expected
energy within the band.

## Main statements

* `inBand_amplitude_ge_half`: a lower bound for repeated momentum-filter amplitudes near the
  target phase.
* `energy_filter_main_result`: the combined overlap, iteration, energy, and empty-band bounds.

## References

* [Poulin and Wocjan, 2009][PoulinWocjan2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.GroundState08.MainResults.MomentumInnerProduct

namespace Qatlib.Papers.GroundState08.MainResults.FilterAnalysis

variable {N : ℕ}

/-- The indices whose energies differ from the target `μ` by at most `ε`. -/
def inBand (μ ε : ℝ) (φ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun a => |φ a - μ| ≤ ε)

/-- Membership in the energy band is equivalent to `|φ a - μ| ≤ ε`. -/
lemma mem_inBand {μ ε : ℝ} {φ : Fin N → ℝ} {a : Fin N} :
    a ∈ inBand μ ε φ ↔ |φ a - μ| ≤ ε := by
  simp [inBand]

/-- The sum of `α a ^ 2 * w a ^ 2` over indices in the target energy band. -/
def filterOverlap (μ ε : ℝ) (φ : Fin N → ℝ) (α w : Fin N → ℝ) : ℝ :=
  ∑ a ∈ inBand μ ε φ, α a ^ 2 * w a ^ 2

/-- For `N > 0`, squared initial amplitudes at least `1/N` and in-band filter amplitudes at
least `1/2` give overlap at least the band cardinality divided by `4N` [PoulinWocjan2009]. -/
theorem overlap_lower_bound (μ ε : ℝ) (φ : Fin N → ℝ) (α w : Fin N → ℝ)
    (hN : 0 < N)
    (hα : ∀ a, 1 / (N : ℝ) ≤ α a ^ 2)
    (hw : ∀ a ∈ inBand μ ε φ, (1 / 2 : ℝ) ≤ w a) :
    ((inBand μ ε φ).card : ℝ) / (4 * (N : ℝ)) ≤ filterOverlap μ ε φ α w := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ a ∈ inBand μ ε φ,
      (1 / (N : ℝ)) * (1 / 4 : ℝ) ≤ α a ^ 2 * w a ^ 2 := by
    intro a ha
    have hw2sq : (1 / 4 : ℝ) ≤ w a ^ 2 := by
      have h := hw a ha
      nlinarith [h]
    have ha2nn : (0 : ℝ) ≤ α a ^ 2 := by positivity
    exact mul_le_mul (hα a) hw2sq (by norm_num) ha2nn
  have hsum : (∑ a ∈ inBand μ ε φ, (1 / (N : ℝ)) * (1 / 4 : ℝ)) ≤
      filterOverlap μ ε φ α w :=
    Finset.sum_le_sum hterm
  have hconst : (∑ _a ∈ inBand μ ε φ, (1 / (N : ℝ)) * (1 / 4 : ℝ)) =
      ((inBand μ ε φ).card : ℝ) * ((1 / (N : ℝ)) * (1 / 4 : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst] at hsum
  calc ((inBand μ ε φ).card : ℝ) / (4 * (N : ℝ)) =
        ((inBand μ ε φ).card : ℝ) * ((1 / (N : ℝ)) * (1 / 4 : ℝ)) := by
        field_simp
    _ ≤ filterOverlap μ ε φ α w := hsum

/-- If `N > 0` and `q ≥ 1/N`, then `1 / √q ≤ √N` [PoulinWocjan2009]. -/
theorem grover_iterations_le_sqrt (q : ℝ) (hN : 0 < N) (hq : 1 / (N : ℝ) ≤ q) :
    1 / Real.sqrt q ≤ Real.sqrt (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hqN : (1 : ℝ) ≤ (N : ℝ) * q := by
    have h := mul_le_mul_of_nonneg_left hq (le_of_lt hNpos)
    rwa [one_div, mul_inv_cancel₀ hNpos.ne'] at h
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hqpos)]
  have hsq : (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
  rw [hsq, ← Real.sqrt_mul (le_of_lt hNpos)]
  apply Real.sqrt_le_sqrt
  linarith [hqN]

/-- A nonnegative probability distribution supported in the target energy band has expected
energy within `ε` of `μ` [PoulinWocjan2009]. -/
theorem success_energy_within_band (μ ε : ℝ) (φ : Fin N → ℝ) (p : Fin N → ℝ)
    (hpnn : ∀ a, 0 ≤ p a)
    (hpsum : (∑ a, p a) = 1)
    (hsupp : ∀ a, p a ≠ 0 → |φ a - μ| ≤ ε) :
    |(∑ a, p a * φ a) - μ| ≤ ε := by
  have hsplit2 : (∑ a, p a * μ) = μ := by
    rw [← Finset.sum_mul, hpsum, one_mul]
  have hsplit : (∑ a, p a * φ a) - μ = ∑ a, p a * (φ a - μ) := by
    have h1 : (∑ a, p a * φ a) - μ = (∑ a, p a * φ a) - ∑ a, p a * μ := by
      rw [hsplit2]
    rw [h1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsplit]
  calc
    |∑ a, p a * (φ a - μ)| ≤ ∑ a, |p a * (φ a - μ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, p a * |φ a - μ| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul, abs_of_nonneg (hpnn a)]
    _ ≤ ∑ a, p a * ε := by
        apply Finset.sum_le_sum
        intro a _
        by_cases hp : p a = 0
        · simp [hp]
        · exact mul_le_mul_of_nonneg_left (hsupp a hp) (hpnn a)
    _ = ε := by
        rw [← Finset.sum_mul, hpsum, one_mul]

/-- For `N > 0`, an empty energy band gives filter overlap strictly below `1/N^2`
[PoulinWocjan2009]. -/
theorem empty_band_aborts (μ ε : ℝ) (φ : Fin N → ℝ) (α w : Fin N → ℝ)
    (hN : 0 < N) (hempty : inBand μ ε φ = ∅) :
    filterOverlap μ ε φ α w < 1 / (N : ℝ) ^ 2 := by
  have hzero : filterOverlap μ ε φ α w = 0 := by
    simp [filterOverlap, hempty]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := by positivity
  rw [hzero]
  linarith

/-- If `2^k = ε⁻¹` with positive `ε`, then the reciprocal of `2^k` equals `ε`. -/
theorem filter_width_parameter (k : ℕ) (ε : ℝ) (_hε : 0 < ε) (hk : (2 : ℝ) ^ k = ε⁻¹) :
    ((2 : ℝ) ^ k)⁻¹ = ε := by
  rw [hk, inv_inv]

/-- Within the band of width `2⁻ᵏ / (2π√η)`, the momentum-overlap norm raised to a positive
integer power `η` is at least `1/2` [PoulinWocjan2009]. -/
theorem inBand_amplitude_ge_half (k η : ℕ) (hη : 0 < η) (φ : Fin N → ℝ) (μ : ℝ) :
    ∀ a ∈ inBand μ (((2 : ℕ) ^ k : ℝ)⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ))) φ,
      (1 / 2 : ℝ) ≤ ‖momentumInner k (φ a) μ‖ ^ η := by
  intro a ha
  exact momentumInner_pow_ge_half k η hη (φ a) μ (mem_inBand.mp ha)

/-- The stated amplitude, overlap, and support assumptions imply the band-cardinality overlap
bound, the `√N` inverse-square-root bound, the energy expectation bound, and the empty-band
implication [PoulinWocjan2009]. -/
theorem energy_filter_main_result (μ ε : ℝ) (φ : Fin N → ℝ) (α w p : Fin N → ℝ)
    (hN : 0 < N)
    (hα : ∀ a, 1 / (N : ℝ) ≤ α a ^ 2)
    (hw : ∀ a ∈ inBand μ ε φ, (1 / 2 : ℝ) ≤ w a)
    (hq : 1 / (N : ℝ) ≤ filterOverlap μ ε φ α w)
    (hpnn : ∀ a, 0 ≤ p a) (hpsum : (∑ a, p a) = 1)
    (hsupp : ∀ a, p a ≠ 0 → |φ a - μ| ≤ ε) :
    ((inBand μ ε φ).card : ℝ) / (4 * (N : ℝ)) ≤ filterOverlap μ ε φ α w ∧
    1 / Real.sqrt (filterOverlap μ ε φ α w) ≤ Real.sqrt (N : ℝ) ∧
    |(∑ a, p a * φ a) - μ| ≤ ε ∧
    (inBand μ ε φ = ∅ → filterOverlap μ ε φ α w < 1 / (N : ℝ) ^ 2) := by
  refine ⟨overlap_lower_bound μ ε φ α w hN hα hw,
    grover_iterations_le_sqrt _ hN hq,
    success_energy_within_band μ ε φ p hpnn hpsum hsupp, ?_⟩
  intro hempty
  exact empty_band_aborts μ ε φ α w hN hempty

end Qatlib.Papers.GroundState08.MainResults.FilterAnalysis
