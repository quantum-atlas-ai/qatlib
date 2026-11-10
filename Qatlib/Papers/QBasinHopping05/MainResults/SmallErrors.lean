/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.QBasinHopping05.MainResults

theorem source_small_error_amplitude_bound
    (amp θ η ζ r Nβ N : ℝ) (k : ℕ)
    (hsin : 0 < Real.sin θ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hexpansion :
      amp ≥ r ^ k * Real.sin ((k : ℝ) * η + ζ) / Real.sin θ
        - (2 / Real.sin θ) * Real.sqrt (Nβ / N)
            * ∑ j ∈ Finset.range k, r ^ j * |Real.sin (θ - 2 * ζ - (j : ℝ) * η)|) :
    amp ≥ (1 / Real.sin θ)
      * (r ^ k * Real.sin ((k : ℝ) * η + ζ) - 2 * (k : ℝ) * Real.sqrt (Nβ / N)) := by
  have hterm : ∀ j ∈ Finset.range k,
      r ^ j * |Real.sin (θ - 2 * ζ - (j : ℝ) * η)| ≤ 1 := by
    intro j _
    have hp : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1
    have hs : |Real.sin (θ - 2 * ζ - (j : ℝ) * η)| ≤ 1 := Real.abs_sin_le_one _
    have hp0 : 0 ≤ r ^ j := pow_nonneg hr0 j
    have hs0 : 0 ≤ |Real.sin (θ - 2 * ζ - (j : ℝ) * η)| := abs_nonneg _
    nlinarith
  have hsum : (∑ j ∈ Finset.range k,
        r ^ j * |Real.sin (θ - 2 * ζ - (j : ℝ) * η)|) ≤ (k : ℝ) := by
    calc (∑ j ∈ Finset.range k, r ^ j * |Real.sin (θ - 2 * ζ - (j : ℝ) * η)|)
        ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (k : ℝ) := by simp
  have hS : 0 ≤ Real.sqrt (Nβ / N) := Real.sqrt_nonneg _
  have hc : 0 ≤ 2 / Real.sin θ := le_of_lt (div_pos (by norm_num) hsin)
  have hcoef : 0 ≤ (2 / Real.sin θ) * Real.sqrt (Nβ / N) := mul_nonneg hc hS
  have hmul : (2 / Real.sin θ) * Real.sqrt (Nβ / N)
        * (∑ j ∈ Finset.range k,
            r ^ j * |Real.sin (θ - 2 * ζ - (j : ℝ) * η)|)
      ≤ (2 / Real.sin θ) * Real.sqrt (Nβ / N) * (k : ℝ) :=
    mul_le_mul_of_nonneg_left hsum hcoef
  have hsne : Real.sin θ ≠ 0 := ne_of_gt hsin
  have hkey : (1 / Real.sin θ)
      * (r ^ k * Real.sin ((k : ℝ) * η + ζ) - 2 * (k : ℝ) * Real.sqrt (Nβ / N))
      = r ^ k * Real.sin ((k : ℝ) * η + ζ) / Real.sin θ
        - (2 / Real.sin θ) * Real.sqrt (Nβ / N) * (k : ℝ) := by
    field_simp
  rw [hkey]
  linarith

theorem success_probability_of_amplitude
    (amp e : ℝ) (he : e ≤ 1) (hamp : 1 - e ≤ amp) :
    1 - 2 * e ≤ amp ^ 2 := by
  have h1e : 0 ≤ 1 - e := by linarith
  have hsq : (1 - e) ^ 2 ≤ amp ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self h1e hamp
  nlinarith [sq_nonneg e]

theorem success_probability_from_amplitude_bound
    (amp bound e : ℝ) (hbound0 : 0 ≤ bound) (he : e ≤ 1)
    (hle : bound ≤ amp) (hbound : 1 - e ≤ bound) : 1 - 2 * e ≤ amp ^ 2 := by
  have h1e : 0 ≤ 1 - e := by linarith
  have hsq1 : (1 - e) ^ 2 ≤ bound ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self h1e hbound
  have hsq2 : bound ^ 2 ≤ amp ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hbound0 hle
  have h1 : 1 - 2 * e ≤ (1 - e) ^ 2 := by nlinarith [sq_nonneg e]
  linarith

theorem noiseless_amplitude_bound (η : ℝ) (k : ℕ) (N : ℝ) :
    (1 / Real.sin (Real.pi / 2))
      * (1 ^ k * Real.sin ((k : ℝ) * η + η / 2) - 2 * (k : ℝ) * Real.sqrt (0 / N))
      = Real.sin ((2 * (k : ℝ) + 1) * η / 2) := by
  have hsqrt : Real.sqrt (0 / N) = 0 := by simp
  have hang : (k : ℝ) * η + η / 2 = (2 * (k : ℝ) + 1) * η / 2 := by ring
  rw [hsqrt, hang, Real.sin_pi_div_two, one_pow]
  ring

noncomputable def optimalGroverIterations (N Nγ : ℝ) : ℝ :=
  (Real.pi / 4) * Real.sqrt (N / Nγ)

theorem optimal_error_rate (N Nγ Nβ : ℝ) (hN : 0 < N) (hNγ : 0 < Nγ) :
    1 - (1 - 2 * optimalGroverIterations N Nγ * Real.sqrt (Nβ / N))
      = (Real.pi / 2) * Real.sqrt (Nβ / Nγ) := by
  unfold optimalGroverIterations
  have hNne : N ≠ 0 := ne_of_gt hN
  have hNγne : Nγ ≠ 0 := ne_of_gt hNγ
  have hprod : Real.sqrt (N / Nγ) * Real.sqrt (Nβ / N) = Real.sqrt (Nβ / Nγ) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hN hNγ))]
    congr 1
    field_simp
  have h1 : 1 - (1 - 2 * ((Real.pi / 4) * Real.sqrt (N / Nγ)) * Real.sqrt (Nβ / N))
      = 2 * ((Real.pi / 4) * Real.sqrt (N / Nγ)) * Real.sqrt (Nβ / N) := by ring
  have h2 : 2 * ((Real.pi / 4) * Real.sqrt (N / Nγ)) * Real.sqrt (Nβ / N)
      = (Real.pi / 2) * (Real.sqrt (N / Nγ) * Real.sqrt (Nβ / N)) := by ring
  rw [h1, h2, hprod]

theorem success_probability_from_noise_rate
    (amp Nβ Nγ : ℝ) (hNγ : 0 < Nγ)
    (hle : 1 - (Real.pi / 2) * Real.sqrt (Nβ / Nγ) ≤ amp) :
    1 - Real.pi * Real.sqrt (Nβ / Nγ) ≤ amp ^ 2 := by
  set s := Real.sqrt (Nβ / Nγ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set e := (Real.pi / 2) * s with he
  have h2e : 2 * e = Real.pi * s := by rw [he]; ring
  by_cases h1 : e ≤ 1
  · have hamp : 1 - e ≤ amp := by rw [he]; linarith
    have h := success_probability_of_amplitude amp e h1 hamp
    linarith [h, h2e]
  · push_neg at h1
    have hneg : 1 - Real.pi * s < 0 := by nlinarith [h2e, h1]
    nlinarith [sq_nonneg amp, hneg]

theorem small_entangling_high_success (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (amp Nβ Nγ : ℝ), 0 < Nγ →
      Real.sqrt (Nβ / Nγ) ≤ δ →
      1 - (Real.pi / 2) * Real.sqrt (Nβ / Nγ) ≤ amp →
      1 - ε ≤ amp ^ 2 := by
  refine ⟨ε / Real.pi, ?_, ?_⟩
  · positivity
  · intro amp Nβ Nγ hNγ hsδ hamp
    have hπ : 0 < Real.pi := Real.pi_pos
    have hprob := success_probability_from_noise_rate amp Nβ Nγ hNγ hamp
    have hmul : Real.pi * Real.sqrt (Nβ / Nγ) ≤ ε := by
      have h := mul_le_mul_of_nonneg_left hsδ (le_of_lt hπ)
      have hδ : Real.pi * (ε / Real.pi) = ε := by field_simp
      linarith [h, hδ]
    linarith [hprob, hmul]

theorem noiseless_peak_iteration (η : ℝ) (hη : 0 < η) :
    Real.sin ((2 * (Real.pi / (2 * η) - 1 / 2) + 1) * η / 2) = 1 := by
  have hang : (2 * (Real.pi / (2 * η) - 1 / 2) + 1) * η / 2 = Real.pi / 2 := by
    field_simp
    ring
  rw [hang, Real.sin_pi_div_two]

end Qatlib.Papers.QBasinHopping05.MainResults
