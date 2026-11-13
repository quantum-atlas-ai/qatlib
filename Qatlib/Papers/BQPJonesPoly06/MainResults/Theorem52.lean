/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem32

/-!
# Parameter-dependent braid synthesis bounds

The inequality `theorem52_base_mono` replaces logarithmic precision dependence by
inverse-precision dependence while retaining the factor `k + 1`. The synthesis theorems apply
this estimate simultaneously to crossing counts and a supplied cost function in the development
of Theorem 5.2 of [AharonovArad2011].

## Main statements

* `theorem52_density_efficiency`: converts assumed logarithmic crossing and cost bounds into
  bounds polynomial in inverse precision and `k`.
* `theorem52_synthesis`: provides this conversion with the stated parameter and
  norm-preservation hypotheses.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- For `0 < δ ≤ 1`, replacing `log (1 / δ) + 1` by `δ⁻¹ + 1` increases the stated power bound
with parameter factor `k + 1` [AharonovArad2011]. -/
theorem theorem52_base_mono (C d k : ℕ) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (C : ℝ) * ((Real.log (1 / δ) + 1) * (k + 1)) ^ d ≤
        (C : ℝ) * ((δ⁻¹ + 1) * (k + 1)) ^ d := by
  intro δ hδ hδ1
  have hb0 : 0 ≤ Real.log (1 / δ) + 1 :=
    log_one_div_add_one_nonneg hδ hδ1
  have hb1 : Real.log (1 / δ) + 1 ≤ δ⁻¹ + 1 := by
    have hlog := log_one_div_le_inv hδ
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hmul : (Real.log (1 / δ) + 1) * ((k : ℝ) + 1) ≤
      (δ⁻¹ + 1) * ((k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hb1 hk0
  have hmul0 : 0 ≤ (Real.log (1 / δ) + 1) * ((k : ℝ) + 1) :=
    mul_nonneg hb0 hk0
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmul0 hmul d) (by positivity)

/-- Assumed logarithmic precision bounds for both crossing count and cost yield polynomial
bounds in inverse precision and `k`, with the same approximation on unit vectors
[AharonovArad2011, Theorem 5.2][AharonovArad2011]. -/
theorem theorem52_density_efficiency {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (k : ℕ)
    (ρ : BraidWord 8 → H →L[ℂ] H) (Ũ : H →L[ℂ] H) (cost : BraidWord 8 → ℕ)
    (C d : ℕ)
    (hsynth : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C * ((Real.log (1 / δ) + 1) * (k + 1)) ^ d) ∧
      ((cost b : ℝ) ≤ C * ((Real.log (1 / δ) + 1) * (k + 1)) ^ d) ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ)) :
    ∃ C' d' : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C' * ((δ⁻¹ + 1) * (k + 1)) ^ d') ∧
      ((cost b : ℝ) ≤ C' * ((δ⁻¹ + 1) * (k + 1)) ^ d') ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ) := by
  refine ⟨C, d, fun δ hδ hδ1 => ?_⟩
  obtain ⟨b, hb, hc, happrox⟩ := hsynth δ hδ hδ1
  have hmono := theorem52_base_mono C d k δ hδ hδ1
  exact ⟨b, le_trans hb hmono, le_trans hc hmono, happrox⟩

/-- Under the stated parameter and norm-preservation hypotheses, the supplied synthesis
guarantee yields crossing and cost bounds polynomial in inverse precision and `k`
[AharonovArad2011, Theorem 5.2][AharonovArad2011]. -/
theorem theorem52_synthesis {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (k : ℕ) (_hk : 4 < k) (_hk6 : k ≠ 6)
    (ρ : BraidWord 8 → H →L[ℂ] H) (Ũ : H →L[ℂ] H) (cost : BraidWord 8 → ℕ)
    (_hρ : ∀ (b : BraidWord 8) (p : H), ‖p‖ = 1 → ‖ρ b p‖ = 1)
    (_hŨ : ∀ p : H, ‖p‖ = 1 → ‖Ũ p‖ = 1)
    (C d : ℕ)
    (hsynth : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C * ((Real.log (1 / δ) + 1) * (k + 1)) ^ d) ∧
      ((cost b : ℝ) ≤ C * ((Real.log (1 / δ) + 1) * (k + 1)) ^ d) ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ)) :
    ∃ C' d' : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C' * ((δ⁻¹ + 1) * (k + 1)) ^ d') ∧
      ((cost b : ℝ) ≤ C' * ((δ⁻¹ + 1) * (k + 1)) ^ d') ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ) :=
  theorem52_density_efficiency k ρ Ũ cost C d hsynth

end Qatlib.Papers.BQPJonesPoly06.MainResults
