/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Transfer of latent decoder approximation

`continuous_decoder_uat_transfer` composes a supplied neural approximation property with a
continuous decoder on a compact latent domain. Starting from a continuous parameter map with
error at most half the target tolerance, it obtains a neural parameter map meeting the full
tolerance; `lemma3_expectation_corollary` integrates a uniform error bound. See [TranEtAl2026]
for the paper context.

## Main statements

* `continuous_decoder_uat_transfer`: On a compact latent domain, uniform approximation of
  continuous parameter maps transfers through a continuous decoder, turning a supplied `δ / 2`
  target approximation into a neural-parameterized approximation of error at most positive `δ`.
* `lemma3_expectation_corollary`: A uniform norm-error bound by `δ` gives expected norm error at
  most `δ` under a probability measure, assuming integrability.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.LatentUniversal

/-- On a compact latent domain, uniform approximation of continuous parameter maps transfers
through a continuous decoder, turning a supplied `δ / 2` target approximation into a
neural-parameterized approximation of error at most positive `δ` [TranEtAl2026]. -/
theorem continuous_decoder_uat_transfer
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {K : ℕ} {Op : Type*} [NormedAddCommGroup Op]
    (IsNNParametrized : (Z → (Fin K → ℝ)) → Prop)
    (V : Z → Op) (δ : ℝ) (hδ : 0 < δ)
    (c : Z → (Fin K → ℝ)) (hc : Continuous c)
    (C : (Fin K → ℝ) → Op) (hC : Continuous C)
    (happrox : ∀ z, ‖C (c z) - V z‖ ≤ δ / 2)
    (hnn : ∀ g : Z → (Fin K → ℝ), Continuous g → ∀ η > 0,
      ∃ θw : Z → (Fin K → ℝ), IsNNParametrized θw ∧ ∀ z, ‖θw z - g z‖ ≤ η) :
    ∃ θw : Z → (Fin K → ℝ), IsNNParametrized θw ∧
      ∀ z, ‖C (θw z) - V z‖ ≤ δ := by

  obtain ⟨R, hR⟩ := (isCompact_range hc).isBounded.subset_ball 0

  have hSc : IsCompact (Metric.closedBall (0 : Fin K → ℝ) (R + 1)) :=
    ProperSpace.isCompact_closedBall 0 _
  have huc := hSc.uniformContinuousOn_of_continuous hC.continuousOn
  obtain ⟨δ', hδ'pos, hδ'C⟩ := Metric.uniformContinuousOn_iff_le.1 huc (δ / 2) (by linarith)

  obtain ⟨θw, hθw, hθwap⟩ := hnn c hc (min (δ' / 2) 1) (lt_min (by linarith) one_pos)
  have hmin : min (δ' / 2) 1 ≤ δ' := le_trans (min_le_left _ _) (by linarith)
  refine ⟨θw, hθw, fun z => ?_⟩
  have hcn : ‖c z‖ < R := by
    have h := hR (Set.mem_range_self z)
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hcz : c z ∈ Metric.closedBall (0 : Fin K → ℝ) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hθz : θw z ∈ Metric.closedBall (0 : Fin K → ℝ) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖θw z - c z‖ ≤ 1 := le_trans (hθwap z) (min_le_right _ _)
    have h2 : ‖θw z‖ ≤ ‖θw z - c z‖ + ‖c z‖ := by
      simpa using norm_add_le (θw z - c z) (c z)
    linarith
  have hd : dist (θw z) (c z) ≤ δ' :=
    le_trans (by rw [dist_eq_norm]; exact hθwap z) hmin
  have h1 : dist (C (θw z)) (C (c z)) ≤ δ / 2 := hδ'C _ hθz _ hcz hd
  have h2 : dist (C (c z)) (V z) ≤ δ / 2 := by
    rw [dist_eq_norm]; exact happrox z
  have h3 : dist (C (θw z)) (V z) ≤ δ :=
    le_trans (dist_triangle _ _ _) (by linarith)
  rwa [dist_eq_norm] at h3

/-- A uniform norm-error bound by `δ` gives expected norm error at most `δ` under a probability
measure, assuming integrability [TranEtAl2026]. -/
theorem lemma3_expectation_corollary
    {Z Op : Type*} [MeasurableSpace Z] (r : Measure Z) [IsProbabilityMeasure r]
    [NormedAddCommGroup Op]
    (U V : Z → Op) (δ : ℝ)
    (hbound : ∀ z, ‖U z - V z‖ ≤ δ)
    (hint : Integrable (fun z => ‖U z - V z‖) r) :
    ∫ z, ‖U z - V z‖ ∂r ≤ δ := by
  have hconst : Integrable (fun _ : Z => δ) r := integrable_const _
  have hmono : ∫ z, ‖U z - V z‖ ∂r ≤ ∫ z, δ ∂r :=
    integral_mono hint hconst hbound
  rwa [integral_const, probReal_univ, one_smul] at hmono

end Qatlib.Papers.LatentPQCTran26.MainResults.LatentUniversal
