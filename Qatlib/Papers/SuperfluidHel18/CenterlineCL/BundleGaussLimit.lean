/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BiotSavartIntegrability
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedBundle
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussFiniteCutoff

import Mathlib.Tactic.Ring

/-!
# An oriented-measure classical limit for centerline helicity

The normalized geometric helicity of a finite bundle and the
Biot–Savart helicity of an integrable vorticity are the same full
product interaction evaluated on different measures. Weak convergence
of the normalized oriented bundles and uniform near-pair control
give the corresponding convergence of the helicities.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- A bundle of finitely many smooth filaments has finite total oriented mass. -/
theorem isFiniteMeasure_orientedBundle {ι : Type*} [Fintype ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i)) :
    IsFiniteMeasure (orientedBundleMeasure κ γ) := by
  refine ⟨?_⟩
  rw [orientedBundleMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  let := isFiniteMeasure_orientedFilament (κ i) (γ i) (hγ i)
  exact measure_lt_top _ _

/-- The original finite bundle measure scaled inversely to the absolute
total circulation, so its self-pairing has the required squared scale. -/
noncomputable def rescaledOrientedBundle {ι : Type*} [Fintype ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i)) :
    FiniteMeasure VorticityElement := by
  letI := isFiniteMeasure_orientedBundle κ γ hγ
  exact ⟨ENNReal.ofReal (|(∑ i, κ i)|⁻¹) • orientedBundleMeasure κ γ,
    Measure.smul_finite _ ENNReal.ofReal_ne_top⟩

/-- The bounded or integrable continuum vorticity induces a finite
oriented measure by weighting volume with its tangent magnitude. -/
noncomputable def continuumOriented {ω : VorticitySpace → VorticitySpace}
    (hm : Measurable ω) (hω : Integrable ω) : FiniteMeasure VorticityElement :=
  ⟨orientedVorticityMeasure volume id ω,
    isFiniteMeasure_orientedVorticityMeasure volume measurable_id hm hω⟩

/-- The rescaled oriented bundle self-pairing equals the actual
centerline helicity divided by the squared total circulation. -/
theorem integral_rescaledOrientedBundle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hG : ∀ i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ i) (γ j) p.1 p.2) gaussMeasure) :
    (∫ p, gaussSoftKernel 0 p.1 p.2 ∂((rescaledOrientedBundle κ γ hγ).toMeasure.prod
      (rescaledOrientedBundle κ γ hγ).toMeasure)) =
      centerlineHelicityGaussSelf κ γ / (∑ i, κ i) ^ 2 := by
  let := isFiniteMeasure_orientedBundle κ γ hγ
  let a := |(∑ i, κ i)|⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (abs_nonneg _)
  let ν := orientedBundleMeasure κ γ
  change (∫ p, gaussSoftKernel 0 p.1 p.2 ∂((ENNReal.ofReal a • ν).prod
    (ENNReal.ofReal a • ν))) = _
  rw [Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ha, smul_eq_mul, smul_eq_mul]
  change a * (a * ∫ p, gaussSoftKernel 0 p.1 p.2 ∂((orientedBundleMeasure κ γ).prod
    (orientedBundleMeasure κ γ))) = _
  rw [integral_orientedBundle_eq_helicity κ γ hγ hG, ← mul_assoc, ← pow_two]
  dsimp only [a]
  rw [inv_pow, sq_abs, div_eq_mul_inv, mul_comm]

/-- Pairwise integrability of the geometric Gauss kernels gives
integrability for the entire rescaled oriented bundle product. -/
theorem integrable_rescaledOrientedBundle {ι : Type*} [Fintype ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hG : ∀ i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ i) (γ j) p.1 p.2) gaussMeasure) :
    Integrable (fun p => gaussSoftKernel 0 p.1 p.2) ((rescaledOrientedBundle κ γ hγ).toMeasure.prod
      (rescaledOrientedBundle κ γ hγ).toMeasure) := by
  let ν := fun i => orientedFilamentMeasure (κ i) (γ i)
  let (i : ι) := isFiniteMeasure_orientedFilament (κ i) (γ i) (hγ i)
  let c := ENNReal.ofReal (|(∑ i, κ i)|⁻¹)
  change Integrable (fun p => gaussSoftKernel 0 p.1 p.2)
    ((c • Measure.sum ν).prod (c • Measure.sum ν))
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_sum, Measure.sum_fintype]
  have hpair (p : ι × ι) : Integrable (fun s => gaussSoftKernel 0 s.1 s.2) ((ν p.1).prod (ν p.2)) :=
    integrable_orientedFilament_pair (κ p.1) (κ p.2) (γ p.1) (γ p.2)
      (hγ p.1) (hγ p.2) (hG p.1 p.2)
  have h : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) (∑ p : ι × ι, (ν p.1).prod (ν p.2)) :=
    integrable_finsetSum_measure.2 (fun p _ => hpair p)
  exact (h.smul_measure ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top

/-- Under weak oriented-measure convergence and uniform smallness
of the absolute near-pair interaction, the normalized centerline
helicities converge to the Biot–Savart helicity of the limit vorticity. -/
theorem tendsto_rescaledCenterline_crossPairing (κ : (n : ℕ) → Fin (n + 1) → ℝ)
    (γ : (n : ℕ) → Fin (n + 1) → ℝ → VorticitySpace)
    (hγ : ∀ n i, ContDiff ℝ 1 (γ n i))
    (hG : ∀ n i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ n i) (γ n j) p.1 p.2) gaussMeasure)
    {ω : VorticitySpace → VorticitySpace} (hm : Measurable ω) (hω : Integrable ω)
    {C : ℝ} (hb : ∀ x, ‖ω x‖ ≤ C)
    (hF : Tendsto (fun n => rescaledOrientedBundle (κ n) (γ n) (hγ n)) atTop
      (𝓝 (continuumOriented hm hω)))
    (hnear : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ n in atTop,
      (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
        (rescaledOrientedBundle (κ n) (γ n) (hγ n)).toMeasure.prod
        (rescaledOrientedBundle (κ n) (γ n) (hγ n)).toMeasure)) < ε) :
    Tendsto (fun n => centerlineHelicityGaussSelf (κ n) (γ n) / (∑ i, κ n i) ^ 2)
      atTop (𝓝 (crossPairing ω ω)) := by
  have hlen (v : VorticitySpace) : 0 ≤ euclideanLength v := norm_nonneg _
  have hi : Integrable (fun p => gaussSoftKernel 0 p.1 p.2)
      ((continuumOriented hm hω).toMeasure.prod (continuumOriented hm hω).toMeasure) := by
    change Integrable _ ((orientedVorticityMeasure volume id ω).prod
      (orientedVorticityMeasure volume id ω))
    rw [integrable_prod_orientedVorticityMeasure volume volume measurable_id hm measurable_id hm]
    simpa only [id_eq, max_eq_right (hlen _), bsPairKernel] using
      integrable_bsPairKernel_of_bounded hm hm hω hω hb
  have h := tendsto_finiteGaussFullPairing hF
    (fun n => integrable_rescaledOrientedBundle (κ n) (γ n) (hγ n) (hG n)) hi hnear
  have hlimit : (∫ p, gaussSoftKernel 0 p.1 p.2 ∂((continuumOriented hm hω).toMeasure.prod
    (continuumOriented hm hω).toMeasure)) = crossPairing ω ω :=
    integral_orientedVorticityMeasure_eq_crossPairing hm hm
  simpa only [integral_rescaledOrientedBundle _ _ _ (hG _), hlimit] using h

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
