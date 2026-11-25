/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedGaussLimit

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Weak convergence for softened Gauss pairings

At positive cutoff, the finite oriented self-pairing is bounded
by the square of the total mass. This bound handles convergence
to the zero measure as well as nonzero probability normalization.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped ENNReal Real Topology

/-- At any positive cutoff, the unnormalized Gauss self-pairing
is controlled by the kernel bound times the square of the mass. -/
theorem abs_integral_gaussSoftKernel_finite_le {δ : ℝ} (hδ : 0 < δ)
    (ν : FiniteMeasure VorticityElement) :
    |∫ p, gaussSoftKernel δ p.1 p.2 ∂(ν.toMeasure.prod ν.toMeasure)| ≤
      (ν.mass : ℝ) ^ 2 * (3 / (2 * π * δ ^ 2)) := by
  rw [← orientedGaussSelf_mass_normalize, orientedGaussSelf, abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let μ := (ν.normalize.prod ν.normalize).toMeasure
  have h : ∀ᵐ p : VorticityElement × VorticityElement ∂μ,
      ‖gaussSoftKernel δ p.1 p.2‖ ≤ 3 / (2 * π * δ ^ 2) :=
    Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_gaussSoftKernel_le hδ p.1 p.2
  simpa only [Real.norm_eq_abs, μ, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const h

/-- Weak convergence of finite oriented measures implies convergence
of their unnormalized Gauss self-pairings at every positive cutoff. -/
theorem tendsto_finiteGaussSoftPairing {ι : Type*} {l : Filter ι}
    {F : ι → FiniteMeasure VorticityElement} {μ : FiniteMeasure VorticityElement}
    (hF : Tendsto F l (𝓝 μ)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => ∫ p, gaussSoftKernel δ p.1 p.2 ∂((F i).toMeasure.prod (F i).toMeasure))
      l (𝓝 (∫ p, gaussSoftKernel δ p.1 p.2 ∂(μ.toMeasure.prod μ.toMeasure))) := by
  have hm : Tendsto (fun i => ((F i).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.comp FiniteMeasure.continuous_mass).continuousAt.tendsto.comp hF
  by_cases hμ : μ = 0
  · subst μ
    have hm₀ : Tendsto (fun i => ((F i).mass : ℝ)) l (𝓝 0) := by simpa using hm
    have hDom : Tendsto (fun i => ((F i).mass : ℝ) ^ 2 * (3 / (2 * π * δ ^ 2))) l (𝓝 0) := by
      simpa using (hm₀.pow 2).mul_const (3 / (2 * π * δ ^ 2))
    have hZero : (∫ p, gaussSoftKernel δ p.1 p.2 ∂((0 : FiniteMeasure VorticityElement).toMeasure.prod
        (0 : FiniteMeasure VorticityElement).toMeasure)) = 0 := by
      rw [← orientedGaussSelf_mass_normalize]
      simp [orientedGaussSelf]
    rw [hZero, tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    exact squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _)
      (Eventually.of_forall fun i => abs_integral_gaussSoftKernel_finite_le hδ (F i)) hDom
  · have hn := FiniteMeasure.tendsto_normalize_of_tendsto hF hμ
    have hp := (hm.pow 2).mul (tendsto_gaussSoftPairing hδ hn hn)
    change Tendsto (fun i => orientedGaussSelf δ ((F i).mass : ℝ) (F i).normalize) l
      (𝓝 (orientedGaussSelf δ (μ.mass : ℝ) μ.normalize)) at hp
    simpa only [orientedGaussSelf_mass_normalize] using hp

/-- Weak limits of finite oriented measures preserve the full Gauss
self-pairing when the absolute close-pair interactions are uniformly small. -/
theorem tendsto_finiteGaussFullPairing {ι : Type*} {l : Filter ι}
    {F : ι → FiniteMeasure VorticityElement} {μ : FiniteMeasure VorticityElement}
    (hF : Tendsto F l (𝓝 μ))
    (hfull : ∀ i, Integrable (fun p => gaussSoftKernel 0 p.1 p.2)
      ((F i).toMeasure.prod (F i).toMeasure))
    (hμ : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) (μ.toMeasure.prod μ.toMeasure))
    (hnear : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ i in l,
      (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2|
        ∂((F i).toMeasure.prod (F i).toMeasure)) < ε) :
    Tendsto (fun i => ∫ p, gaussSoftKernel 0 p.1 p.2 ∂((F i).toMeasure.prod (F i).toMeasure))
      l (𝓝 (∫ p, gaussSoftKernel 0 p.1 p.2 ∂(μ.toMeasure.prod μ.toMeasure))) := by
  let H := fun (δ : ℝ) (ν : FiniteMeasure VorticityElement) =>
    ∫ p, gaussSoftKernel δ p.1 p.2 ∂(ν.toMeasure.prod ν.toMeasure)
  have hlimit : Tendsto (fun δ => H δ μ) (𝓝[>] (0 : ℝ)) (𝓝 (H 0 μ)) :=
    tendsto_integral_gaussSoftKernel hμ
  change Tendsto (fun i => H 0 (F i)) l (𝓝 (H 0 μ))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨b, hb, hlim⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1
    ((Metric.tendsto_nhds.1 hlimit) (ε / 3) hthird)
  obtain ⟨δ, hδ, hδnear⟩ := hnear (ε / 3) hthird b hb
  have hcut : Tendsto (fun i => H δ (F i)) l (𝓝 (H δ μ)) :=
    tendsto_finiteGaussSoftPairing hF hδ.1
  filter_upwards [hδnear, (Metric.tendsto_nhds.1 hcut) (ε / 3) hthird] with i hclose hweak
  have hleft : dist (H 0 (F i)) (H δ (F i)) < ε / 3 := by
    rw [Real.dist_eq]
    exact (abs_integral_gaussSoftKernel_error hδ.1 (hfull i)).trans_lt hclose
  have hright : dist (H δ μ) (H 0 μ) < ε / 3 := hlim hδ
  calc
    _ ≤ dist (H 0 (F i)) (H δ (F i)) + dist (H δ (F i)) (H 0 μ) := dist_triangle _ _ _
    _ ≤ dist (H 0 (F i)) (H δ (F i)) + (dist (H δ (F i)) (H δ μ) + dist (H δ μ) (H 0 μ)) :=
      add_le_add (le_refl _) (dist_triangle _ _ _)
    _ < ε := by linarith

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
