/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BundleGaussLimit

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Concentration of geometric vortex bundles

Compressing a bundle scales the total oriented mass by the spatial
scale. Its normalized centerline helicity remains fixed at positive
scales. A nonzero seed therefore shows the role of the close-pair
condition in the weak convergence theorem.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology

/-- A spatial dilation multiplies the total oriented mass of each
filament by the magnitude of the spatial scale. -/
private theorem orientedFilamentMeasure_univ_const_smul (κ c : ℝ) (γ : ℝ → Fin 3 → ℝ)
    (hγ : ContDiff ℝ 1 γ) :
    orientedFilamentMeasure κ (fun s => c • γ s) univ =
      ‖c‖ₑ * orientedFilamentMeasure κ γ univ := by
  let η := fun s => c • γ s
  let μ := volume.restrict (Icc (0 : ℝ) (2 * π))
  have hη : ContDiff ℝ 1 η := ContDiff.const_smul c hγ
  have hκ : Continuous (fun _ : ℝ => κ) := continuous_const
  have hγd : Continuous (fun s => deriv γ s) := hγ.continuous_deriv (by norm_num)
  have hηd : Continuous (fun s => deriv η s) := hη.continuous_deriv (by norm_num)
  have hγt : Measurable (fun s => κ • deriv γ s) := (hκ.fun_smul hγd).measurable
  have hηt : Measurable (fun s => κ • deriv η s) := (hκ.fun_smul hηd).measurable
  have hd (s : ℝ) : deriv η s = c • deriv γ s :=
    (HasDerivAt.const_smul c ((hγ.contDiffAt.differentiableAt (by norm_num)).hasDerivAt)).deriv
  change orientedFilamentMeasure κ η univ = _
  rw [orientedFilamentMeasure, orientedFilamentMeasure,
    orientedVorticityMeasure_univ μ hη.continuous.measurable hηt,
    orientedVorticityMeasure_univ μ hγ.continuous.measurable hγt]
  have h (s : ℝ) : ‖κ • deriv η s‖ₑ = ‖c‖ₑ * ‖κ • deriv γ s‖ₑ := by
    rw [hd s, smul_comm κ c, enorm_smul]
  simp_rw [h]
  exact lintegral_const_mul' _ _ enorm_ne_top

/-- The mass of a rescaled finite bundle still changes linearly
with the absolute spatial dilation factor. -/
theorem rescaledOrientedBundle_mass_const_smul {ι : Type*} [Fintype ι]
    (κ : ι → ℝ) (γ : ι → ℝ → Fin 3 → ℝ) (hγ : ∀ i, ContDiff ℝ 1 (γ i)) (c : ℝ) :
    (rescaledOrientedBundle κ (fun i s => c • γ i s)
        (fun i => ContDiff.const_smul c (hγ i))).mass =
      ‖c‖₊ * (rescaledOrientedBundle κ γ hγ).mass := by
  apply ENNReal.coe_inj.mp
  rw [ENNReal.coe_mul, FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
  let d := ENNReal.ofReal (|(∑ i, κ i)|⁻¹)
  change (d • orientedBundleMeasure κ (fun i s => c • γ i s)) univ =
    ‖c‖ₑ * (d • orientedBundleMeasure κ γ) univ
  simp only [Measure.smul_apply, smul_eq_mul, orientedBundleMeasure,
    Measure.sum_apply _ MeasurableSet.univ, tsum_fintype, orientedFilamentMeasure_univ_const_smul _ _ _ (hγ _)]
  rw [← Finset.mul_sum, mul_left_comm d]

/-- Bundles compressed by scales tending to zero converge weakly
to the zero oriented measure, with all circulations fixed. -/
theorem tendsto_rescaledOrientedBundle_const_smul_zero {ι τ : Type*} [Fintype ι] {l : Filter τ}
    (κ : ι → ℝ) (γ : ι → ℝ → Fin 3 → ℝ) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (c : τ → ℝ) (hc : Tendsto c l (𝓝 0)) :
    Tendsto (fun n => rescaledOrientedBundle κ (fun i s => c n • γ i s)
        (fun i => ContDiff.const_smul (c n) (hγ i))) l (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖c n‖₊) l (𝓝 0) := by
    simpa only [nnnorm_zero] using hc.nnnorm
  have hmass : Tendsto (fun n => ‖c n‖₊ * (rescaledOrientedBundle κ γ hγ).mass) l (𝓝 0) := by
    simpa only [zero_mul] using hnorm.mul_const (rescaledOrientedBundle κ γ hγ).mass
  apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
  exact hmass.congr' (Eventually.of_forall fun n =>
    (rescaledOrientedBundle_mass_const_smul κ γ hγ (c n)).symm)

/-- A positive common dilation preserves the actual centerline
helicity, including the same-filament writhe. -/
theorem centerlineHelicityGaussSelf_const_smul_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → Fin 3 → ℝ) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    {c : ℝ} (hc : 0 < c) :
    centerlineHelicityGaussSelf κ (fun i s => c • γ i s) = centerlineHelicityGaussSelf κ γ := by
  have h (i j : ι) :
      gaussLinking (fun s => c • γ i s) (fun s => c • γ j s) = gaussLinking (γ i) (γ j) :=
    gaussLinking_const_smul_eq _ _ hc (hγ i) (hγ j)
  simp only [centerlineHelicityGaussSelf, centerlineHelicityGauss, gaussWrithe, h]

/-- A seed with nonzero normalized centerline helicity retains
that value upon concentration even though its oriented measure
tends weakly to zero. -/
theorem concentratedBundle_not_tendsto_zero_helicity {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter τ} [l.NeBot] (κ : ι → ℝ) (γ : ι → ℝ → Fin 3 → ℝ)
    (hγ : ∀ i, ContDiff ℝ 1 (γ i)) (c : τ → ℝ) (hc : Tendsto c l (𝓝 0))
    (hpos : ∀ n, 0 < c n)
    (hne : centerlineHelicityGaussSelf κ γ / (∑ i, κ i) ^ 2 ≠ 0) :
    Tendsto (fun n => rescaledOrientedBundle κ (fun i s => c n • γ i s)
        (fun i => ContDiff.const_smul (c n) (hγ i))) l (𝓝 0) ∧
      ¬ Tendsto (fun n => centerlineHelicityGaussSelf κ (fun i s => c n • γ i s) /
        (∑ i, κ i) ^ 2) l (𝓝 0) := by
  refine ⟨tendsto_rescaledOrientedBundle_const_smul_zero κ γ hγ c hc, ?_⟩
  have h (n : τ) := centerlineHelicityGaussSelf_const_smul_eq κ γ hγ (hpos n)
  simp_rw [h]
  intro hzero
  exact hne (tendsto_nhds_unique tendsto_const_nhds hzero)

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
