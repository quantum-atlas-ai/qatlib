/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BundleGaussLimit

import Mathlib.Tactic.Ring

/-!
# Separating close interactions within and between filaments

The absolute near-pair mass is the sum of the restricted Gauss
integrals on the filament parameter squares. A uniform absolute
self-writhe bound controls the contribution of same-filament
pairs by the inverse effective bundle size.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- The absolute Gauss interaction of the parameters whose spatial
chord is shorter than the cutoff. -/
noncomputable def absoluteGaussNear (δ : ℝ) (γ η : ℝ → VorticitySpace) : ℝ :=
  ∫ p in {p : ℝ × ℝ | euclideanLength (γ p.1 - η p.2) < δ},
    |gaussKernel γ η p.1 p.2| ∂gaussMeasure

/-- The absolute near-pair mass of a rescaled bundle is exactly the
absolute circulation-weighted sum of the near integrals on its
filament parameter squares. -/
theorem setIntegral_rescaledBundle_nearPairs {ι : Type*} [Fintype ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hG : ∀ i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ i) (γ j) p.1 p.2) gaussMeasure)
    (δ : ℝ) :
    (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
      (rescaledOrientedBundle κ γ hγ).toMeasure.prod (rescaledOrientedBundle κ γ hγ).toMeasure)) =
    (∑ i, ∑ j, |κ i * κ j| * absoluteGaussNear δ (γ i) (γ j)) / (∑ i, κ i) ^ 2 := by
  let := isFiniteMeasure_orientedBundle κ γ hγ
  let a := |(∑ i, κ i)|⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (abs_nonneg _)
  let ν := fun i => orientedFilamentMeasure (κ i) (γ i)
  let (i : ι) : IsFiniteMeasure (ν i) := isFiniteMeasure_orientedFilament (κ i) (γ i) (hγ i)
  have hp (p : ι × ι) :
      Integrable (fun s => |gaussSoftKernel 0 s.1 s.2|)
        (((ν p.1).prod (ν p.2)).restrict (gaussNearPairs δ)) :=
    (integrable_orientedFilament_pair (κ p.1) (κ p.2) (γ p.1) (γ p.2)
      (hγ p.1) (hγ p.2) (hG p.1 p.2)).abs.integrableOn
  let S : Set (VorticitySpace × VorticitySpace) :=
    {p | euclideanLength (p.1 - p.2) < δ}
  have hS : MeasurableSet S :=
    measurableSet_lt (continuous_euclideanLength.measurable.comp (measurable_fst.sub measurable_snd))
      measurable_const
  change (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
    (ENNReal.ofReal a • Measure.sum ν).prod (ENNReal.ofReal a • Measure.sum ν))) = _
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.restrict_smul, Measure.restrict_smul,
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha, smul_eq_mul, smul_eq_mul,
    Measure.prod_sum, Measure.restrict_sum _ (measurableSet_gaussNearPairs δ), Measure.sum_fintype,
    integral_finsetSum_measure (fun p _ => hp p), Fintype.sum_prod_type]
  have hpair (i j : ι) :
      (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂((ν i).prod (ν j))) =
        |κ i * κ j| * absoluteGaussNear δ (γ i) (γ j) :=
    setIntegral_abs_orientedFilament_pair (κ i) (κ j) (γ i) (γ j) (hγ i) (hγ j) hS
  simp_rw [hpair]
  rw [← mul_assoc, ← pow_two]
  dsimp only [a]
  rw [inv_pow, sq_abs, div_eq_mul_inv, mul_comm]

/-- The same-filament contribution to the absolute near interaction
is at most a uniform absolute writhe bound times the inverse
effective bundle size. The remaining sum is over distinct filaments. -/
theorem setIntegral_rescaledBundle_nearPairs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hG : ∀ i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ i) (γ j) p.1 p.2) gaussMeasure)
    {W : ℝ} (hW : ∀ i, (∫ p, |gaussKernel (γ i) (γ i) p.1 p.2| ∂gaussMeasure) ≤ W)
    (δ : ℝ) :
    (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
      (rescaledOrientedBundle κ γ hγ).toMeasure.prod (rescaledOrientedBundle κ γ hγ).toMeasure)) ≤
    (∑ i, ∑ j, if i = j then 0 else |κ i * κ j| * absoluteGaussNear δ (γ i) (γ j)) /
      (∑ i, κ i) ^ 2 + W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2) := by
  rw [setIntegral_rescaledBundle_nearPairs κ γ hγ hG δ]
  let T := fun i j => |κ i * κ j| * absoluteGaussNear δ (γ i) (γ j)
  have hsplit (i : ι) : (∑ j, T i j) = (∑ j, if i = j then 0 else T i j) + T i i := by
    have hd : (∑ j, if i = j then T i j else 0) = T i i := by simp
    rw [← hd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, T i j) / (∑ i, κ i) ^ 2 ≤ _
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, add_div]
  refine add_le_add_right ?_ _
  rw [show W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2) =
    (W * ∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2 by ring]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : absoluteGaussNear δ (γ i) (γ i) ≤ W :=
    (setIntegral_le_integral (hG i i).abs (Eventually.of_forall fun p => abs_nonneg _)).trans (hW i)
  change |κ i * κ i| * absoluteGaussNear δ (γ i) (γ i) ≤ W * κ i ^ 2
  rw [← pow_two, abs_of_nonneg (sq_nonneg _), mul_comm W]
  exact mul_le_mul_of_nonneg_left hi (sq_nonneg _)

/-- In the classical limit, uniform absolute self-writhe bounds and
vanishing inverse effective bundle size remove the same-filament
part of the near-pair hypothesis. Only the absolute near interaction
between distinct filaments needs separate uniform control. -/
theorem tendsto_rescaledCenterline_of_offNear
    (κ : (n : ℕ) → Fin (n + 1) → ℝ)
    (γ : (n : ℕ) → Fin (n + 1) → ℝ → VorticitySpace)
    (hγ : ∀ n i, ContDiff ℝ 1 (γ n i))
    (hG : ∀ n i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ n i) (γ n j) p.1 p.2) gaussMeasure)
    {ω : VorticitySpace → VorticitySpace} (hm : Measurable ω) (hω : Integrable ω)
    {C : ℝ} (hb : ∀ x, ‖ω x‖ ≤ C)
    (hF : Tendsto (fun n => rescaledOrientedBundle (κ n) (γ n) (hγ n)) atTop
      (𝓝 (continuumOriented hm hω)))
    {W : ℝ} (hW : ∀ n i, (∫ p, |gaussKernel (γ n i) (γ n i) p.1 p.2| ∂gaussMeasure) ≤ W)
    (hsize : Tendsto (fun n => (∑ i, κ n i ^ 2) / (∑ i, κ n i) ^ 2) atTop (𝓝 0))
    (hoff : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ n in atTop,
      (∑ i, ∑ j, if i = j then 0 else |κ n i * κ n j| * absoluteGaussNear δ (γ n i) (γ n j)) /
        (∑ i, κ n i) ^ 2 < ε) :
    Tendsto (fun n => centerlineHelicityGaussSelf (κ n) (γ n) / (∑ i, κ n i) ^ 2)
      atTop (𝓝 (crossPairing ω ω)) := by
  apply tendsto_rescaledCenterline_crossPairing κ γ hγ hG hm hω hb hF
  intro ε hε b hb'
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hoff'⟩ := hoff (ε / 2) hhalf b hb'
  refine ⟨δ, hδ, ?_⟩
  have hdiag : Tendsto (fun n => W * ((∑ i, κ n i ^ 2) / (∑ i, κ n i) ^ 2))
      atTop (𝓝 0) := by
    simpa using hsize.const_mul W
  filter_upwards [hoff', (tendsto_order.1 hdiag).2 (ε / 2) hhalf] with n hOff hDiag
  have h := setIntegral_rescaledBundle_nearPairs_le (κ n) (γ n) (hγ n) (hG n) (hW n) δ
  exact h.trans_lt (by linarith)

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
