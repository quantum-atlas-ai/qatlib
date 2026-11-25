/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.NonuniformCL
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedFilaments

import Mathlib.Tactic.Ring

/-!
# Centerline helicity as one oriented product integral

The oriented bundle measure is the sum of the individual filament
measures. Its self-pairing recovers both the off-diagonal linking
terms and the diagonal writhe terms in the centerline helicity.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped BigOperators

local notation "VorticitySpace" => Fin 3 → ℝ

/-- Add the signed oriented filament contributions to form the measure of a bundle. -/
noncomputable def orientedBundleMeasure {ι : Type*} (κ : ι → ℝ)
    (γ : ι → ℝ → VorticitySpace) : Measure VorticityElement :=
  Measure.sum (fun i => orientedFilamentMeasure (κ i) (γ i))

/-- The oriented bundle self-pairing is the actual geometric centerline
helicity, including the self-writhe terms. -/
theorem integral_orientedBundle_eq_helicity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → VorticitySpace) (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hG : ∀ i j, Integrable (fun p : ℝ × ℝ => gaussKernel (γ i) (γ j) p.1 p.2) gaussMeasure) :
    (∫ p, gaussSoftKernel 0 p.1 p.2
      ∂((orientedBundleMeasure κ γ).prod (orientedBundleMeasure κ γ))) =
      centerlineHelicityGaussSelf κ γ := by
  let μ := fun i => orientedFilamentMeasure (κ i) (γ i)
  let (i : ι) : IsFiniteMeasure (μ i) := isFiniteMeasure_orientedFilament (κ i) (γ i) (hγ i)
  have hμ (p : ι × ι) :
      Integrable (fun s => gaussSoftKernel 0 s.1 s.2) ((μ p.1).prod (μ p.2)) :=
    integrable_orientedFilament_pair (κ p.1) (κ p.2) (γ p.1) (γ p.2)
      (hγ p.1) (hγ p.2) (hG p.1 p.2)
  change (∫ p, gaussSoftKernel 0 p.1 p.2 ∂(Measure.sum μ).prod (Measure.sum μ)) = _
  rw [Measure.prod_sum, Measure.sum_fintype, integral_finsetSum_measure (fun p _ => hμ p)]
  dsimp only [μ]
  simp_rw [integral_orientedFilament_eq_gaussLinking _ _ _ _ (hγ _) (hγ _)]
  rw [Fintype.sum_prod_type, centerlineHelicityGaussSelf_eq, pairLinkingGauss_eq,
    writheGaussPart, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiag :
      (∑ j, if i = j then κ i * κ j * gaussLinking (γ i) (γ j) else 0) =
        κ i ^ 2 * gaussWrithe (γ i) := by
    simp [pow_two, gaussWrithe]
  rw [← hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j <;> simp [hij]

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
