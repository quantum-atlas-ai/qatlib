/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedVorticity

import Mathlib.Tactic.Ring

/-!
# Oriented measures for Gauss helicity of filaments

On a filament the tangent is weighted by its signed circulation.
The unregularized interaction of two such oriented measures is
their actual Gauss linking integral with both circulation weights.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open scoped Real

local notation "VorticitySpace" => Fin 3 → ℝ

/-- The oriented vorticity of a filament on the Gauss parameter interval,
with its signed circulation included in the tangent. -/
noncomputable def orientedFilamentMeasure (κ : ℝ) (γ : ℝ → VorticitySpace) :
    Measure VorticityElement :=
  orientedVorticityMeasure (volume.restrict (Icc 0 (2 * π))) γ (fun s => κ • deriv γ s)

/-- The signed tangent is continuous and is integrable on the compact
parameter interval of a smooth filament. -/
private theorem continuous_signedTangent (κ : ℝ) (γ : ℝ → VorticitySpace)
    (hγ : ContDiff ℝ 1 γ) : Continuous (fun s => κ • deriv γ s) := by
  have hκ : Continuous (fun _ : ℝ => κ) := continuous_const
  have hd : Continuous (fun s : ℝ => deriv γ s) := hγ.continuous_deriv (by norm_num)
  exact hκ.fun_smul hd

/-- A smooth filament has finite oriented mass because its signed tangent
is continuous on the compact Gauss parameter interval. -/
theorem isFiniteMeasure_orientedFilament (κ : ℝ) (γ : ℝ → VorticitySpace)
    (hγ : ContDiff ℝ 1 γ) : IsFiniteMeasure (orientedFilamentMeasure κ γ) :=
  isFiniteMeasure_orientedVorticityMeasure (volume.restrict (Icc 0 (2 * π)))
    hγ.continuous.measurable (continuous_signedTangent κ γ hγ).measurable
    ((continuous_signedTangent κ γ hγ).continuousOn.integrableOn_compact isCompact_Icc)

/-- The cyclic triple product converts the zero-cutoff pairing of signed
tangents to the actual circulation-weighted Gauss kernel. -/
private theorem orientedFilament_integrand_eq (κ κ' : ℝ) (γ η : ℝ → VorticitySpace)
    (s t : ℝ) :
    dot3 (κ • deriv γ s) (cross3 (κ' • deriv η t) (γ s - η t)) /
      (4 * π * max 0 (euclideanLength (γ s - η t)) ^ 3) =
    κ * κ' * gaussKernel γ η s t := by
  have hlen : 0 ≤ euclideanLength (γ s - η t) := norm_nonneg _
  rw [max_eq_right hlen, gaussKernel, cross3_smul_left, dot3_smul_left, dot3_smul_right]
  rw [← mul_div_assoc]
  congr 1
  simp [dot3, cross3]
  ring

/-- The oriented product inherits absolute integrability of the original
pairwise Gauss kernel. -/
theorem integrable_orientedFilament_pair (κ κ' : ℝ) (γ η : ℝ → VorticitySpace)
    (hγ : ContDiff ℝ 1 γ) (hη : ContDiff ℝ 1 η)
    (hG : Integrable (fun p : ℝ × ℝ => gaussKernel γ η p.1 p.2) gaussMeasure) :
    Integrable (fun p => gaussSoftKernel 0 p.1 p.2)
      ((orientedFilamentMeasure κ γ).prod (orientedFilamentMeasure κ' η)) := by
  let μ := volume.restrict (Icc (0 : ℝ) (2 * π))
  unfold orientedFilamentMeasure
  rw [integrable_prod_orientedVorticityMeasure μ μ hγ.continuous.measurable
    (continuous_signedTangent κ γ hγ).measurable hη.continuous.measurable
    (continuous_signedTangent κ' η hη).measurable]
  exact (hG.const_mul (κ * κ')).congr
    (Eventually.of_forall fun p => (orientedFilament_integrand_eq κ κ' γ η p.1 p.2).symm)

/-- Two oriented filament measures pair to the circulation-weighted actual
Gauss linking integral. The identity also applies to a self pairing. -/
theorem integral_orientedFilament_eq_gaussLinking (κ κ' : ℝ) (γ η : ℝ → VorticitySpace)
    (hγ : ContDiff ℝ 1 γ) (hη : ContDiff ℝ 1 η) :
    (∫ p, gaussSoftKernel 0 p.1 p.2 ∂((orientedFilamentMeasure κ γ).prod
      (orientedFilamentMeasure κ' η))) = κ * κ' * gaussLinking γ η := by
  let μ := volume.restrict (Icc (0 : ℝ) (2 * π))
  have hγ' := (continuous_signedTangent κ γ hγ).measurable
  have hη' := (continuous_signedTangent κ' η hη).measurable
  change (∫ p, gaussSoftKernel 0 p.1 p.2 ∂((orientedVorticityMeasure μ γ
    (fun s => κ • deriv γ s)).prod (orientedVorticityMeasure μ η
    (fun s => κ' • deriv η s)))) = _
  rw [integral_prod_orientedVorticityMeasure μ μ hγ.continuous.measurable hγ'
    hη.continuous.measurable hη', gaussLinking, ← integral_const_mul]
  exact integral_congr_ae
    (Eventually.of_forall fun p => orientedFilament_integrand_eq κ κ' γ η p.1 p.2)

/-- The absolute interaction restricted to a measurable set of
position pairs pulls back to the corresponding subset of the
Gauss parameter square, weighted by the absolute circulations. -/
theorem setIntegral_abs_orientedFilament_pair (κ κ' : ℝ) (γ η : ℝ → VorticitySpace)
    (hγ : ContDiff ℝ 1 γ) (hη : ContDiff ℝ 1 η)
    {S : Set (VorticitySpace × VorticitySpace)} (hS : MeasurableSet S) :
    (∫ p in {p : VorticityElement × VorticityElement | (p.1.1, p.2.1) ∈ S},
      |gaussSoftKernel 0 p.1 p.2| ∂((orientedFilamentMeasure κ γ).prod
        (orientedFilamentMeasure κ' η))) =
      |κ * κ'| * ∫ p in {p : ℝ × ℝ | (γ p.1, η p.2) ∈ S},
        |gaussKernel γ η p.1 p.2| ∂gaussMeasure := by
  let μ := volume.restrict (Icc (0 : ℝ) (2 * π))
  have hγ' := (continuous_signedTangent κ γ hγ).measurable
  have hη' := (continuous_signedTangent κ' η hη).measurable
  unfold orientedFilamentMeasure
  rw [setIntegral_abs_prod_orientedVorticityMeasure μ μ hγ.continuous.measurable hγ'
    hη.continuous.measurable hη' 0 hS, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by
    dsimp only
    rw [orientedFilament_integrand_eq, abs_mul])

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
