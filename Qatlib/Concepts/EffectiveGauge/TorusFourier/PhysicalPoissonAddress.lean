/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonValueExecution
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonTermError

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Poisson Address

Torus Fourier constructions for Effective Gauge.
Defines `rationalAddressMagnitude`, `physicalPoissonAddressAccuracy`, `rationalPhysicalPoissonAddress`.
Proves `rationalAddressMagnitude_nonneg`, `physicalPoissonAddressAccuracy_spec`, `physicalPoissonAddressAccuracy_budget`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rational Address Magnitude in the Torus Fourier construction. -/
def rationalAddressMagnitude (X : Fin 3 → ℚ) : ℚ := ∑ j : Fin 3, |X j|

/-- Definition of physical Poisson Address Accuracy in the Torus Fourier construction. -/
def physicalPoissonAddressAccuracy (C6 : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) : ℚ :=
  min 1 (tolerance/((156*|C6|+1)*(rationalAddressMagnitude X+1)))

/-- Definition of rational Physical Poisson Address in the Torus Fourier construction. -/
def rationalPhysicalPoissonAddress (X : Fin 3 → ℚ) (ell : ℚ) : Fin 3 → ℚ :=
  fun j => X j/fourierPeriodExecution ell

/-- Rational physical X is normalized using a new finite Machin period.
The requested accuracy depends only on saved data, X and tolerance. -/
def generalPoissonPhysicalPhaseValue (r : GeneralPoissonValueState) (X : Fin 3 → ℚ)
    (tolerance : ℚ) : ℚ :=
  let ell := physicalPoissonAddressAccuracy r.preparation.referenceCache.connectionBounds[6] X tolerance
  generalPoissonStateValue r (rationalPhysicalPoissonAddress X ell)-generalPoissonStateValue r 0

/-- Original `rationalAddressMagnitude_nonneg` guarantee for the `PhysicalPoissonAddress` construction; the complete source hypotheses are retained. -/
theorem rationalAddressMagnitude_nonneg (X : Fin 3 → ℚ) : 0 ≤ rationalAddressMagnitude X :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Original `physicalPoissonAddressAccuracy_spec` guarantee for the `PhysicalPoissonAddress` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonAddressAccuracy_spec (C6 : ℚ) (X : Fin 3 → ℚ)
    (tolerance : ℚ) (ht : 0<tolerance) :
    0<physicalPoissonAddressAccuracy C6 X tolerance ∧ physicalPoissonAddressAccuracy C6 X tolerance ≤ 1 := by
  have hS := rationalAddressMagnitude_nonneg X
  have hden : 0<(156*|C6|+1)*(rationalAddressMagnitude X+1) := by positivity
  exact ⟨lt_min (by norm_num) (div_pos ht hden),min_le_left _ _⟩

/-- Original `physicalPoissonAddressAccuracy_budget` guarantee for the `PhysicalPoissonAddress` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonAddressAccuracy_budget (C6 : ℚ) (X : Fin 3 → ℚ)
    (tolerance : ℚ) (ht : 0<tolerance) :
    (156*|C6|)*rationalAddressMagnitude X*physicalPoissonAddressAccuracy C6 X tolerance ≤ tolerance := by
  have hS := rationalAddressMagnitude_nonneg X
  have hD : 0 ≤ 156*|C6| := by positivity
  have hden : 0<(156*|C6|+1)*(rationalAddressMagnitude X+1) := by positivity
  have hbound := (le_div_iff₀ hden).mp
    (min_le_right (1 : ℚ) (tolerance/((156*|C6|+1)*(rationalAddressMagnitude X+1))))
  have hsmall : (156*|C6|)*rationalAddressMagnitude X ≤
      (156*|C6|+1)*(rationalAddressMagnitude X+1) := by nlinarith
  have hell := (physicalPoissonAddressAccuracy_spec C6 X tolerance ht).1.le
  have hmul := mul_le_mul_of_nonneg_right hsmall hell
  dsimp only [physicalPoissonAddressAccuracy] at hmul ⊢
  nlinarith

noncomputable section

/-- Original `rationalPhysicalPoissonAddress_error` guarantee for the `PhysicalPoissonAddress` construction; the complete source hypotheses are retained. -/
theorem rationalPhysicalPoissonAddress_error (C6 : ℚ) (X : Fin 3 → ℚ)
    (tolerance : ℚ) (ht : 0<tolerance) (j : Fin 3) :
    let ell := physicalPoissonAddressAccuracy C6 X tolerance
    |(rationalPhysicalPoissonAddress X ell j : ℝ)-
      (physicalPeriod⁻¹ • rationalSpatialPoint X) j| ≤ |(X j : ℝ)| * (ell : ℝ)/30 := by
  dsimp only
  let ell := physicalPoissonAddressAccuracy C6 X tolerance
  let length := fourierPeriodExecution ell
  have hell := physicalPoissonAddressAccuracy_spec C6 X tolerance ht
  have hl : (5 : ℝ)<length := fourierPeriodExecution_gt_five ell hell.1 hell.2
  have he := fourierPeriodExecution_error ell hell.1
  have hinv : |(length : ℝ)⁻¹-physicalPeriod⁻¹| ≤ (ell : ℝ)/30 := by
    have h := poissonPeriod_inverse_error (length : ℝ) (ell : ℝ) hl he
    simpa only [← Complex.ofReal_inv,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  change |(X j/length : ℚ)-physicalPeriod⁻¹*(X j : ℝ)| ≤ _
  rw [Rat.cast_div]
  rw [show (X j : ℝ)/(length : ℝ)-physicalPeriod⁻¹*(X j : ℝ)=
      (X j : ℝ)*((length : ℝ)⁻¹-physicalPeriod⁻¹) by ring,abs_mul]
  exact (mul_le_mul_of_nonneg_left hinv (abs_nonneg _)).trans_eq (by ring)

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
