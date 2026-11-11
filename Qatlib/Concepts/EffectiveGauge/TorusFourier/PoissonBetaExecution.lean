/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierCoefficientList
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Beta Execution

Torus Fourier constructions for Effective Gauge.
Defines `rationalFrequencyEnergy`, `rationalPoissonBeta`, `rationalPoissonBetaList`.
Proves `rationalFrequencyEnergy_cast`, `rationalPoissonBeta_zero`, `complexPoissonBeta_zero`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rational Frequency Energy in the Torus Fourier construction. -/
def rationalFrequencyEnergy (k : SpatialFrequency) : ℚ := ∑ j : Fin 3, (k j : ℚ)^2

/-- The inverse L factor is applied at value evaluation, not in beta.
The zero frequency is totalized by rational division by zero to beta=0. -/
def rationalPoissonBeta (k : SpatialFrequency) (coefficient : Fin 3 → RationalCircleSample) : RationalCircleSample :=
  (-(∑ j : Fin 3, (k j : ℚ)*(coefficient j).2)/rationalFrequencyEnergy k,
    (∑ j : Fin 3, (k j : ℚ)*(coefficient j).1)/rationalFrequencyEnergy k)

/-- Definition of rational Poisson Beta List in the Torus Fourier construction. -/
def rationalPoissonBetaList (coefficients : RationalFourierCoefficientList) :
    List (SpatialFrequency × RationalCircleSample) :=
  coefficients.map (fun record => (record.1,rationalPoissonBeta record.1 record.2))

noncomputable section

/-- Definition of complex Poisson Beta in the Torus Fourier construction. -/
def complexPoissonBeta (a : Fin 3 → SpatialFrequency → ℂ) (k : SpatialFrequency) : ℂ :=
  (physicalPeriod : ℂ)*unitPoissonCoefficient a k

/-- Original `rationalFrequencyEnergy_cast` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem rationalFrequencyEnergy_cast (k : SpatialFrequency) :
    (rationalFrequencyEnergy k : ℝ)=frequencyEnergy k := by
  simp only [rationalFrequencyEnergy,frequencyEnergy,Rat.cast_sum,Rat.cast_pow,Rat.cast_intCast]

/-- Original `rationalPoissonBeta_zero` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonBeta_zero (coefficient : Fin 3 → RationalCircleSample) :
    rationalPoissonBeta 0 coefficient=(0,0) := by
  simp [rationalPoissonBeta,rationalFrequencyEnergy]

/-- Original `complexPoissonBeta_zero` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem complexPoissonBeta_zero (a : Fin 3 → SpatialFrequency → ℂ) : complexPoissonBeta a 0=0 := by
  simp only [complexPoissonBeta,unitPoissonCoefficient_zero,mul_zero]

/-- Original `complexPoissonBeta_eq` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem complexPoissonBeta_eq (a : Fin 3 → SpatialFrequency → ℂ) (k : SpatialFrequency) :
    complexPoissonBeta a k=Complex.I*(∑ j : Fin 3, (k j : ℂ)*a j k)/(frequencyEnergy k : ℂ) := by
  have hL : (physicalPeriod : ℂ)≠0 := by exact_mod_cast physicalPeriod_pos.ne'
  simp only [complexPoissonBeta,unitPoissonCoefficient,div_eq_mul_inv,mul_inv_rev]
  calc
    _ = ((physicalPeriod : ℂ)*(physicalPeriod : ℂ)⁻¹)*
        (Complex.I*(∑ j : Fin 3, (k j : ℂ)*a j k)*(frequencyEnergy k : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hL,one_mul]

/-- Original `rationalPoissonBeta_cast` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonBeta_cast (k : SpatialFrequency) (coefficient : Fin 3 → RationalCircleSample) :
    rationalCircleCast (rationalPoissonBeta k coefficient)=
      complexPoissonBeta (fun j _ => rationalCircleCast (coefficient j)) k := by
  rw [complexPoissonBeta_eq,Complex.div_ofReal]
  apply Complex.ext <;> simp [rationalPoissonBeta,rationalFrequencyEnergy,rationalCircleCast,frequencyEnergy]

/-- Original `complexPoissonBeta_sub` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem complexPoissonBeta_sub (a b : Fin 3 → SpatialFrequency → ℂ) (k : SpatialFrequency) :
    complexPoissonBeta a k-complexPoissonBeta b k=complexPoissonBeta (fun j l => a j l-b j l) k := by
  simp only [complexPoissonBeta,unitPoissonCoefficient,mul_sub,Finset.sum_sub_distrib,sub_div]

/-- Original `complexPoissonBeta_norm_le` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem complexPoissonBeta_norm_le (a : Fin 3 → SpatialFrequency → ℂ) (k : SpatialFrequency)
    (B : ℝ) (hb : ∀ j, ‖a j k‖ ≤ B) : ‖complexPoissonBeta a k‖ ≤ 3*B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  by_cases hk : k=0
  · subst k
    rw [complexPoissonBeta_zero,norm_zero]
    positivity
  · have hr : (0 : ℝ)<frequencyRadius k := Nat.cast_pos.mpr (frequencyRadius_pos k hk)
    have hr1 : (1 : ℝ) ≤ frequencyRadius k := by
      exact_mod_cast (Nat.succ_le_iff.mpr (frequencyRadius_pos k hk))
    calc
      _ = physicalPeriod*‖unitPoissonCoefficient a k‖ := by
        rw [complexPoissonBeta,norm_mul,Complex.norm_real,Real.norm_of_nonneg physicalPeriod_pos.le]
      _ ≤ physicalPeriod*(3*B/(physicalPeriod*(frequencyRadius k : ℝ))) :=
        mul_le_mul_of_nonneg_left (unitPoissonCoefficient_norm_le a k hk B hb) physicalPeriod_pos.le
      _ = 3*B/(frequencyRadius k : ℝ) := by field_simp [physicalPeriod_pos.ne',hr.ne']
      _ ≤ 3*B := by
        apply (div_le_iff₀ hr).mpr
        nlinarith [mul_nonneg hB (sub_nonneg.mpr hr1)]

/-- Original `complexPoissonBeta_sub_norm_le` guarantee for the `PoissonBetaExecution` construction; the complete source hypotheses are retained. -/
theorem complexPoissonBeta_sub_norm_le (a b : Fin 3 → SpatialFrequency → ℂ)
    (k : SpatialFrequency) (E : ℝ) (he : ∀ j, ‖a j k-b j k‖ ≤ E) :
    ‖complexPoissonBeta a k-complexPoissonBeta b k‖ ≤ 3*E := by
  rw [complexPoissonBeta_sub]
  exact complexPoissonBeta_norm_le (fun j l => a j l-b j l) k E he

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
