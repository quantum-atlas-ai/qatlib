/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.ThermalTrace
import Qatlib.Papers.ThermalRate98.MainResults.EvolutionInit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

theorem physical_flux_correlation_cyclic (β t ħ : ℝ) (H P : Matrix I I ℂ) :
    physicalFluxCorrelation β t ħ H P =
      Matrix.trace (physicalFlux ħ H P *
        (physicalBoltzmannHalf β H * (physicalPropagation t ħ H)ᴴ) *
        physicalFlux ħ H P *
        (physicalPropagation t ħ H * physicalBoltzmannHalf β H)) := by
  unfold physicalFluxCorrelation
  (try dsimp only)
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (physicalBoltzmannHalf β H)
      (physicalFlux ħ H P * physicalBoltzmannHalf β H * (physicalPropagation t ħ H)ᴴ *
        physicalFlux ħ H P * physicalPropagation t ħ H))

theorem physical_boltzmann_mul_propagation_adjoint (β t ħ : ℝ) (H : Matrix I I ℂ)
    (hH : H.IsHermitian) :
    physicalBoltzmannHalf β H * (physicalPropagation t ħ H)ᴴ =
      NormedSpace.exp ((Complex.I * ((t/ħ : ℝ) : ℂ) - (β : ℂ)/2) • H) := by
  rw [physicalPropagation_adjoint t ħ H hH]
  unfold physicalBoltzmannHalf
  have hc : Commute ((-((β : ℂ)/2)) • H)
      ((Complex.I * ((t/ħ : ℝ) : ℂ)) • H) :=
    ((Commute.refl H).smul_right (Complex.I * ((t/ħ : ℝ) : ℂ))).smul_left (-((β : ℂ)/2))
  rw [← Matrix.exp_add_of_commute _ _ hc]
  congr 1
  rw [← add_smul]
  congr 1
  ring

theorem physical_propagation_mul_boltzmann (β t ħ : ℝ) (H : Matrix I I ℂ) :
    physicalPropagation t ħ H * physicalBoltzmannHalf β H =
      NormedSpace.exp ((-Complex.I * ((t/ħ : ℝ) : ℂ) - (β : ℂ)/2) • H) := by
  unfold physicalPropagation physicalBoltzmannHalf
  have hc : Commute ((-Complex.I * ((t/ħ : ℝ) : ℂ)) • H) ((-((β : ℂ)/2)) • H) :=
    ((Commute.refl H).smul_right (-((β : ℂ)/2))).smul_left (-Complex.I * ((t/ħ : ℝ) : ℂ))
  rw [← Matrix.exp_add_of_commute _ _ hc]
  congr 1
  rw [← add_smul]
  congr 1

theorem physical_flux_correlation_complex_time (β t ħ : ℝ) (H P : Matrix I I ℂ)
    (hH : H.IsHermitian) :
    physicalFluxCorrelation β t ħ H P =
      Matrix.trace (physicalFlux ħ H P *
        NormedSpace.exp ((Complex.I * ((t/ħ : ℝ) : ℂ) - (β : ℂ)/2) • H) *
        physicalFlux ħ H P *
        NormedSpace.exp ((-Complex.I * ((t/ħ : ℝ) : ℂ) - (β : ℂ)/2) • H)) := by
  rw [physical_flux_correlation_cyclic,
    physical_boltzmann_mul_propagation_adjoint β t ħ H hH,
    physical_propagation_mul_boltzmann β t ħ H]

end Qatlib.Papers.ThermalRate98.MainResults
