/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MolEnergySim06.MainResults.ChemicalPrecision

@[expose] public section

/-!
# Energy tolerance of a twenty-bit phase estimate

Equation (1) relates the phase used in the simulation to the energy.
A twenty-bit phase error can be propagated through that scale under a
positive evolution time, independently of errors in preparing the state.
-/

set_option autoImplicit false

open Qatlib.Papers.MolEnergySim06.MainResults

namespace Qatlib.Papers.MolEnergySim06.MainResults

/-- If a phase estimate is correct to twenty bits in the chosen phase
representative, the resulting energy error has the explicit time scaling. -/
theorem twenty_bit_energy_error_le (τ φ φhat : ℝ) (hτ : 0 < τ)
    (hphase : |φ - φhat| ≤ (1 / 2 : ℝ) ^ 20) :
    |energyOfPhase τ φ - energyOfPhase τ φhat| ≤
      2 * Real.pi / (1000000 * τ) := by
  have hwidth : (1 / 2 : ℝ) ^ 20 ≤ 1 / 1000000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr twenty_bit_resolution
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  calc
    _ ≤ 2 * Real.pi * (1 / 1000000) / τ :=
      energy_error_le τ φ φhat _ hτ (hphase.trans hwidth)
    _ = _ := by
      rw [mul_one_div, div_div]

end Qatlib.Papers.MolEnergySim06.MainResults
