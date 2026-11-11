/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Papers.MolEnergySim06.MainResults.ResourceScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reported molecular energies and phase precision

This module stores rational energy values and comparison scales for the water and
lithium-hydride examples of [AspuruGuzikEtAl2005]. Exact arithmetic verifies their reported
discrepancies, agreement tolerance, and compact-register sizes.

`energyOfPhase` converts phase to energy using a positive time parameter. The accompanying error
estimate propagates a phase tolerance, while `exact_grid_readout_probability` gives unit
probability for an exactly representable eigenphase in the stated phase-estimation circuit.

## Main statements

* `reported_errors_below_reaction_scale`: Both stored energy discrepancies are below the
  specified reaction-energy scale.
* `energy_error_le`: Propagate a phase error through the phase-to-energy conversion.
* `exact_grid_readout_probability`: An exact grid eigenphase is read out with probability one.

## References

* [Aspuru-Guzik et al., 2005][AspuruGuzikEtAl2005]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

/-- The stored water phase-estimation energy `-84.203663` in atomic units, represented as a
rational number. -/
def h2oPEAEnergy : ℚ := -84203663 / 1000000

/-- The stored water diagonalization energy `-84.203665` in atomic units, represented as a
rational number. -/
def h2oDiagonalizationEnergy : ℚ := -84203665 / 1000000

/-- The stored lithium-hydride phase-estimation energy `-9.1228936` in atomic units, represented
as a rational number. -/
def lihPEAEnergy : ℚ := -91228936 / 10000000

/-- The stored lithium-hydride diagonalization energy `-9.1228934` in atomic units, represented
as a rational number. -/
def lihDiagonalizationEnergy : ℚ := -91228934 / 10000000

/-- The rational agreement tolerance `1 / 100000` in atomic units. -/
def reportedAgreementTolerance : ℚ := 1 / 100000

/-- The rational comparison scale `1 / (10 * 628)` in atomic units for one tenth of a
kilocalorie per mole. -/
def tenthKcalPerMolInAu : ℚ := 1 / 10 / 628

/-- The stored water phase-estimation energy exceeds the stored diagonalization energy by
exactly `2 / 1000000`. -/
theorem h2o_error_exact :
    h2oPEAEnergy - h2oDiagonalizationEnergy = 2 / 1000000 := by
  unfold h2oPEAEnergy h2oDiagonalizationEnergy
  norm_num

/-- The absolute discrepancy between the two stored water energies is at most
`reportedAgreementTolerance`; see [AspuruGuzikEtAl2005]. -/
theorem h2o_matches_diagonalization :
    |h2oPEAEnergy - h2oDiagonalizationEnergy| ≤ reportedAgreementTolerance := by
  rw [h2o_error_exact]
  unfold reportedAgreementTolerance
  norm_num

/-- The stored lithium-hydride phase-estimation energy minus the stored diagonalization energy
is exactly `-2 / 10000000`. -/
theorem lih_error_exact :
    lihPEAEnergy - lihDiagonalizationEnergy = -(2 / 10000000) := by
  unfold lihPEAEnergy lihDiagonalizationEnergy
  norm_num

/-- The absolute discrepancy between the two stored lithium-hydride energies is at most
`reportedAgreementTolerance`; see [AspuruGuzikEtAl2005]. -/
theorem lih_matches_diagonalization :
    |lihPEAEnergy - lihDiagonalizationEnergy| ≤ reportedAgreementTolerance := by
  rw [lih_error_exact]
  unfold reportedAgreementTolerance
  norm_num

/-- Both stored molecular energy discrepancies are strictly below `tenthKcalPerMolInAu`; see
[AspuruGuzikEtAl2005]. -/
theorem reported_errors_below_reaction_scale :
    |h2oPEAEnergy - h2oDiagonalizationEnergy| < tenthKcalPerMolInAu ∧
    |lihPEAEnergy - lihDiagonalizationEnergy| < tenthKcalPerMolInAu := by
  constructor
  · rw [h2o_error_exact]
    unfold tenthKcalPerMolInAu
    norm_num
  · rw [lih_error_exact]
    unfold tenthKcalPerMolInAu
    norm_num

/-- The stored agreement tolerance equals `1 / 100000` atomic units. -/
theorem reported_agreement_le_ten_microhartree :
    reportedAgreementTolerance = 1 / 100000 := rfl

/-- The rational phase width `2^(-20)` is at most one millionth. -/
theorem twenty_bit_resolution : (1 / 2 : ℚ) ^ 20 ≤ 1 / 1000000 := by
  norm_num

/-- The compact encoding of 196 configurations requires eight qubits according to
`compactQubits`; see [AspuruGuzikEtAl2005]. -/
theorem compactQubits_196 : compactQubits 196 = 8 := by
  have hle : compactQubits 196 ≤ 8 :=
    Nat.clog_le_of_le_pow (by norm_num : 196 ≤ 2 ^ 8)
  have hge : 8 ≤ compactQubits 196 := by
    have h7 : 7 < compactQubits 196 := by
      unfold compactQubits
      exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
        (by norm_num : 2 ^ 7 < 196)
    exact Nat.succ_le_iff.mpr h7
  exact le_antisymm hle hge

/-- The compact encoding of 1210 configurations requires eleven qubits according to
`compactQubits`; see [AspuruGuzikEtAl2005]. -/
theorem compactQubits_1210 : compactQubits 1210 = 11 := by
  have hle : compactQubits 1210 ≤ 11 :=
    Nat.clog_le_of_le_pow (by norm_num : 1210 ≤ 2 ^ 11)
  have hge : 11 ≤ compactQubits 1210 := by
    have h10 : 10 < compactQubits 1210 := by
      unfold compactQubits
      exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
        (by norm_num : 2 ^ 10 < 1210)
    exact Nat.succ_le_iff.mpr h10
  exact le_antisymm hle hge

/-- Convert phase `φ` to energy by the formula `2 * Real.pi * φ / τ`. -/
def energyOfPhase (τ φ : ℝ) : ℝ := 2 * Real.pi * φ / τ

/-- For positive `τ`, a phase discrepancy at most `ε` gives an energy discrepancy at most `2 *
Real.pi * ε / τ`; see [AspuruGuzikEtAl2005]. -/
theorem energy_error_le (τ φ φ' ε : ℝ) (hτ : 0 < τ) (h : |φ - φ'| ≤ ε) :
    |energyOfPhase τ φ - energyOfPhase τ φ'| ≤ 2 * Real.pi * ε / τ := by
  have hτ' : τ ≠ 0 := hτ.ne'
  have hcoef : (0 : ℝ) < 2 * Real.pi / τ := by positivity
  have hEq : energyOfPhase τ φ - energyOfPhase τ φ' =
      (2 * Real.pi / τ) * (φ - φ') := by
    unfold energyOfPhase
    field_simp [hτ']
  rw [hEq, abs_mul, abs_of_pos hcoef]
  calc
    (2 * Real.pi / τ) * |φ - φ'| ≤ (2 * Real.pi / τ) * ε :=
      mul_le_mul_of_nonneg_left h hcoef.le
    _ = 2 * Real.pi * ε / τ := by ring

/-- For a normalized eigenstate with eigenphase exactly indexed by `j : Fin (2^t)`, the stated
controlled-power and inverse-Fourier circuit measures `j` with probability one; see
[AspuruGuzikEtAl2005]. -/
theorem exact_grid_readout_probability (t : ℕ) {I : Type*} [Fintype I]
    [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (hψn : Normalized ψ)
    (j : Fin (2 ^ t))
    (hψ : U *ᵥ ψ = (primRoot (2 ^ t) ^ ((j.val : ℤ))) • ψ) :
    MeasureProb
        (ApplyGate (TensorGate (QFTMatrix (2 ^ t))ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U (2 ^ t) *ᵥ
            TensorState (fun _ : Fin (2 ^ t) =>
              (Real.sqrt ((2 ^ t : ℕ) : ℝ) : ℂ)⁻¹) ψ))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1 := by
  exact (qpe_exact_readout (by positivity) hψn j hψ).2

end Qatlib.Papers.MolEnergySim06.MainResults
