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
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

def h2oPEAEnergy : ℚ := -84203663 / 1000000

def h2oDiagonalizationEnergy : ℚ := -84203665 / 1000000

def lihPEAEnergy : ℚ := -91228936 / 10000000

def lihDiagonalizationEnergy : ℚ := -91228934 / 10000000

def reportedAgreementTolerance : ℚ := 1 / 100000

def tenthKcalPerMolInAu : ℚ := 1 / 10 / 628

theorem h2o_error_exact :
    h2oPEAEnergy - h2oDiagonalizationEnergy = 2 / 1000000 := by
  unfold h2oPEAEnergy h2oDiagonalizationEnergy
  norm_num

theorem h2o_matches_diagonalization :
    |h2oPEAEnergy - h2oDiagonalizationEnergy| ≤ reportedAgreementTolerance := by
  rw [h2o_error_exact]
  unfold reportedAgreementTolerance
  norm_num

theorem lih_error_exact :
    lihPEAEnergy - lihDiagonalizationEnergy = -(2 / 10000000) := by
  unfold lihPEAEnergy lihDiagonalizationEnergy
  norm_num

theorem lih_matches_diagonalization :
    |lihPEAEnergy - lihDiagonalizationEnergy| ≤ reportedAgreementTolerance := by
  rw [lih_error_exact]
  unfold reportedAgreementTolerance
  norm_num

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

theorem reported_agreement_le_ten_microhartree :
    reportedAgreementTolerance = 1 / 100000 := rfl

theorem twenty_bit_resolution : (1 / 2 : ℚ) ^ 20 ≤ 1 / 1000000 := by
  norm_num

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

def energyOfPhase (τ φ : ℝ) : ℝ := 2 * Real.pi * φ / τ

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
