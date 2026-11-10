/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedBellTeleportation
import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.SingletConventionBridgeTele
import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.TeleportGuessingDepolarizingTele
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.QuditTeleport.DepolarizingLaw
open Matrix

namespace Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport

theorem c001_resource_preparation_eqs1_3 :
    Normalized teleportBellResource ∧
      (∀ b c, teleportBellResource (b, c) =
        if b = c then ((Real.sqrt 2)⁻¹ : ℝ) else 0) ∧
      teleportPreparationGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      IsIsometry teleportInitialFrame ∧ IsIsometry teleportPreparedFrame ∧
      teleportPreparedFrame = teleportPreparationGate * teleportInitialFrame :=
  bell_resource_preparation_laws

theorem c001_bell_basis_branches_eq5 :
    teleportDecodeGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      (∀ o : Bool × Bool, teleportBranchKraus o = (1 / 2 : ℂ) •
        relabelGate boolEquivFin2
          ((if o.2 then PauliX else 1) * (if o.1 then PauliZ else 1))) :=
  bell_decoded_branch_operators

theorem c001_pauli_corrections_eq6 :
    ∀ o : Bool × Bool, teleportCorrection o ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      teleportCorrection o * teleportBranchKraus o = (1 / 2 : ℂ) • (1 : Operator 2) :=
  bell_pauli_corrections

theorem c001_perfect_teleportation_eqs5_6 :
    ∀ ρ : Operator 2,
      (∀ o, teleportCorrectedInstrument.branch o ρ = (1 / 4 : ℂ) • ρ ∧
        instrumentProb teleportCorrectedInstrument ρ o = (Matrix.trace ρ).re / 4) ∧
      teleportCorrectedInstrument.forget.map ρ = ρ :=
  bell_corrected_channel_and_mass

theorem c001_conditional_recovery_mixed :
    ∀ (ρ : Operator 2) (_hρ : IsDensityOperator ρ) (o : Bool × Bool),
      instrumentProb teleportCorrectedInstrument ρ o = 1 / 4 ∧
      (∀ h : 0 < instrumentProb teleportCorrectedInstrument ρ o,
        teleportCorrectedInstrument.conditionalState ρ o h = ρ) :=
  bell_conditional_recovery

theorem c001_two_bit_classical_message :
    (∀ o : Bool × Bool, (teleportMessage o).length = 2) ∧
      Function.Injective teleportMessage ∧ Fintype.card (Bool × Bool) = 4 :=
  bell_classical_message_cost

theorem c001_actual_program_branch_bridge :
    ∀ o : Bool × Bool, teleportActualBranchMap o = teleportCorrectedInstrument.branch o :=
  bell_actual_program_branch_bridge

theorem c001_entangled_reference_recovery :
    ∀ (R : ℕ) (ρ : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ) (o : Bool × Bool),
      tensorLeft (teleportActualBranchMap o) ρ = (1 / 4 : ℂ) • ρ ∧
      (∑ o : Bool × Bool, tensorLeft (teleportActualBranchMap o) ρ) = ρ :=
  bell_actual_program_reference_recovery

theorem c001_singlet_convention_eqs1_5_6 : SingletConventionBridge :=
  singletConventionBridge

theorem c001_guessing_depolarizing : TeleportGuessingDepolarizing :=
  teleportGuessingDepolarizing

theorem c001_guessing_state_maximally_mixed
    (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    (∑ o : Bool × Bool, conjBranch (teleportBranchKraus o) ρ) =
      (1 / 2 : ℂ) • (1 : Operator 2) := by
  rw [teleportGuessingDepolarizing.1 ρ, hρ.2]

end Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport
