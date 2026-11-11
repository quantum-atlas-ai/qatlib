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

/-!
# Qubit teleportation with explicit branches and reference recovery

The Bell resource, Bell-basis decoding, and Pauli corrections give four
corrected branches, each equal to one quarter of the input operator. Forgetting
the outcome recovers the identity channel, including on a qubit entangled with
an arbitrary finite reference. The outcome has a two-bit encoding. Additional
results relate the Bell and singlet conventions and describe the uncorrected
receiver's maximally mixed state.

The protocol is [BennettEtAl1993Teleportation]; see also
[Nielsen & Chuang, quantum teleportation][NielsenChuang2010].
-/
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

/-- The Bell resource is normalized with matching index amplitudes `1 / sqrt 2`, and the unitary
preparation gate carries the initial isometric frame to the prepared frame. -/
theorem c001_resource_preparation_eqs1_3 :
    Normalized teleportBellResource ∧
      (∀ b c, teleportBellResource (b, c) =
        if b = c then ((Real.sqrt 2)⁻¹ : ℝ) else 0) ∧
      teleportPreparationGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      IsIsometry teleportInitialFrame ∧ IsIsometry teleportPreparedFrame ∧
      teleportPreparedFrame = teleportPreparationGate * teleportInitialFrame :=
  bell_resource_preparation_laws

/-- The Bell decoding gate is unitary, and each branch Kraus operator is one half of the
relabeled Pauli product selected by the outcome bits. -/
theorem c001_bell_basis_branches_eq5 :
    teleportDecodeGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      (∀ o : Bool × Bool, teleportBranchKraus o = (1 / 2 : ℂ) •
        relabelGate boolEquivFin2
          ((if o.2 then PauliX else 1) * (if o.1 then PauliZ else 1))) :=
  bell_decoded_branch_operators

/-- Every prescribed Pauli correction is unitary and turns its Bell branch Kraus operator into
one half of the identity. -/
theorem c001_pauli_corrections_eq6 :
    ∀ o : Bool × Bool, teleportCorrection o ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      teleportCorrection o * teleportBranchKraus o = (1 / 2 : ℂ) • (1 : Operator 2) :=
  bell_pauli_corrections

/-- Every corrected branch is `ρ / 4`, and their sum is `ρ`, realizing the
teleportation protocol of [Bennett et al.][BennettEtAl1993Teleportation]. -/
theorem c001_perfect_teleportation_eqs5_6 :
    ∀ ρ : Operator 2,
      (∀ o, teleportCorrectedInstrument.branch o ρ = (1 / 4 : ℂ) • ρ ∧
        instrumentProb teleportCorrectedInstrument ρ o = (Matrix.trace ρ).re / 4) ∧
      teleportCorrectedInstrument.forget.map ρ = ρ :=
  bell_corrected_channel_and_mass

/-- For every qubit density operator, each corrected Bell outcome has probability one quarter
and its conditional state equals the input [BennettEtAl1993Teleportation]. -/
theorem c001_conditional_recovery_mixed :
    ∀ (ρ : Operator 2) (_hρ : IsDensityOperator ρ) (o : Bool × Bool),
      instrumentProb teleportCorrectedInstrument ρ o = 1 / 4 ∧
      (∀ h : 0 < instrumentProb teleportCorrectedInstrument ρ o,
        teleportCorrectedInstrument.conditionalState ρ o h = ρ) :=
  bell_conditional_recovery

/-- Each of the four Bell outcomes has an injective classical encoding of length two bits. -/
theorem c001_two_bit_classical_message :
    (∀ o : Bool × Bool, (teleportMessage o).length = 2) ∧
      Function.Injective teleportMessage ∧ Fintype.card (Bool × Bool) = 4 :=
  bell_classical_message_cost

/-- Each branch map of the actual qubit teleportation program equals the corresponding branch of
the corrected instrument. -/
theorem c001_actual_program_branch_bridge :
    ∀ o : Bool × Bool, teleportActualBranchMap o = teleportCorrectedInstrument.branch o :=
  bell_actual_program_branch_bridge

/-- Teleportation recovers the input even with an untouched finite reference;
each classical outcome contributes one quarter of the joint operator
[BennettEtAl1993Teleportation]. -/
theorem c001_entangled_reference_recovery :
    ∀ (R : ℕ) (ρ : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ) (o : Bool × Bool),
      tensorLeft (teleportActualBranchMap o) ρ = (1 / 4 : ℂ) • ρ ∧
      (∑ o : Bool × Bool, tensorLeft (teleportActualBranchMap o) ρ) = ρ :=
  bell_actual_program_reference_recovery

/-- Relates singlet convention branches to signed, relabeled Bell branches and shows that each
corrected singlet branch gives one quarter of the input [BennettEtAl1993Teleportation]. -/
theorem c001_singlet_convention_eqs1_5_6 : SingletConventionBridge :=
  singletConventionBridge

/-- Summing uncorrected teleportation branches gives the input trace times the maximally mixed
operator for both qubits and positive dimensional qudits. -/
theorem c001_guessing_depolarizing : TeleportGuessingDepolarizing :=
  teleportGuessingDepolarizing

/-- For every qubit density operator, summing the uncorrected Bell branches gives the maximally
mixed state `1 / 2` times the identity. -/
theorem c001_guessing_state_maximally_mixed
    (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    (∑ o : Bool × Bool, conjBranch (teleportBranchKraus o) ρ) =
      (1 / 2 : ℂ) • (1 : Operator 2) := by
  rw [teleportGuessingDepolarizing.1 ρ, hρ.2]

end Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport
