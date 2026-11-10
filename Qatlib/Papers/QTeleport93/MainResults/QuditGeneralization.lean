/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Matrix

namespace Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization

theorem c002_resource_eq7 :
    ∀ (n : ℕ) [NeZero n],
      Normalized (quditResource n) ∧ IsIsometry (quditInitialFrame n) ∧
      (∀ b : ZMod n, quditX n b ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      (∀ a : ZMod n, quditZ n a ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      quditSUM n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ :=
  qudit_resource_and_weyl_access_laws

theorem c002_measurement_and_correction_eq8 :
    ∀ (n : ℕ) [NeZero n] (r : QuditTriple n) (j : Fin n),
      quditPreparedFrame n (quditRegisterEquiv n r) j =
        (if r.1.1 = j then quditResource n (r.1.2, r.2) else 0) ∧
      ∀ o : Fin n × Fin n,
        quditBranchKraus n o = (1 / (n : ℂ)) •
          (quditX n ((ZMod.finEquiv n) o.2) * quditZ n (-((ZMod.finEquiv n) o.1))) ∧
        quditCorrection n o * quditBranchKraus n o = (1 / (n : ℂ)) • (1 : Operator n) :=
  qudit_actual_resource_decoding_and_correction

theorem c002_actual_kraus_and_branch_eq8 :
    ∀ (n : ℕ) [NeZero n],
      (∑ o : Fin n × Fin n, (quditBranchKraus n o)ᴴ * quditBranchKraus n o) = 1 ∧
      (∑ o : Fin n × Fin n, (quditCorrection n o * quditBranchKraus n o)ᴴ *
        (quditCorrection n o * quditBranchKraus n o)) = 1 ∧
      ∀ (rho : Operator n) (o : Fin n × Fin n),
        quditActualBranchCore n o rho =
          conjBranch (quditCorrection n o * quditBranchKraus n o) rho ∧
        quditActualBranchCore n o rho = (1 / (n : ℂ) ^ 2) • rho :=
  qudit_actual_kraus_complete_and_branch_bridge

theorem c002_perfect_teleportation :
    ∀ (n : ℕ) [NeZero n],
      ∃ I : Instrument (Fin n × Fin n) n n,
        (∀ (rho : Operator n) (o : Fin n × Fin n),
          I.branch o rho = quditActualBranchCore n o rho) ∧
        (∀ rho : Operator n, I.forget.map rho = rho) ∧
        (∀ (rho : Operator n) (_hrho : IsDensityOperator rho) (o : Fin n × Fin n),
          instrumentProb I rho o = 1 / (n : ℝ) ^ 2 ∧
          ∀ hp : 0 < instrumentProb I rho o, I.conditionalState rho o hp = rho) :=
  qudit_actual_instrument_and_conditional_recovery

theorem c002_entangled_reference_recovery :
    ∀ (n R : ℕ) [NeZero n] (X : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ),
      (∀ o : Fin n × Fin n, quditActualReferenceCore n R o X = (1 / (n : ℂ) ^ 2) • X) ∧
      (∑ o : Fin n × Fin n, quditActualReferenceCore n R o X) = X :=
  qudit_actual_entangled_reference_recovery

theorem c002_fixed_width_message :
    ∀ (n k : ℕ) (_hwidth : n ≤ 2 ^ k),
      (∀ o : Fin n × Fin n,
        (quditMessage n k o).length = 2 * k ∧
          quditDecodeMessage n k (quditMessage n k o) = some o) ∧
      Function.Injective (quditMessage n k) ∧
      Fintype.card (Fin n × Fin n) = n * n ∧
      n ≤ 2 ^ (Nat.clog 2 n) :=
  qudit_actual_fixed_width_message

theorem c002_program_legality_and_counts :
    ∀ (n : ℕ) [NeZero n],
      observedWellFormed (quditProgram n) ∧
      observedLeafCount (quditProgram n) = n * n ∧
      observedKrausLeaves 1 (quditProgram n) =
        List.ofFn (fun k : Fin (n * n) =>
          quditProgramLeaf n ((quditOutcomeEquiv n).symm k)) ∧
      ∀ o : Fin n × Fin n,
        (quditProgramLeaf n o).accepted = true ∧
          (quditProgramLeaf n o).queries = 0 ∧
          (quditProgramLeaf n o).gates = 6 ∧
          (quditProgramLeaf n o).measurements = 1 ∧
          (quditProgramLeaf n o).outcomes =
            [(n * n, ((quditOutcomeEquiv n) o).val)] :=
  qudit_actual_program_legality_and_counts

theorem c002_qutrit_and_trivial_consumers :
    IsDensityOperator (relabelGate (quditOutcomeEquiv 3) (quditEntangledDensity 3)) ∧
    Matrix.traceLeft (quditEntangledDensity 3) = (1 / 3 : ℂ) • (1 : Operator 3) ∧
    conjBranch (quditBranchKraus 3 (0, 1))
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3))) ≠
      (1 / 9 : ℂ) • outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ∧
    (∑ o : Fin 3 × Fin 3,
      quditActualReferenceCore 3 3 o (quditEntangledDensity 3)) = quditEntangledDensity 3 ∧
    (∀ o : Fin 3 × Fin 3,
      quditDecodeMessage 3 2 (quditMessage 3 2 o) = some o) ∧
    (∀ rho : Operator 1, quditActualBranchCore 1 (0, 0) rho = rho) :=
  qudit_qutrit_entangled_and_trivial_consumers

end Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization
