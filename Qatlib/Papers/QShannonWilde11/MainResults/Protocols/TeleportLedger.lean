/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel
public import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedBellTeleportation

@[expose] public section


/-!
# Qubit teleportation ledger: branch recovery, classical message, shared e-bit

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Ch. 6, §6.2 (teleportation), fixed PDF
pp. 208–217.
<https://arxiv.org/abs/1106.1445>

§6.2 teleports an unknown qubit with one pre-shared Bell pair and two classical bits: Alice
measures in the Bell basis, sends her two-bit outcome, and Bob applies the matching Pauli
correction.  The counted circuit of
`Qatlib.Concepts.QuditTeleport.TeleportCore` already supplies the branch and message
identities, and this file assembles them into one ledger statement in the paper model:

* every corrected branch succeeds with probability `1/4` and reproduces its input exactly
  (`bell_conditional_recovery`);
* each counted circuit branch is the corresponding corrected instrument branch
  (`bell_actual_program_branch_bridge`);
* Alice's message is an injective two-bit encoding of the four outcomes
  (`bell_classical_message_cost`).

The e-bit count is recorded as the paper-side constant `teleportEbits`.  The library has no
resource ledger for pre-shared entanglement (`LoccBits` counts classical message bits only),
so the single e-bit is a convention attached to the shared Bell resource, not a computed
consumption.  Nothing here models noise, and no operational coding statement is derived.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QShannonWilde11.MainResults.Protocols

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Papers.QShannonWilde11.MainResults.Model

noncomputable section

/-- Pre-shared entanglement used by the qubit teleportation protocol of §6.2, in e-bits: one
Bell pair, so one e-bit.  The library's `Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits`
charges classical message bits only, hence the ledger is kept here. -/
def teleportEbits : ℕ := 1

/-- The teleportation ledger records one e-bit of pre-shared entanglement. -/
theorem teleportEbits_eq_one : teleportEbits = 1 := rfl

/-- With a pure qubit input, every one of the four corrected Bell branches occurs with
probability `1/4` and its conditional state is exactly the input, [Wilde2017], §6.2. -/
theorem qubit_teleport_pure_input_recovery (ψ : QState (Fin 2)) (hψ : Normalized ψ)
    (o : Bool × Bool) :
    instrumentProb teleportCorrectedInstrument (outerProduct ψ) o = 1 / 4 ∧
      (∀ h : 0 < instrumentProb teleportCorrectedInstrument (outerProduct ψ) o,
        teleportCorrectedInstrument.conditionalState (outerProduct ψ) o h = outerProduct ψ) :=
  bell_conditional_recovery (outerProduct ψ) (isDensityOperator_outerProduct hψ) o

/-- The same recovery statement for an arbitrary qubit density operator of the paper model
`Qatlib.Papers.QShannonWilde11.MainResults.Model.Dens (Fin 2)`. -/
theorem qubit_teleport_density_recovery (ρ : Dens (Fin 2)) (o : Bool × Bool) :
    instrumentProb teleportCorrectedInstrument ρ.val o = 1 / 4 ∧
      (∀ h : 0 < instrumentProb teleportCorrectedInstrument ρ.val o,
        teleportCorrectedInstrument.conditionalState ρ.val o h = ρ.val) :=
  bell_conditional_recovery ρ.val ⟨ρ.2.1, ρ.2.2⟩ o

/-- The §6.2 ledger for a pure input: four equiprobable recovering branches, agreement of the
counted circuit branches with the corrected instrument, an injective two-bit outcome message,
and one e-bit of pre-shared entanglement. -/
theorem qubit_teleport_pure_input_ledger (ψ : QState (Fin 2)) (hψ : Normalized ψ) :
    (∀ o : Bool × Bool,
        instrumentProb teleportCorrectedInstrument (outerProduct ψ) o = 1 / 4) ∧
      (∀ o : Bool × Bool,
        teleportActualBranchMap o = teleportCorrectedInstrument.branch o) ∧
      (∀ o : Bool × Bool, (teleportMessage o).length = 2) ∧
      Function.Injective teleportMessage ∧
      Fintype.card (Bool × Bool) = 4 ∧
      teleportEbits = 1 :=
  ⟨fun o => (qubit_teleport_pure_input_recovery ψ hψ o).1,
    fun o => bell_actual_program_branch_bridge o,
    bell_classical_message_cost.1,
    bell_classical_message_cost.2.1,
    bell_classical_message_cost.2.2,
    teleportEbits_eq_one⟩

end

end Qatlib.Papers.QShannonWilde11.MainResults.Protocols
