/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformQmaAmplificationDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompleteness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.LocalMachine.LocalTransport

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib
open Matrix

def MwWitnessPreserving (p : WitnessVerifierProgram)
    (M : Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ) : Prop :=
  ∀ u u', M u u' ≠ 0 → M u u' = M u u

def MwTwoProjectionsOrthogonal (p : WitnessVerifierProgram) : Prop :=
  (∀ u : Reg (programQubits p),
    mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0) ∧
  (∀ u u' : Reg (programQubits p), u ≠ u' → mwGoodProjector p u u' = 0)

def MwFailureRate (k : ℕ) : ℕ := k

def qmaIsDyadicC (width : ℕ) (z : ℂ) : Prop :=
  ∃ a c : ℤ, (2 : ℂ) ^ width * z = (a : ℂ) + Complex.I * (c : ℂ)

def qmaClause2Bits (C : QmaHistoryCircuit) : ℕ :=
  3 * (C.qubits + C.gates.length) + 64

noncomputable def qmaClause2YesBound (C : QmaHistoryCircuit) (a : ℝ) : ℝ :=
  (1 - a) / (C.gates.length + 1) + qmaTiny (C.qubits + C.gates.length + 2)

noncomputable def qmaClause2NoBound (C : QmaHistoryCircuit) (ε : ℝ) : ℝ :=
  (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
    - qmaTiny (C.qubits + C.gates.length + 2)

def qmaClause2TwoWay (C : QmaHistoryCircuit) : Prop :=
  (∀ a : ℝ,
      (∃ φ : QState (Reg C.qubits), QmaInitLegal C φ ∧ Normalized φ ∧
        a ≤ qmaHistoryAcceptProb C φ) →
      ∃ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η ∧
        qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C))) η
          ≤ qmaClause2YesBound C a)
  ∧ (∀ ε : ℝ,
      (∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
        qmaHistoryAcceptProb C φ ≤ ε) →
      ∀ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η →
        qmaClause2NoBound C ε
          ≤ qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C))) η)
  ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C)),
      qmaActsOn C.qubits C.gates.length t.matrix t.clockSupport t.workSupport
        ∧ t.clockSupport.card ≤ 2 ∧ t.workSupport.card ≤ 2)
  ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C)),
      ∀ p q : Fin (C.gates.length + 1) × Reg C.qubits, ‖t.matrix p q‖ ≤ 1)
  ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C)),
      ∀ p q : Fin (C.gates.length + 1) × Reg C.qubits,
        qmaIsDyadicC (qmaClause2Bits C + 1) (t.matrix p q))
  ∧ (qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C))).length
      ≤ C.gates.length + C.qubits + 1

def qmaClause3GammaBits (v : ℕ) : List Bool := List.replicate v true ++ [false]

def qmaClause3NatBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: qmaClause3NatBits w (v / 2)

def qmaClause3EncNat (v : ℕ) : List Bool :=
  qmaClause3GammaBits (v.log2 + 1) ++ qmaClause3NatBits (v.log2 + 1) v

def qmaClause3EncList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  qmaClause3GammaBits xs.length ++ (xs.map f).flatten

def qmaClause3EncInt (v : ℤ) : List Bool := decide (0 ≤ v) :: qmaClause3EncNat v.natAbs

def qmaClause3TermEntries {N : ℕ} (t : LhTerm N) : List ℤ :=
  (lhIndexPairs (2 ^ t.wires.length)).map (fun q => t.re q.1 q.2)
    ++ (lhIndexPairs (2 ^ t.wires.length)).map (fun q => t.im q.1 q.2)

def qmaClause3EncTerm {N : ℕ} (t : LhTerm N) : List Bool :=
  qmaClause3EncNat t.wires.length
    ++ qmaClause3EncList (fun j => qmaClause3EncNat j.val) t.wires
    ++ qmaClause3EncList qmaClause3EncInt (qmaClause3TermEntries t)

def qmaClause3ToBits (E : LhEncoding) : List Bool :=
  qmaClause3EncNat E.qubitCount ++ qmaClause3EncNat E.width
    ++ qmaClause3EncList (fun t : LhTerm E.qubitCount => qmaClause3EncTerm t) E.terms

def qmaClause3YesBound (_E : LhEncoding) : ℝ := 0

noncomputable def qmaClause3NoBound (E : LhEncoding) : ℝ :=
  1 / (2 ^ 20 * (E.qubitCount + 1) ^ 4)

def qmaClause3YesBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, qmaClause3ToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhYesInst E (qmaClause3YesBound E)

def qmaClause3NoBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, qmaClause3ToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhNoInst E (qmaClause3NoBound E)

def qmaClause3AuxWires (V : QmaVerifier) (x : List Bool) :
    Finset (Fin (qmaRegisterSize V x.length)) :=
  Finset.univ.filter fun j =>
    V.witnessQubits x.length ≤ j.val
      ∧ j.val < V.witnessQubits x.length + V.auxQubits x.length

def qmaClause3OutWire (V : QmaVerifier) (x : List Bool) : Fin (qmaRegisterSize V x.length) :=
  ⟨V.witnessQubits x.length + V.auxQubits x.length, by
    show V.witnessQubits x.length + V.auxQubits x.length
      < V.witnessQubits x.length + V.auxQubits x.length + 1
    omega⟩

def qmaClause3VerifierCircuit (V : QmaVerifier) (x : List Bool) : QmaHistoryCircuit where
  qubits := qmaRegisterSize V x.length
  gates := V.program x
  legal := V.legal x
  initZeroWires := qmaClause3AuxWires V x ∪ {qmaClause3OutWire V x}
  outputWire := qmaClause3OutWire V x

end Qatlib.Concepts.QmaCompleteness.HistoryHam
