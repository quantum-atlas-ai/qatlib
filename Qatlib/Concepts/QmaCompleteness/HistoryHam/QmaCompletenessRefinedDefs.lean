/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformQmaAmplificationDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompleteness

/-!
# Refined QMA completeness predicates and encodings

This module defines `qmaClause2TwoWay`, which packages energy bounds, declared supports, entry
bounds, complex dyadic precision, and term counts for rounded history Hamiltonians. The
construction follows the circuit-to-Hamiltonian framework of [KempeKitaevRegev2006]. The
predicate `qmaIsDyadicC` allows integer numerators in both complex components.

It also defines the serialization `qmaClause3ToBits`, with length prefixes for natural numbers
and lists, and the associated local Hamiltonian promise predicates. `qmaClause3VerifierCircuit`
supplies a history circuit from a verifier, while `MwWitnessPreserving` and
`MwTwoProjectionsOrthogonal` formulate matrix conditions used in the amplification analysis
related to [MarriottWatrous2005].

## Main definitions

* `qmaClause2TwoWay`: the combined specification for a rounded history Hamiltonian.
* `qmaClause3ToBits`: serialization of local Hamiltonian descriptions with length prefixes.
* `qmaClause3YesBits` and `qmaClause3NoBits`: the corresponding energy promise predicates.
* `qmaClause3VerifierCircuit`: the verifier circuit with initialized ancilla and output wires.

## References

* [Kempe, Kitaev and Regev, 2006][KempeKitaevRegev2006]
* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

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

/-- Requires every nonzero entry `M u u'` to equal the diagonal entry `M u u` in the same row. -/
def MwWitnessPreserving (p : WitnessVerifierProgram)
    (M : Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ) : Prop :=
  ∀ u u', M u u' ≠ 0 → M u u' = M u u

/-- Requires `mwGoodProjector p` to be diagonal with diagonal equal to the indicator of
`programOutputEvent p`. -/
def MwTwoProjectionsOrthogonal (p : WitnessVerifierProgram) : Prop :=
  (∀ u : Reg (programQubits p),
    mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0) ∧
  (∀ u u' : Reg (programQubits p), u ≠ u' → mwGoodProjector p u u' = 0)

/-- The natural-number failure-rate parameter, defined to equal `k`. -/
def MwFailureRate (k : ℕ) : ℕ := k

/-- Requires multiplication by `2^width` to express `z` as a Gaussian integer. -/
def qmaIsDyadicC (width : ℕ) (z : ℂ) : Prop :=
  ∃ a c : ℤ, (2 : ℂ) ^ width * z = (a : ℂ) + Complex.I * (c : ℂ)

/-- The rounding precision `3 * (C.qubits + C.gates.length) + 64` used for the refined history
Hamiltonian. -/
def qmaClause2Bits (C : QmaHistoryCircuit) : ℕ :=
  3 * (C.qubits + C.gates.length) + 64

/-- The YES energy bound `(1 - a) / (C.gates.length + 1)` plus the prescribed rounding error. -/
noncomputable def qmaClause2YesBound (C : QmaHistoryCircuit) (a : ℝ) : ℝ :=
  (1 - a) / (C.gates.length + 1) + qmaTiny (C.qubits + C.gates.length + 2)

/-- The NO energy bound `(1 - 2 * ε) / (2^10 * (C.gates.length + 1)^3)` minus the prescribed
rounding error. -/
noncomputable def qmaClause2NoBound (C : QmaHistoryCircuit) (ε : ℝ) : ℝ :=
  (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
    - qmaTiny (C.qubits + C.gates.length + 2)

/-- The conjunction of YES and NO variational energy bounds, support and entry bounds, complex
dyadic precision, and a term-count bound for the rounded history Hamiltonian. -/
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

/-- The unary length prefix consisting of `v` true bits followed by one false bit. -/
def qmaClause3GammaBits (v : ℕ) : List Bool := List.replicate v true ++ [false]

/-- The low bits of a natural number, emitted recursively from least to most significant for the
requested width. -/
def qmaClause3NatBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: qmaClause3NatBits w (v / 2)

/-- Encodes a natural number with a unary prefix for `v.log2 + 1` followed by that many binary
digits. -/
def qmaClause3EncNat (v : ℕ) : List Bool :=
  qmaClause3GammaBits (v.log2 + 1) ++ qmaClause3NatBits (v.log2 + 1) v

/-- Encodes a list by a unary length prefix followed by the concatenated encodings of its
elements. -/
def qmaClause3EncList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  qmaClause3GammaBits xs.length ++ (xs.map f).flatten

/-- Encodes an integer by its nonnegativity bit and the length-prefixed natural encoding of its
absolute value. -/
def qmaClause3EncInt (v : ℤ) : List Bool := decide (0 ≤ v) :: qmaClause3EncNat v.natAbs

/-- Lists all real numerator entries of a local term, followed by all imaginary numerator
entries, in `lhIndexPairs` order. -/
def qmaClause3TermEntries {N : ℕ} (t : LhTerm N) : List ℤ :=
  (lhIndexPairs (2 ^ t.wires.length)).map (fun q => t.re q.1 q.2)
    ++ (lhIndexPairs (2 ^ t.wires.length)).map (fun q => t.im q.1 q.2)

/-- Encodes a local term's wire count, length-prefixed wire list, and length-prefixed integer
entry list. -/
def qmaClause3EncTerm {N : ℕ} (t : LhTerm N) : List Bool :=
  qmaClause3EncNat t.wires.length
    ++ qmaClause3EncList (fun j => qmaClause3EncNat j.val) t.wires
    ++ qmaClause3EncList qmaClause3EncInt (qmaClause3TermEntries t)

/-- Encodes the qubit count, dyadic precision, and length-prefixed list of local Hamiltonian
terms. -/
def qmaClause3ToBits (E : LhEncoding) : List Bool :=
  qmaClause3EncNat E.qubitCount ++ qmaClause3EncNat E.width
    ++ qmaClause3EncList (fun t : LhTerm E.qubitCount => qmaClause3EncTerm t) E.terms

/-- The zero energy threshold for the refined local Hamiltonian YES predicate. -/
def qmaClause3YesBound (_E : LhEncoding) : ℝ := 0

/-- The positive NO energy threshold `1 / (2^20 * (E.qubitCount + 1)^4)`. -/
noncomputable def qmaClause3NoBound (E : LhEncoding) : ℝ :=
  1 / (2 ^ 20 * (E.qubitCount + 1) ^ 4)

/-- Bit strings serialized by `qmaClause3ToBits` from Hermitian `k`-local instances satisfying
the refined YES energy bound. -/
def qmaClause3YesBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, qmaClause3ToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhYesInst E (qmaClause3YesBound E)

/-- Bit strings serialized by `qmaClause3ToBits` from Hermitian `k`-local instances satisfying
the refined NO energy bound. -/
def qmaClause3NoBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, qmaClause3ToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhNoInst E (qmaClause3NoBound E)

/-- The verifier register positions belonging to its ancilla block. -/
def qmaClause3AuxWires (V : QmaVerifier) (x : List Bool) :
    Finset (Fin (qmaRegisterSize V x.length)) :=
  Finset.univ.filter fun j =>
    V.witnessQubits x.length ≤ j.val
      ∧ j.val < V.witnessQubits x.length + V.auxQubits x.length

/-- The verifier output position immediately after its witness and ancilla blocks. -/
def qmaClause3OutWire (V : QmaVerifier) (x : List Bool) : Fin (qmaRegisterSize V x.length) :=
  ⟨V.witnessQubits x.length + V.auxQubits x.length, by
    show V.witnessQubits x.length + V.auxQubits x.length
      < V.witnessQubits x.length + V.auxQubits x.length + 1
    omega⟩

/-- The history circuit using the verifier's gates, with its ancilla and output wires required
to start at zero. -/
def qmaClause3VerifierCircuit (V : QmaVerifier) (x : List Bool) : QmaHistoryCircuit where
  qubits := qmaRegisterSize V x.length
  gates := V.program x
  legal := V.legal x
  initZeroWires := qmaClause3AuxWires V x ∪ {qmaClause3OutWire V x}
  outputWire := qmaClause3OutWire V x

end Qatlib.Concepts.QmaCompleteness.HistoryHam
