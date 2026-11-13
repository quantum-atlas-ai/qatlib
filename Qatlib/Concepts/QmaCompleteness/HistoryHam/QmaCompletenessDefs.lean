/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Mathlib.Algebra.Order.Floor.Ring

/-!
# QMA verifiers and history Hamiltonians

This module defines `QmaVerifier`, its acceptance probabilities, and the promise predicate
`InPromiseQMA`. It also introduces witness embeddings, acceptance operators, and reflection
circuits used to formulate amplification, following the quantum verification framework of
[KitaevShenVyalyi2002] and [MarriottWatrous2005].

`QmaHistoryCircuit` supplies the data for a finite Feynman–Kitaev construction. The module
defines propagation and boundary terms, their sum `qmaHistoryHamiltonian`, entrywise rounding,
and finite local Hamiltonian encodings with variational YES and NO predicates. These definitions
support the circuit-to-Hamiltonian analysis of [KempeKitaevRegev2006].

## Main definitions

* `QmaVerifier`: legal finite gate programs with a polynomial bound on program length.
* `InPromiseQMA`: completeness and soundness conditions with thresholds 2/3 and 1/3.
* `qmaHistoryHamiltonian`: the sum of propagation, input, and output penalties.
* `LhEncoding`: integer local matrices interpreted at a common dyadic scale.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
* [Marriott and Watrous, 2005][MarriottWatrous2005]
* [Kempe, Kitaev and Regev, 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open Matrix
open scoped BigOperators

set_option autoImplicit false

/-- The register equivalence separating `w` witness bits, `a` ancilla bits, and one output bit. -/
def qmaRegSplit (w a : ℕ) : Reg (w + a + 1) ≃ (Reg w × Reg a) × Reg 1 :=
  (regAppendEquiv (w + a) 1).trans (Equiv.prodCongr (regAppendEquiv w a) (Equiv.refl (Reg 1)))

/-- Extracts the witness block from a verifier basis register. -/
def qmaWitnessBits (w a : ℕ) (p : Reg (w + a + 1)) : Reg w := ((qmaRegSplit w a p).1).1

/-- Extracts the ancilla block from a verifier basis register. -/
def qmaAncillaBits (w a : ℕ) (p : Reg (w + a + 1)) : Reg a := ((qmaRegSplit w a p).1).2

/-- Extracts the final output bit from a verifier basis register. -/
def qmaOutputBit (w a : ℕ) (p : Reg (w + a + 1)) : Bool := ((qmaRegSplit w a p).2) 0

/-- Embeds the witness state `ψ` into the full register with the ancilla and output registers
initialized to zero. -/
noncomputable def qmaInitialState (w a : ℕ) (ψ : QState (Reg w)) :
    QState (Reg (w + a + 1)) :=
  fun p => TensorState (TensorState ψ (Ket (ZeroStr a))) (Ket (ZeroStr 1)) (qmaRegSplit w a p)

/-- A family of legal finite gate programs with witness and ancilla sizes depending on input
length and a polynomial bound on program length. -/
structure QmaVerifier where

  witnessQubits : ℕ → ℕ

  auxQubits : ℕ → ℕ

  program : List Bool → List FiniteGateCode

  legal : ∀ x : List Bool,
    finiteWordLegal (witnessQubits x.length + auxQubits x.length + 1) (program x) = true

  sizeBound : ∃ c k : ℕ, ∀ x : List Bool, (program x).length ≤ c * x.length ^ k + c

/-- The total number of witness, ancilla, and output qubits for inputs of length `m`. -/
def qmaRegisterSize (V : QmaVerifier) (m : ℕ) : ℕ :=
  V.witnessQubits m + V.auxQubits m + 1

/-- The basis registers whose output bit is true. -/
def qmaAcceptEvent (w a : ℕ) : Finset (Reg (w + a + 1)) :=
  Finset.univ.filter fun p => qmaOutputBit w a p

/-- The basis registers whose output bit is true and whose ancilla block is zero. -/
def qmaCleanAcceptEvent (w a : ℕ) : Finset (Reg (w + a + 1)) :=
  Finset.univ.filter fun p =>
    qmaOutputBit w a p && decide (qmaAncillaBits w a p = ZeroStr a)

/-- The output acceptance weight after running `V` on input `x` with witness `ψ` and zero
ancillas. -/
noncomputable def qmaAcceptProb (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (finiteCodeCircuit (qmaRegisterSize V x.length) (V.program x))
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

/-- The acceptance weight requiring both a true output bit and a zero ancilla block after
running the verifier. -/
noncomputable def qmaCleanAcceptProb (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (finiteCodeCircuit (qmaRegisterSize V x.length) (V.program x))
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaCleanAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

/-- The verifier acceptance weight expressed on a fixed witness register using the size
equalities `hw`. -/
noncomputable def qmaAcceptProbW (V : QmaVerifier) (w : ℕ)
    (hw : ∀ m : ℕ, V.witnessQubits m = w) (x : List Bool) (ψ : QState (Reg w)) : ℝ :=
  qmaAcceptProb V x (cast (by rw [hw x.length]) ψ)

/-- The gate encoding size budget `3 + 2 * n` for an `n`-qubit register. -/
def qmaCodeBits (n : ℕ) : ℕ := 3 + 2 * n

/-- The sum of the gate encoding size budgets over the verifier program for `x`. -/
def qmaProgramBits (V : QmaVerifier) (x : List Bool) : ℕ :=
  ((V.program x).map (fun _g => qmaCodeBits (qmaRegisterSize V x.length))).sum

/-- The matrix of a finite gate word, with each successive gate multiplying on the left. -/
noncomputable def finiteWordMatrix (n : ℕ) : List FiniteGateCode → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => finiteWordMatrix n gs * finiteCodeMatrix n g

/-- Running the circuit associated to a finite gate word equals applying `finiteWordMatrix` to
the initial state. -/
theorem run_finiteCodeCircuit (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ
      = (finiteWordMatrix n gs).mulVec ψ := by
  induction gs generalizing ψ with
  | nil => simp [finiteCodeCircuit, finiteWordMatrix]
  | cons g gs ih =>
    have h1 : finiteCodeCircuit n (g :: gs)
        = Step.gate (finiteCodeMatrix n g) :: finiteCodeCircuit n gs := rfl
    rw [h1, run_gate, ih, ApplyGate, Matrix.mulVec_mulVec]
    rfl

/-- The matrix of a legal finite gate word is unitary. -/
theorem finiteWordMatrix_unitary (n : ℕ) (gs : List FiniteGateCode)
    (hg : finiteWordLegal n gs = true) :
    finiteWordMatrix n gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons g gs ih =>
    have hgg : finiteCodeLegal n g = true ∧ finiteWordLegal n gs = true := by
      simpa [finiteWordLegal] using hg
    exact Submonoid.mul_mem _ (ih hgg.2) (finiteCodeMatrix_unitary n g hgg.1)

/-- The matrix obtained by composing the verifier's finite gate program on input `x`. -/
noncomputable def qmaVerifierUnitary (V : QmaVerifier) (x : List Bool) :
    Matrix (Reg (V.witnessQubits x.length + V.auxQubits x.length + 1))
      (Reg (V.witnessQubits x.length + V.auxQubits x.length + 1)) ℂ :=
  finiteWordMatrix (V.witnessQubits x.length + V.auxQubits x.length + 1) (V.program x)

/-- The diagonal projector onto basis registers with a true output bit. -/
def qmaAcceptProjector (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  Matrix.diagonal fun p => if qmaOutputBit w a p then 1 else 0

/-- The diagonal projector onto basis registers with zero ancillas and a false output bit. -/
def qmaInitProjector (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  Matrix.diagonal fun p =>
    if qmaAncillaBits w a p = ZeroStr a ∧ ¬qmaOutputBit w a p then 1 else 0

/-- The reflection `2 • qmaAcceptProjector w a - 1` about the accepting subspace. -/
def qmaAcceptReflection (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  2 • qmaAcceptProjector w a - 1

/-- The reflection `2 • qmaInitProjector w a - 1` about the initialized subspace. -/
def qmaInitReflection (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  2 • qmaInitProjector w a - 1

/-- The four-gate round applying `Uv`, the acceptance reflection, `Uvᴴ`, and the initialization
reflection in that order. -/
noncomputable def qmaMwRound (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) : Circuit (Reg (w + a + 1)) :=
  [Step.gate Uv, Step.gate (qmaAcceptReflection w a), Step.gate Uvᴴ,
    Step.gate (qmaInitReflection w a)]

/-- Repeats `qmaMwRound` for `r` rounds and then applies `Uv` once more. -/
noncomputable def qmaMwCircuit (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) (r : ℕ) :
    Circuit (Reg (w + a + 1)) :=
  RepeatCircuit (qmaMwRound w a Uv) r ++ [Step.gate Uv]

/-- The acceptance weight of `qmaMwCircuit` on the witness state with zero ancillas and output
bit. -/
noncomputable def qmaMwAcceptProb (V : QmaVerifier) (x : List Bool) (r : ℕ)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (qmaMwCircuit (V.witnessQubits x.length) (V.auxQubits x.length)
        (qmaVerifierUnitary V x) r)
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

/-- The matrix embedding a witness basis register into the full register with zero ancillas and
output bit. -/
def qmaWitnessEmbed (w a : ℕ) : Matrix (Reg (w + a + 1)) (Reg w) ℂ :=
  Matrix.of fun p y =>
    if qmaWitnessBits w a p = y ∧ qmaAncillaBits w a p = ZeroStr a ∧ ¬qmaOutputBit w a p then 1
    else 0

/-- The accepting projector conjugated by `Uv` and compressed to the embedded witness register. -/
noncomputable def qmaAcceptanceOperator (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) : Matrix (Reg w) (Reg w) ℂ :=
  (qmaWitnessEmbed w a)ᴴ * Uvᴴ * qmaAcceptProjector w a * Uv * qmaWitnessEmbed w a

/-- The ordered product selecting `Q` for true bits of `b` and `1 - Q` for false bits. -/
noncomputable def qmaMwPatternOperator (w : ℕ) (Q : Matrix (Reg w) (Reg w) ℂ) (m : ℕ)
    (b : Fin m → Bool) : Matrix (Reg w) (Reg w) ℂ :=
  (List.finRange m).foldr (fun j M => (if b j then Q else 1 - Q) * M) 1

/-- The number of true bits in the Boolean pattern `b`. -/
def qmaTrueCount (m : ℕ) (b : Fin m → Bool) : ℕ := (Finset.univ.filter fun j => b j).card

/-- The sum of squared pattern-operator amplitudes over patterns containing at least `j₀` true
bits. -/
noncomputable def qmaMwTailAcceptProb (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) (m j₀ : ℕ)
    (ψ : QState (Reg w)) : ℝ :=
  ∑ b : Fin m → Bool,
    if j₀ ≤ qmaTrueCount m b then
      ∑ y : Reg w,
        ‖(qmaMwPatternOperator w (qmaAcceptanceOperator w a Uv) m b *ᵥ ψ) y‖ ^ 2
    else 0

/-- Requires the clean acceptance weight of `V'` to equal the tail expression for `V` whenever
their witness sizes agree. -/
def qmaMwRealizes (V V' : QmaVerifier) (m j₀ : ℕ) : Prop :=
  ∀ (x : List Bool) (hwx : V'.witnessQubits x.length = V.witnessQubits x.length)
      (ψ : QState (Reg (V'.witnessQubits x.length))),
    qmaCleanAcceptProb V' x ψ
      = qmaMwTailAcceptProb (V'.witnessQubits x.length) (V.auxQubits x.length)
          (cast (by rw [hwx]) (qmaVerifierUnitary V x)) m j₀ ψ

/-- The existence of a verifier accepting some normalized witness on each YES input with weight
at least 2/3 and every normalized witness on each NO input with weight at most 1/3. -/
def InPromiseQMA (Lyes Lno : List Bool → Prop) : Prop :=
  ∃ V : QmaVerifier,
    (∀ x : List Bool, Lyes x →
      ∃ ψ : QState (Reg (V.witnessQubits x.length)),
        Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb V x ψ)
    ∧ (∀ x : List Bool, Lno x →
      ∀ ψ : QState (Reg (V.witnessQubits x.length)), Normalized ψ →
        qmaAcceptProb V x ψ ≤ 1 / 3)

/-- A legal finite gate word with designated initially zero wires and an output wire for a
history Hamiltonian. -/
structure QmaHistoryCircuit where

  qubits : ℕ

  gates : List FiniteGateCode

  legal : finiteWordLegal qubits gates = true

  initZeroWires : Finset (Fin qubits)

  outputWire : Fin qubits

/-- Returns the gate at position `t`, using a Hadamard on wire zero when the position is out of
range. -/
def qmaGateAt (gs : List FiniteGateCode) (t : ℕ) : FiniteGateCode :=
  match gs.drop t with
  | g :: _ => g
  | [] => .h 0

/-- The register wires of a legal single-qubit or controlled-X gate, with the empty list
returned for invalid wire data. -/
def qmaGateWires (n : ℕ) (g : FiniteGateCode) : List (Fin n) :=
  match g with
  | .h w | .x w | .t w | .tdg w => if h : w < n then [⟨w, h⟩] else []
  | .cx c t => if h : c < n ∧ t < n ∧ c ≠ t then [⟨c, h.1⟩, ⟨t, h.2.1⟩] else []

/-- The output acceptance weight after applying the history circuit's gate word to `φ`. -/
noncomputable def qmaHistoryAcceptProb (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits C.gates) φ)
    (Finset.univ.filter fun z => z C.outputWire)

/-- Requires every basis register in the support of `φ` to be zero on the circuit's
initialization wires. -/
def QmaInitLegal (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) : Prop :=
  ∀ p : Reg C.qubits, φ p ≠ 0 → ∀ j ∈ C.initZeroWires, p j = false

/-- The clock matrix unit with its sole nonzero entry in row `i` and column `j`. -/
def qmaClockTerm (m : ℕ) (i j : Fin (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun p q => Ket i p * Ket j q

/-- The half-scaled propagation block coupling clock positions `i.castSucc` and `i.succ` through
`U i` and its adjoint. -/
noncomputable def qmaPropTerm (n : ℕ) (m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  (1 / 2 : ℂ) • (TensorGate (qmaClockTerm m i.succ i.succ) 1
      + TensorGate (qmaClockTerm m i.castSucc i.castSucc) 1
      - TensorGate (qmaClockTerm m i.succ i.castSucc) (U i)
      - TensorGate (qmaClockTerm m i.castSucc i.succ) ((U i)ᴴ))

/-- The initial-time penalty for a true bit on work wire `j`. -/
noncomputable def qmaInTerm (n m : ℕ) (j : Fin n) :
    Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  TensorGate (qmaClockTerm m 0 0) (Matrix.diagonal fun z => if z j then 1 else 0)

/-- The final-time penalty for a false bit on the designated output wire. -/
noncomputable def qmaOutTerm (n m : ℕ) (out : Fin n) :
    Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  TensorGate (qmaClockTerm m (Fin.last m) (Fin.last m))
    (Matrix.diagonal fun z => if z out then 0 else 1)

/-- A matrix on the clock and work registers together with designated clock and work support
sets. -/
structure QmaHistoryTerm (n m : ℕ) where

  clockSupport : Finset (Fin (m + 1))

  workSupport : Finset (Fin n)

  matrix : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ

/-- The exact gate matrices indexed by the positions of a history circuit's gate word. -/
noncomputable def qmaExactGates (C : QmaHistoryCircuit) :
    Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
  fun t => finiteCodeMatrix C.qubits (qmaGateAt C.gates t.val)

/-- The propagation terms with their adjacent clock positions and gate wire supports. -/
noncomputable def qmaHistoryPropTerms (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  (List.finRange C.gates.length).map fun i =>
    { clockSupport := {i.castSucc, i.succ}
      workSupport := (qmaGateWires C.qubits (qmaGateAt C.gates i.val)).toFinset
      matrix := qmaPropTerm C.qubits C.gates.length U i }

/-- The initial-time penalties for all designated initially zero wires, with their support sets. -/
noncomputable def qmaHistoryInTerms (C : QmaHistoryCircuit) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  C.initZeroWires.toList.map fun j =>
    { clockSupport := {0}
      workSupport := {j}
      matrix := qmaInTerm C.qubits C.gates.length j }

/-- The singleton list containing the final output penalty and its support sets. -/
noncomputable def qmaHistoryOutTerm (C : QmaHistoryCircuit) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  [{ clockSupport := {Fin.last C.gates.length}
     workSupport := {C.outputWire}
     matrix := qmaOutTerm C.qubits C.gates.length C.outputWire }]

/-- The concatenated list of propagation, input, and output terms for the gate matrices `U`. -/
noncomputable def qmaHistoryTerms (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  qmaHistoryPropTerms C U ++ qmaHistoryInTerms C ++ qmaHistoryOutTerm C

/-- The sum of the matrices in `qmaHistoryTerms C U`. -/
noncomputable def qmaHistoryHamiltonian (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    Matrix (Fin (C.gates.length + 1) × Reg C.qubits)
      (Fin (C.gates.length + 1) × Reg C.qubits) ℂ :=
  (qmaHistoryTerms C U).foldr (fun t M => t.matrix + M) 0

/-- Rounds the real and imaginary parts of `z` to multiples of `2⁻ᵇ` using `floor (x * 2^b +
1/2)`. -/
noncomputable def qmaRoundC (b : ℕ) (z : ℂ) : ℂ :=
  (((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
    + Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)) / (2 ^ b : ℂ)

/-- The entrywise dyadic rounding of the matrix associated to the finite gate code `g`. -/
noncomputable def qmaRoundedGate (n b : ℕ) (g : FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => qmaRoundC b (finiteCodeMatrix n g x y)

/-- The gate matrices of `C` rounded entrywise at precision `b`. -/
noncomputable def qmaRoundedGates (C : QmaHistoryCircuit) (b : ℕ) :
    Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
  fun t => qmaRoundedGate C.qubits b (qmaGateAt C.gates t.val)

/-- Requires `z` to equal an integer divided by `2^width`, viewed as a complex number. -/
def qmaIsDyadic (width : ℕ) (z : ℂ) : Prop :=
  ∃ num : ℤ, z = (num : ℂ) / (2 ^ width : ℂ)

/-- The error scale `2⁻ᵏ` as a real number. -/
noncomputable def qmaTiny (k : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ k

/-- Requires nonzero matrix entries to lie in `Sc` in both clock coordinates and to agree on all
work wires outside `Sw`. -/
def qmaActsOn (n m : ℕ)
    (T : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ)
    (Sc : Finset (Fin (m + 1))) (Sw : Finset (Fin n)) : Prop :=
  ∀ p q : Fin (m + 1) × Reg n, T p q ≠ 0 →
    p.1 ∈ Sc ∧ q.1 ∈ Sc ∧ ∀ j : Fin n, j ∉ Sw → p.2 j = q.2 j

/-- The real part of the quadratic form `Inner η (H *ᵥ η)`. -/
noncomputable def qmaEnergy {I : Type*} [Fintype I] (H : Matrix I I ℂ) (η : QState I) : ℝ :=
  (Inner η (H *ᵥ η)).re

/-- A local term specified by an ordered list of wires and integer matrices for its real and
imaginary numerators. -/
structure LhTerm (N : ℕ) where

  wires : List (Fin N)

  re : Matrix (Fin (2 ^ wires.length)) (Fin (2 ^ wires.length)) ℤ

  im : Matrix (Fin (2 ^ wires.length)) (Fin (2 ^ wires.length)) ℤ

/-- A finite local Hamiltonian description with a qubit count, a common dyadic precision, and a
list of local terms. -/
structure LhEncoding where

  qubitCount : ℕ

  width : ℕ

  terms : List (LhTerm qubitCount)

/-- Requires each encoded term to have symmetric real numerators and skew-symmetric imaginary
numerators. -/
def lhHermitian (E : LhEncoding) : Prop :=
  ∀ t ∈ E.terms, ∀ p q : Fin (2 ^ t.wires.length),
    t.re p q = t.re q p ∧ t.im p q = -t.im q p

/-- Interprets integer real and imaginary numerator matrices as a complex matrix divided by
`2^width`. -/
noncomputable def lhValueMatrix (width : ℕ) {s : ℕ}
    (re im : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℤ) :
    Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ :=
  Matrix.of fun p q => ((re p q : ℂ) + Complex.I * (im p q : ℂ)) / (2 ^ width : ℂ)

/-- The basis index obtained by reading the bits of `x` along the ordered wire list. -/
def lhBitIndex {N : ℕ} (wires : List (Fin N)) (x : Reg N) : Fin (2 ^ wires.length) :=
  bitVecEquiv wires.length (fun i => x (wires.get i))

/-- Tests whether two basis registers agree on every wire outside the given list. -/
def lhAgreeOutside {N : ℕ} (wires : List (Fin N)) (x y : Reg N) : Bool :=
  (List.finRange N).all fun j => wires.contains j || (x j == y j)

/-- Embeds a local dyadic matrix into the full register, setting entries to zero when the
exterior bits differ. -/
noncomputable def lhEmbedTerm {N : ℕ} (width : ℕ) (t : LhTerm N) :
    Matrix (Reg N) (Reg N) ℂ :=
  Matrix.of fun x y =>
    if lhAgreeOutside t.wires x y then
      lhValueMatrix width t.re t.im (lhBitIndex t.wires x) (lhBitIndex t.wires y)
    else 0

/-- The sum of the embedded local terms in an encoding. -/
noncomputable def lhHamiltonian (E : LhEncoding) :
    Matrix (Reg E.qubitCount) (Reg E.qubitCount) ℂ :=
  (E.terms.map (lhEmbedTerm E.width)).foldr (· + ·) 0

/-- Requires every encoded term to use at most `k` listed wires. -/
def lhLocal (k : ℕ) (E : LhEncoding) : Prop :=
  ∀ t ∈ E.terms, t.wires.length ≤ k

/-- The existence of a normalized state whose encoded Hamiltonian energy is at most `a`. -/
def LhYesInst (E : LhEncoding) (a : ℝ) : Prop :=
  ∃ η : QState (Reg E.qubitCount), Normalized η ∧ qmaEnergy (lhHamiltonian E) η ≤ a

/-- Requires every normalized state to have encoded Hamiltonian energy at least `b`. -/
def LhNoInst (E : LhEncoding) (b : ℝ) : Prop :=
  ∀ η : QState (Reg E.qubitCount), Normalized η → b ≤ qmaEnergy (lhHamiltonian E) η

/-- The low `len` binary digits of `v`, listed from least to most significant. -/
def natToBits (len v : ℕ) : List Bool :=
  (List.range len).map fun i => decide (v / 2 ^ i % 2 = 1)

/-- A nonnegativity bit followed by the low `len` binary digits of the absolute value of `v`. -/
def intToBits (len : ℕ) (v : ℤ) : List Bool :=
  decide (0 ≤ v) :: natToBits len v.natAbs

/-- All ordered pairs of indices in `Fin d`, listed with the first index varying in the outer
loop. -/
def lhIndexPairs (d : ℕ) : List (Fin d × Fin d) :=
  (List.finRange d).flatMap fun p => (List.finRange d).map fun q => (p, q)

/-- Serializes a term's wires and integer matrix entries using the prescribed fixed widths. -/
def lhTermToBits {N : ℕ} (width : ℕ) (t : LhTerm N) : List Bool :=
  ((t.wires.map fun j => natToBits N j.val).flatten)
    ++ (((lhIndexPairs (2 ^ t.wires.length)).map
        fun q => intToBits (width + 2 ^ t.wires.length + 64) (t.re q.1 q.2)).flatten)
    ++ (((lhIndexPairs (2 ^ t.wires.length)).map
        fun q => intToBits (width + 2 ^ t.wires.length + 64) (t.im q.1 q.2)).flatten)

/-- Serializes the qubit count, precision, and concatenated term data using `natToBits` and
`lhTermToBits`. -/
def lhToBits (E : LhEncoding) : List Bool :=
  natToBits (E.qubitCount + 1) E.qubitCount
    ++ natToBits (E.width + 1) E.width
    ++ (E.terms.map (lhTermToBits E.width)).flatten

/-- Bit strings encoding a Hermitian `k`-local instance with some normalized state of energy at
most zero. -/
def LhYesBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, lhToBits E = x ∧ lhLocal k E ∧ lhHermitian E ∧ LhYesInst E 0

/-- Bit strings encoding a Hermitian `k`-local instance whose normalized states all have energy
at least `1 / (2^20 * (E.qubitCount + 1)^4)`. -/
def LhNoBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, lhToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhNoInst E (1 / (2 ^ 20 * (E.qubitCount + 1) ^ 4))

end Qatlib.Concepts.QmaCompleteness.HistoryHam
