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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

def qmaRegSplit (w a : ℕ) : Reg (w + a + 1) ≃ (Reg w × Reg a) × Reg 1 :=
  (regAppendEquiv (w + a) 1).trans (Equiv.prodCongr (regAppendEquiv w a) (Equiv.refl (Reg 1)))

def qmaWitnessBits (w a : ℕ) (p : Reg (w + a + 1)) : Reg w := ((qmaRegSplit w a p).1).1

def qmaAncillaBits (w a : ℕ) (p : Reg (w + a + 1)) : Reg a := ((qmaRegSplit w a p).1).2

def qmaOutputBit (w a : ℕ) (p : Reg (w + a + 1)) : Bool := ((qmaRegSplit w a p).2) 0

noncomputable def qmaInitialState (w a : ℕ) (ψ : QState (Reg w)) :
    QState (Reg (w + a + 1)) :=
  fun p => TensorState (TensorState ψ (Ket (ZeroStr a))) (Ket (ZeroStr 1)) (qmaRegSplit w a p)

structure QmaVerifier where

  witnessQubits : ℕ → ℕ

  auxQubits : ℕ → ℕ

  program : List Bool → List FiniteGateCode

  legal : ∀ x : List Bool,
    finiteWordLegal (witnessQubits x.length + auxQubits x.length + 1) (program x) = true

  sizeBound : ∃ c k : ℕ, ∀ x : List Bool, (program x).length ≤ c * x.length ^ k + c

def qmaRegisterSize (V : QmaVerifier) (m : ℕ) : ℕ :=
  V.witnessQubits m + V.auxQubits m + 1

def qmaAcceptEvent (w a : ℕ) : Finset (Reg (w + a + 1)) :=
  Finset.univ.filter fun p => qmaOutputBit w a p

def qmaCleanAcceptEvent (w a : ℕ) : Finset (Reg (w + a + 1)) :=
  Finset.univ.filter fun p =>
    qmaOutputBit w a p && decide (qmaAncillaBits w a p = ZeroStr a)

noncomputable def qmaAcceptProb (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (finiteCodeCircuit (qmaRegisterSize V x.length) (V.program x))
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

noncomputable def qmaCleanAcceptProb (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (finiteCodeCircuit (qmaRegisterSize V x.length) (V.program x))
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaCleanAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

noncomputable def qmaAcceptProbW (V : QmaVerifier) (w : ℕ)
    (hw : ∀ m : ℕ, V.witnessQubits m = w) (x : List Bool) (ψ : QState (Reg w)) : ℝ :=
  qmaAcceptProb V x (cast (by rw [hw x.length]) ψ)

def qmaCodeBits (n : ℕ) : ℕ := 3 + 2 * n

def qmaProgramBits (V : QmaVerifier) (x : List Bool) : ℕ :=
  ((V.program x).map (fun _g => qmaCodeBits (qmaRegisterSize V x.length))).sum

noncomputable def finiteWordMatrix (n : ℕ) : List FiniteGateCode → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => finiteWordMatrix n gs * finiteCodeMatrix n g

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

theorem finiteWordMatrix_unitary (n : ℕ) (gs : List FiniteGateCode)
    (hg : finiteWordLegal n gs = true) :
    finiteWordMatrix n gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons g gs ih =>
    have hgg : finiteCodeLegal n g = true ∧ finiteWordLegal n gs = true := by
      simpa [finiteWordLegal] using hg
    exact Submonoid.mul_mem _ (ih hgg.2) (finiteCodeMatrix_unitary n g hgg.1)

noncomputable def qmaVerifierUnitary (V : QmaVerifier) (x : List Bool) :
    Matrix (Reg (V.witnessQubits x.length + V.auxQubits x.length + 1))
      (Reg (V.witnessQubits x.length + V.auxQubits x.length + 1)) ℂ :=
  finiteWordMatrix (V.witnessQubits x.length + V.auxQubits x.length + 1) (V.program x)

def qmaAcceptProjector (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  Matrix.diagonal fun p => if qmaOutputBit w a p then 1 else 0

def qmaInitProjector (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  Matrix.diagonal fun p =>
    if qmaAncillaBits w a p = ZeroStr a ∧ ¬qmaOutputBit w a p then 1 else 0

def qmaAcceptReflection (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  2 • qmaAcceptProjector w a - 1

def qmaInitReflection (w a : ℕ) :
    Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ :=
  2 • qmaInitProjector w a - 1

noncomputable def qmaMwRound (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) : Circuit (Reg (w + a + 1)) :=
  [Step.gate Uv, Step.gate (qmaAcceptReflection w a), Step.gate Uvᴴ,
    Step.gate (qmaInitReflection w a)]

noncomputable def qmaMwCircuit (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) (r : ℕ) :
    Circuit (Reg (w + a + 1)) :=
  RepeatCircuit (qmaMwRound w a Uv) r ++ [Step.gate Uv]

noncomputable def qmaMwAcceptProb (V : QmaVerifier) (x : List Bool) (r : ℕ)
    (ψ : QState (Reg (V.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
      (qmaMwCircuit (V.witnessQubits x.length) (V.auxQubits x.length)
        (qmaVerifierUnitary V x) r)
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ))
    (qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length))

def qmaWitnessEmbed (w a : ℕ) : Matrix (Reg (w + a + 1)) (Reg w) ℂ :=
  Matrix.of fun p y =>
    if qmaWitnessBits w a p = y ∧ qmaAncillaBits w a p = ZeroStr a ∧ ¬qmaOutputBit w a p then 1
    else 0

noncomputable def qmaAcceptanceOperator (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) : Matrix (Reg w) (Reg w) ℂ :=
  (qmaWitnessEmbed w a)ᴴ * Uvᴴ * qmaAcceptProjector w a * Uv * qmaWitnessEmbed w a

noncomputable def qmaMwPatternOperator (w : ℕ) (Q : Matrix (Reg w) (Reg w) ℂ) (m : ℕ)
    (b : Fin m → Bool) : Matrix (Reg w) (Reg w) ℂ :=
  (List.finRange m).foldr (fun j M => (if b j then Q else 1 - Q) * M) 1

def qmaTrueCount (m : ℕ) (b : Fin m → Bool) : ℕ := (Finset.univ.filter fun j => b j).card

noncomputable def qmaMwTailAcceptProb (w a : ℕ)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) (m j₀ : ℕ)
    (ψ : QState (Reg w)) : ℝ :=
  ∑ b : Fin m → Bool,
    if j₀ ≤ qmaTrueCount m b then
      ∑ y : Reg w,
        ‖(qmaMwPatternOperator w (qmaAcceptanceOperator w a Uv) m b *ᵥ ψ) y‖ ^ 2
    else 0

def qmaMwRealizes (V V' : QmaVerifier) (m j₀ : ℕ) : Prop :=
  ∀ (x : List Bool) (hwx : V'.witnessQubits x.length = V.witnessQubits x.length)
      (ψ : QState (Reg (V'.witnessQubits x.length))),
    qmaCleanAcceptProb V' x ψ
      = qmaMwTailAcceptProb (V'.witnessQubits x.length) (V.auxQubits x.length)
          (cast (by rw [hwx]) (qmaVerifierUnitary V x)) m j₀ ψ

def InPromiseQMA (Lyes Lno : List Bool → Prop) : Prop :=
  ∃ V : QmaVerifier,
    (∀ x : List Bool, Lyes x →
      ∃ ψ : QState (Reg (V.witnessQubits x.length)),
        Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb V x ψ)
    ∧ (∀ x : List Bool, Lno x →
      ∀ ψ : QState (Reg (V.witnessQubits x.length)), Normalized ψ →
        qmaAcceptProb V x ψ ≤ 1 / 3)

structure QmaHistoryCircuit where

  qubits : ℕ

  gates : List FiniteGateCode

  legal : finiteWordLegal qubits gates = true

  initZeroWires : Finset (Fin qubits)

  outputWire : Fin qubits

def qmaGateAt (gs : List FiniteGateCode) (t : ℕ) : FiniteGateCode :=
  match gs.drop t with
  | g :: _ => g
  | [] => .h 0

def qmaGateWires (n : ℕ) (g : FiniteGateCode) : List (Fin n) :=
  match g with
  | .h w | .x w | .t w | .tdg w => if h : w < n then [⟨w, h⟩] else []
  | .cx c t => if h : c < n ∧ t < n ∧ c ≠ t then [⟨c, h.1⟩, ⟨t, h.2.1⟩] else []

noncomputable def qmaHistoryAcceptProb (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits C.gates) φ)
    (Finset.univ.filter fun z => z C.outputWire)

def QmaInitLegal (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) : Prop :=
  ∀ p : Reg C.qubits, φ p ≠ 0 → ∀ j ∈ C.initZeroWires, p j = false

def qmaClockTerm (m : ℕ) (i j : Fin (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun p q => Ket i p * Ket j q

noncomputable def qmaPropTerm (n : ℕ) (m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  (1 / 2 : ℂ) • (TensorGate (qmaClockTerm m i.succ i.succ) 1
      + TensorGate (qmaClockTerm m i.castSucc i.castSucc) 1
      - TensorGate (qmaClockTerm m i.succ i.castSucc) (U i)
      - TensorGate (qmaClockTerm m i.castSucc i.succ) ((U i)ᴴ))

noncomputable def qmaInTerm (n m : ℕ) (j : Fin n) :
    Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  TensorGate (qmaClockTerm m 0 0) (Matrix.diagonal fun z => if z j then 1 else 0)

noncomputable def qmaOutTerm (n m : ℕ) (out : Fin n) :
    Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ :=
  TensorGate (qmaClockTerm m (Fin.last m) (Fin.last m))
    (Matrix.diagonal fun z => if z out then 0 else 1)

structure QmaHistoryTerm (n m : ℕ) where

  clockSupport : Finset (Fin (m + 1))

  workSupport : Finset (Fin n)

  matrix : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ

noncomputable def qmaExactGates (C : QmaHistoryCircuit) :
    Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
  fun t => finiteCodeMatrix C.qubits (qmaGateAt C.gates t.val)

noncomputable def qmaHistoryPropTerms (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  (List.finRange C.gates.length).map fun i =>
    { clockSupport := {i.castSucc, i.succ}
      workSupport := (qmaGateWires C.qubits (qmaGateAt C.gates i.val)).toFinset
      matrix := qmaPropTerm C.qubits C.gates.length U i }

noncomputable def qmaHistoryInTerms (C : QmaHistoryCircuit) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  C.initZeroWires.toList.map fun j =>
    { clockSupport := {0}
      workSupport := {j}
      matrix := qmaInTerm C.qubits C.gates.length j }

noncomputable def qmaHistoryOutTerm (C : QmaHistoryCircuit) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  [{ clockSupport := {Fin.last C.gates.length}
     workSupport := {C.outputWire}
     matrix := qmaOutTerm C.qubits C.gates.length C.outputWire }]

noncomputable def qmaHistoryTerms (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    List (QmaHistoryTerm C.qubits C.gates.length) :=
  qmaHistoryPropTerms C U ++ qmaHistoryInTerms C ++ qmaHistoryOutTerm C

noncomputable def qmaHistoryHamiltonian (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ) :
    Matrix (Fin (C.gates.length + 1) × Reg C.qubits)
      (Fin (C.gates.length + 1) × Reg C.qubits) ℂ :=
  (qmaHistoryTerms C U).foldr (fun t M => t.matrix + M) 0

noncomputable def qmaRoundC (b : ℕ) (z : ℂ) : ℂ :=
  (((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
    + Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)) / (2 ^ b : ℂ)

noncomputable def qmaRoundedGate (n b : ℕ) (g : FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => qmaRoundC b (finiteCodeMatrix n g x y)

noncomputable def qmaRoundedGates (C : QmaHistoryCircuit) (b : ℕ) :
    Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
  fun t => qmaRoundedGate C.qubits b (qmaGateAt C.gates t.val)

def qmaIsDyadic (width : ℕ) (z : ℂ) : Prop :=
  ∃ num : ℤ, z = (num : ℂ) / (2 ^ width : ℂ)

noncomputable def qmaTiny (k : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ k

def qmaActsOn (n m : ℕ)
    (T : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ)
    (Sc : Finset (Fin (m + 1))) (Sw : Finset (Fin n)) : Prop :=
  ∀ p q : Fin (m + 1) × Reg n, T p q ≠ 0 →
    p.1 ∈ Sc ∧ q.1 ∈ Sc ∧ ∀ j : Fin n, j ∉ Sw → p.2 j = q.2 j

noncomputable def qmaEnergy {I : Type*} [Fintype I] (H : Matrix I I ℂ) (η : QState I) : ℝ :=
  (Inner η (H *ᵥ η)).re

structure LhTerm (N : ℕ) where

  wires : List (Fin N)

  re : Matrix (Fin (2 ^ wires.length)) (Fin (2 ^ wires.length)) ℤ

  im : Matrix (Fin (2 ^ wires.length)) (Fin (2 ^ wires.length)) ℤ

structure LhEncoding where

  qubitCount : ℕ

  width : ℕ

  terms : List (LhTerm qubitCount)

def lhHermitian (E : LhEncoding) : Prop :=
  ∀ t ∈ E.terms, ∀ p q : Fin (2 ^ t.wires.length),
    t.re p q = t.re q p ∧ t.im p q = -t.im q p

noncomputable def lhValueMatrix (width : ℕ) {s : ℕ}
    (re im : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℤ) :
    Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ :=
  Matrix.of fun p q => ((re p q : ℂ) + Complex.I * (im p q : ℂ)) / (2 ^ width : ℂ)

def lhBitIndex {N : ℕ} (wires : List (Fin N)) (x : Reg N) : Fin (2 ^ wires.length) :=
  bitVecEquiv wires.length (fun i => x (wires.get i))

def lhAgreeOutside {N : ℕ} (wires : List (Fin N)) (x y : Reg N) : Bool :=
  (List.finRange N).all fun j => wires.contains j || (x j == y j)

noncomputable def lhEmbedTerm {N : ℕ} (width : ℕ) (t : LhTerm N) :
    Matrix (Reg N) (Reg N) ℂ :=
  Matrix.of fun x y =>
    if lhAgreeOutside t.wires x y then
      lhValueMatrix width t.re t.im (lhBitIndex t.wires x) (lhBitIndex t.wires y)
    else 0

noncomputable def lhHamiltonian (E : LhEncoding) :
    Matrix (Reg E.qubitCount) (Reg E.qubitCount) ℂ :=
  (E.terms.map (lhEmbedTerm E.width)).foldr (· + ·) 0

def lhLocal (k : ℕ) (E : LhEncoding) : Prop :=
  ∀ t ∈ E.terms, t.wires.length ≤ k

def LhYesInst (E : LhEncoding) (a : ℝ) : Prop :=
  ∃ η : QState (Reg E.qubitCount), Normalized η ∧ qmaEnergy (lhHamiltonian E) η ≤ a

def LhNoInst (E : LhEncoding) (b : ℝ) : Prop :=
  ∀ η : QState (Reg E.qubitCount), Normalized η → b ≤ qmaEnergy (lhHamiltonian E) η

def natToBits (len v : ℕ) : List Bool :=
  (List.range len).map fun i => decide (v / 2 ^ i % 2 = 1)

def intToBits (len : ℕ) (v : ℤ) : List Bool :=
  decide (0 ≤ v) :: natToBits len v.natAbs

def lhIndexPairs (d : ℕ) : List (Fin d × Fin d) :=
  (List.finRange d).flatMap fun p => (List.finRange d).map fun q => (p, q)

def lhTermToBits {N : ℕ} (width : ℕ) (t : LhTerm N) : List Bool :=
  ((t.wires.map fun j => natToBits N j.val).flatten)
    ++ (((lhIndexPairs (2 ^ t.wires.length)).map
        fun q => intToBits (width + 2 ^ t.wires.length + 64) (t.re q.1 q.2)).flatten)
    ++ (((lhIndexPairs (2 ^ t.wires.length)).map
        fun q => intToBits (width + 2 ^ t.wires.length + 64) (t.im q.1 q.2)).flatten)

def lhToBits (E : LhEncoding) : List Bool :=
  natToBits (E.qubitCount + 1) E.qubitCount
    ++ natToBits (E.width + 1) E.width
    ++ (E.terms.map (lhTermToBits E.width)).flatten

def LhYesBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, lhToBits E = x ∧ lhLocal k E ∧ lhHermitian E ∧ LhYesInst E 0

def LhNoBits (k : ℕ) (x : List Bool) : Prop :=
  ∃ E : LhEncoding, lhToBits E = x ∧ lhLocal k E ∧ lhHermitian E
    ∧ LhNoInst E (1 / (2 ^ 20 * (E.qubitCount + 1) ^ 4))

end Qatlib.Concepts.QmaCompleteness.HistoryHam
