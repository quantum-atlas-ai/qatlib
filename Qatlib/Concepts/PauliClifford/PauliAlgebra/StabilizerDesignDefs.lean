/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizer
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstructionDefs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLaws
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

open scoped Classical

theorem pauliMul1_assoc (a b c : Pauli1) :
    pauliMul1 (pauliMul1 a b) c = pauliMul1 a (pauliMul1 b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pauliMul1_I (a : Pauli1) : pauliMul1 .I a = a := by
  cases a <;> rfl

theorem pauliMul1_right_I (a : Pauli1) : pauliMul1 a .I = a := by
  cases a <;> rfl

instance pauliOneCommMonoid : CommMonoid Pauli1 where
  mul := pauliMul1
  one := .I
  mul_assoc := pauliMul1_assoc
  one_mul := pauliMul1_I
  mul_one := pauliMul1_right_I
  mul_comm := pauliMul1_comm

def trivialWord {n : ℕ} : PauliWord n := fun _ => .I

def IsTrivialWord {n : ℕ} (w : PauliWord n) : Prop := ∀ i, w i = .I

def pauliInv {n : ℕ} (p : PauliElem n) : PauliElem n := ⟨p.word, -p.phase⟩

theorem pauliMulPhase_I (a : Pauli1) : pauliMulPhase .I a = 0 := by
  cases a <;> rfl

theorem pauliMulPhase_right_I (a : Pauli1) : pauliMulPhase a .I = 0 := by
  cases a <;> rfl

theorem pauliMulPhase_cocycle (a b c : Pauli1) :
    pauliMulPhase a b + pauliMulPhase (pauliMul1 a b) c
      = pauliMulPhase b c + pauliMulPhase a (pauliMul1 b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem pauliMulPhase_sym (a b : Pauli1) :
    pauliMulPhase a b + pauliMulPhase b a = 0 := by
  cases a <;> cases b <;> decide

theorem pauliElem_mul_assoc' {n : ℕ} (p q r : PauliElem n) :
    PauliElem.mul (PauliElem.mul p q) r = PauliElem.mul p (PauliElem.mul q r) := by
  apply pauli_ext
  · funext i
    exact pauliMul1_assoc _ _ _
  · have h : ∀ i : Fin n,
        pauliMulPhase (p.word i) (q.word i)
          + pauliMulPhase (pauliMul1 (p.word i) (q.word i)) (r.word i)
        = pauliMulPhase (q.word i) (r.word i)
          + pauliMulPhase (p.word i) (pauliMul1 (q.word i) (r.word i)) := by
      intro i
      exact pauliMulPhase_cocycle _ _ _
    show p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i) + r.phase
        + ∑ i, pauliMulPhase (pauliMul1 (p.word i) (q.word i)) (r.word i)
      = p.phase + (q.phase + r.phase + ∑ i, pauliMulPhase (q.word i) (r.word i))
        + ∑ i, pauliMulPhase (p.word i) (pauliMul1 (q.word i) (r.word i))
    calc p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i) + r.phase
          + ∑ i, pauliMulPhase (pauliMul1 (p.word i) (q.word i)) (r.word i)
        = p.phase + q.phase + r.phase
          + (∑ i, pauliMulPhase (p.word i) (q.word i)
            + ∑ i, pauliMulPhase (pauliMul1 (p.word i) (q.word i)) (r.word i)) := by abel
      _ = p.phase + q.phase + r.phase
          + ∑ i, (pauliMulPhase (p.word i) (q.word i)
              + pauliMulPhase (pauliMul1 (p.word i) (q.word i)) (r.word i)) := by
        rw [Finset.sum_add_distrib]
      _ = p.phase + q.phase + r.phase
          + ∑ i, (pauliMulPhase (q.word i) (r.word i)
              + pauliMulPhase (p.word i) (pauliMul1 (q.word i) (r.word i))) := by
        simp_rw [h]
      _ = p.phase + q.phase + r.phase
          + (∑ i, pauliMulPhase (q.word i) (r.word i)
            + ∑ i, pauliMulPhase (p.word i) (pauliMul1 (q.word i) (r.word i))) := by
        rw [Finset.sum_add_distrib]
      _ = p.phase + (q.phase + r.phase + ∑ i, pauliMulPhase (q.word i) (r.word i))
          + ∑ i, pauliMulPhase (p.word i) (pauliMul1 (q.word i) (r.word i)) := by abel

instance pauliElemMul {n : ℕ} : Mul (PauliElem n) :=
  ⟨PauliElem.mul⟩

instance pauliElemInv {n : ℕ} : Inv (PauliElem n) :=
  ⟨pauliInv⟩

theorem pauliElem_herm_inv {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    pauliInv p = p := by
  apply pauli_ext
  · rfl
  · show -p.phase = p.phase
    rcases hp with hp0 | hp2
    · rw [hp0, neg_zero]
    · rw [hp2, show (-2 : ZMod 4) = 2 by decide]

theorem pauliElem_herm_sq {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    p * p = 1 := by
  apply pauli_ext
  · funext i
    exact pauliMul1_self _
  · show p.phase + p.phase + ∑ i, pauliMulPhase (p.word i) (p.word i) = (0 : Phase4)
    rcases hp with hp0 | hp2
    · rw [hp0, add_zero]
      simp [pauliMulPhase_self]
    · rw [hp2, show (2 : ZMod 4) + 2 = 0 by decide]
      simp [pauliMulPhase_self]

instance pauliElemDecidableEq {n : ℕ} : DecidableEq (PauliElem n) := by
  intro p q
  exact decidable_of_iff (p.word = q.word ∧ p.phase = q.phase)
    ⟨fun h => pauli_ext h.1 h.2,
     fun h => ⟨congrArg PauliElem.word h, congrArg PauliElem.phase h⟩⟩

def stabilizerFunSupport {n : ℕ} (φ : BooleanVec n → ℂ) : Set (BooleanVec n) :=
  {x | φ x ≠ 0}

noncomputable def stabilizerFunMass {n : ℕ} (φ : BooleanVec n → ℂ) : ℝ :=
  ∑ x, ‖φ x‖ ^ 2

noncomputable def normalizedStabilizerState {n : ℕ} (φ : BooleanVec n → ℂ) : QState (Reg n) :=
  stateOfFn (fun x => φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹)

theorem pauliWord_mul_self {n : ℕ} (w : PauliWord n) : w * w = 1 := by
  funext i
  exact pauliMul1_self _

theorem pauliWord_one_eq_trivial {n : ℕ} : (1 : PauliWord n) = trivialWord := by
  funext i
  rfl

theorem pauliElem_mul_word {n : ℕ} (p q : PauliElem n) :
    (PauliElem.mul p q).word = p.word * q.word := by
  funext i
  rfl

def cliffordSymplecticMap {n : ℕ} (g : CliffordGate n) :
    BooleanVec n × BooleanVec n → BooleanVec n × BooleanVec n
  | (x, z) =>
      match g with
      | .H i =>
          (fun j => if j = i then z j else x j, fun j => if j = i then x j else z j)
      | .S i =>
          (x, fun j => if j = i then z j + x j else z j)
      | .CNOT i j =>
          (fun k => if k = i then x k else if k = j then x k + x i else x k,
           fun k => if k = i then z k + z j else if k = j then z k else z k)

abbrev CliffordCircuit (n : ℕ) := List (CliffordGate n)

def cliffordActionCircuit {n : ℕ} : CliffordCircuit n → PauliElem n → PauliElem n
  | [], p => p
  | g :: gs, p => cliffordActionCircuit gs (cliffordAction g p)

def cliffordSymplecticCircuit {n : ℕ} : CliffordCircuit n →
    (BooleanVec n × BooleanVec n → BooleanVec n × BooleanVec n)
  | [] => id
  | g :: gs => fun v => cliffordSymplecticCircuit gs (cliffordSymplecticMap g v)

def IsNontrivialPauli {n : ℕ} (p : PauliElem n) : Prop :=
  p.word ≠ trivialWord

def zeroSympVec {n : ℕ} : BooleanVec n × BooleanVec n := 0

def siteCanonicalGates {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    List (CliffordGate n) :=
  if v.2 j = 0 then (if v.1 j = 0 then [.S j] else [.S j, .S j])
  else (if v.1 j = 0 then [.H j] else [.H j, .S j])

def siteCanonicalVector {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    BooleanVec n × BooleanVec n :=
  if v.2 j = 0 then (if v.1 j = 0 then cliffordSymplecticMap (.S j) v
    else cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.S j) v))
  else (if v.1 j = 0 then cliffordSymplecticMap (.H j) v
    else cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.H j) v))

def canonicalCircuit {n : ℕ} : List (Fin n) → BooleanVec n × BooleanVec n →
    List (CliffordGate n)
  | [], _ => []
  | j :: js, v => siteCanonicalGates j v ++ canonicalCircuit js (siteCanonicalVector j v)

def cnotFoldX {n : ℕ} (c : Fin n) : List (Fin n) → BooleanVec n → BooleanVec n
  | [], x => x
  | t :: ts, x => cnotFoldX c ts (fun j => if j = t then x j + x c else x j)

def e0SympVec (n : ℕ) : BooleanVec n × BooleanVec n :=
  ((fun j => if j.val = 0 then 1 else 0), fun _ => 0)

def supportTail {n : ℕ} (zero : Fin n) (x : BooleanVec n) : Finset (Fin n) :=
  (Finset.univ.erase zero).filter (fun j => x j ≠ 0)

def cnotClearCircuit {n : ℕ} (zero : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  (supportTail zero x).toList.map (fun j => CliffordGate.CNOT zero j)

def cnotFixCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  if x zero = 0 then [CliffordGate.CNOT i zero] else []

def cnotReduceCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  cnotFixCircuit zero i x ++ cnotClearCircuit zero x

def signedMeasuredPauli {n : ℕ} (p : PauliElem n) (b : Bool) : PauliElem n :=
  if b then p else PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n)

def measuredRow {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool)
    (i : Fin m) : Row n :=
  if i = a₀ then Qatlib.Concepts.PauliClifford.PauliAlgebra.encode (signedMeasuredPauli p b)
  else if pauliCommute (t i).decode p then t i
  else (t i).mul (t a₀)

def measuredTableau {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool) :
    Tableau n m :=
  fun i => measuredRow t a₀ p b i

def signFlipCircuit {n : ℕ} (i : Fin n) (a : Pauli1) : CliffordCircuit n :=
  match a with
  | .I => []
  | .X => [.S i, .S i]
  | .Y => [.H i, .S i, .S i, .H i]
  | .Z => [.H i, .S i, .S i, .H i]

def negPauliElem {n : ℕ} (p : PauliElem n) : PauliElem n := ⟨p.word, p.phase + 2⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra
