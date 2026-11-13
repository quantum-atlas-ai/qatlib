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

/-!
# Algebra and constructions for stabilizer tableaux

This module proves phase-free Pauli multiplication laws and associativity of phase-corrected
Pauli-element multiplication. It defines support, mass, and normalized register-state encodings
for functions on the binary cube, together with the Pauli and binary actions of finite Clifford
circuits.

The local canonicalization, CNOT reduction, sign-flip, and measurement-tableau constructions
provide the data used in the subsequent stabilizer proofs. The binary-coordinate viewpoint is
developed in [DehaeneDeMoor2003], and the tableau setting is described in
[AaronsonGottesman2004].

## Main statements

* `pauliElem_mul_assoc'`: associativity including local phase corrections.
* `normalizedStabilizerState`: rescaling by the square root of total amplitude mass.
* `cliffordSymplecticCircuit`: sequential binary action of a Clifford circuit.
* `measuredTableau`: row update for a specified Pauli measurement and outcome.
* `signFlipCircuit`: local circuit used in the Pauli sign-flip construction.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
* [Aaronson and Gottesman, 2004][AaronsonGottesman2004]
-/

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

/-- Phase-free single-site Pauli multiplication is associative. -/
theorem pauliMul1_assoc (a b c : Pauli1) :
    pauliMul1 (pauliMul1 a b) c = pauliMul1 a (pauliMul1 b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The identity letter is a left identity for phase-free single-site Pauli multiplication. -/
theorem pauliMul1_I (a : Pauli1) : pauliMul1 .I a = a := by
  cases a <;> rfl

/-- The identity letter is a right identity for phase-free single-site Pauli multiplication. -/
theorem pauliMul1_right_I (a : Pauli1) : pauliMul1 a .I = a := by
  cases a <;> rfl

instance pauliOneCommMonoid : CommMonoid Pauli1 where
  mul := pauliMul1
  one := .I
  mul_assoc := pauliMul1_assoc
  one_mul := pauliMul1_I
  mul_one := pauliMul1_right_I
  mul_comm := pauliMul1_comm

/-- The Pauli word consisting entirely of identity letters. -/
def trivialWord {n : ℕ} : PauliWord n := fun _ => .I

/-- Every letter of the Pauli word is the identity letter. -/
def IsTrivialWord {n : ℕ} (w : PauliWord n) : Prop := ∀ i, w i = .I

/-- Keeps a Pauli element's word and negates its phase exponent. -/
def pauliInv {n : ℕ} (p : PauliElem n) : PauliElem n := ⟨p.word, -p.phase⟩

/-- Multiplying the identity letter on the left introduces no Pauli phase correction. -/
theorem pauliMulPhase_I (a : Pauli1) : pauliMulPhase .I a = 0 := by
  cases a <;> rfl

/-- Multiplying the identity letter on the right introduces no Pauli phase correction. -/
theorem pauliMulPhase_right_I (a : Pauli1) : pauliMulPhase a .I = 0 := by
  cases a <;> rfl

/-- The local Pauli multiplication phase satisfies the cocycle identity expressing compatibility
with associativity. -/
theorem pauliMulPhase_cocycle (a b c : Pauli1) :
    pauliMulPhase a b + pauliMulPhase (pauliMul1 a b) c
      = pauliMulPhase b c + pauliMulPhase a (pauliMul1 b c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The phase corrections for the two multiplication orders sum to zero in `ZMod 4`. -/
theorem pauliMulPhase_sym (a b : Pauli1) :
    pauliMulPhase a b + pauliMulPhase b a = 0 := by
  cases a <;> cases b <;> decide

/-- Multiplication of Pauli elements, including the phase correction, is associative. -/
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

/-- Negating the phase exponent of a Hermitian Pauli element leaves the element unchanged. -/
theorem pauliElem_herm_inv {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    pauliInv p = p := by
  apply pauli_ext
  · rfl
  · show -p.phase = p.phase
    rcases hp with hp0 | hp2
    · rw [hp0, neg_zero]
    · rw [hp2, show (-2 : ZMod 4) = 2 by decide]

/-- A Hermitian Pauli element squares to the identity element. -/
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

/-- The set of binary inputs at which a complex-valued function is nonzero. -/
def stabilizerFunSupport {n : ℕ} (φ : BooleanVec n → ℂ) : Set (BooleanVec n) :=
  {x | φ x ≠ 0}

/-- The total squared norm of a complex-valued function on the binary cube. -/
noncomputable def stabilizerFunMass {n : ℕ} (φ : BooleanVec n → ℂ) : ℝ :=
  ∑ x, ‖φ x‖ ^ 2

/-- Encodes a binary-cube function as a register state after dividing its amplitudes by the
square root of its total mass. -/
noncomputable def normalizedStabilizerState {n : ℕ} (φ : BooleanVec n → ℂ) : QState (Reg n) :=
  stateOfFn (fun x => φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹)

/-- Every phase-free Pauli word squares to the identity word. -/
theorem pauliWord_mul_self {n : ℕ} (w : PauliWord n) : w * w = 1 := by
  funext i
  exact pauliMul1_self _

/-- The multiplicative identity Pauli word is `trivialWord`. -/
theorem pauliWord_one_eq_trivial {n : ℕ} : (1 : PauliWord n) = trivialWord := by
  funext i
  rfl

/-- The word of a Pauli-element product is the pointwise phase-free product of the two words. -/
theorem pauliElem_mul_word {n : ℕ} (p q : PauliElem n) :
    (PauliElem.mul p q).word = p.word * q.word := by
  funext i
  rfl

/-- The binary coordinate update associated with a Hadamard, phase, or CNOT gate. -/
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

/-- A finite list of Clifford gates on `n` sites. -/
abbrev CliffordCircuit (n : ℕ) := List (CliffordGate n)

/-- Applies a list of Clifford gates to a Pauli element in list order. -/
def cliffordActionCircuit {n : ℕ} : CliffordCircuit n → PauliElem n → PauliElem n
  | [], p => p
  | g :: gs, p => cliffordActionCircuit gs (cliffordAction g p)

/-- Applies the binary symplectic maps of a Clifford circuit in list order. -/
def cliffordSymplecticCircuit {n : ℕ} : CliffordCircuit n →
    (BooleanVec n × BooleanVec n → BooleanVec n × BooleanVec n)
  | [] => id
  | g :: gs => fun v => cliffordSymplecticCircuit gs (cliffordSymplecticMap g v)

/-- The Pauli element has a word different from `trivialWord`. -/
def IsNontrivialPauli {n : ℕ} (p : PauliElem n) : Prop :=
  p.word ≠ trivialWord

/-- The zero pair of binary X and Z vectors. -/
def zeroSympVec {n : ℕ} : BooleanVec n × BooleanVec n := 0

/-- Chooses a local sequence of Hadamard and phase gates from the binary coordinates at a
selected site. -/
def siteCanonicalGates {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    List (CliffordGate n) :=
  if v.2 j = 0 then (if v.1 j = 0 then [.S j] else [.S j, .S j])
  else (if v.1 j = 0 then [.H j] else [.H j, .S j])

/-- The binary vector obtained by applying the selected local canonicalization gates at one
site. -/
def siteCanonicalVector {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    BooleanVec n × BooleanVec n :=
  if v.2 j = 0 then (if v.1 j = 0 then cliffordSymplecticMap (.S j) v
    else cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.S j) v))
  else (if v.1 j = 0 then cliffordSymplecticMap (.H j) v
    else cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.H j) v))

/-- Builds a circuit that successively canonicalizes the listed sites, using the updated binary
vector at each step. -/
def canonicalCircuit {n : ℕ} : List (Fin n) → BooleanVec n × BooleanVec n →
    List (CliffordGate n)
  | [], _ => []
  | j :: js, v => siteCanonicalGates j v ++ canonicalCircuit js (siteCanonicalVector j v)

/-- Successively adds the control X coordinate at each listed target. -/
def cnotFoldX {n : ℕ} (c : Fin n) : List (Fin n) → BooleanVec n → BooleanVec n
  | [], x => x
  | t :: ts, x => cnotFoldX c ts (fun j => if j = t then x j + x c else x j)

/-- The binary symplectic vector with X coordinate one at index zero and all other coordinates
zero. -/
def e0SympVec (n : ℕ) : BooleanVec n × BooleanVec n :=
  ((fun j => if j.val = 0 then 1 else 0), fun _ => 0)

/-- The finite set of nonzero X coordinates outside a distinguished index. -/
def supportTail {n : ℕ} (zero : Fin n) (x : BooleanVec n) : Finset (Fin n) :=
  (Finset.univ.erase zero).filter (fun j => x j ≠ 0)

/-- Builds CNOT gates from a distinguished control to each index in `supportTail zero x`. -/
def cnotClearCircuit {n : ℕ} (zero : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  (supportTail zero x).toList.map (fun j => CliffordGate.CNOT zero j)

/-- Uses CNOT from `i` to the distinguished site when the latter's X coordinate is zero, and
uses no gates otherwise. -/
def cnotFixCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  if x zero = 0 then [CliffordGate.CNOT i zero] else []

/-- Concatenates the circuit fixing the distinguished X coordinate with the circuit clearing the
remaining support. -/
def cnotReduceCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) : List (CliffordGate n) :=
  cnotFixCircuit zero i x ++ cnotClearCircuit zero x

/-- The measured Pauli element for outcome true and its product with negative identity for
outcome false. -/
def signedMeasuredPauli {n : ℕ} (p : PauliElem n) (b : Bool) : PauliElem n :=
  if b then p else PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n)

/-- Replaces the selected row by the signed measured Pauli, keeps other commuting rows, and
multiplies other noncommuting rows by the selected row. -/
def measuredRow {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool)
    (i : Fin m) : Row n :=
  if i = a₀ then Qatlib.Concepts.PauliClifford.PauliAlgebra.encode (signedMeasuredPauli p b)
  else if pauliCommute (t i).decode p then t i
  else (t i).mul (t a₀)

/-- The tableau whose rows are obtained by `measuredRow` for a selected measurement row and
outcome. -/
def measuredTableau {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool) :
    Tableau n m :=
  fun i => measuredRow t a₀ p b i

/-- Chooses a local Clifford circuit from a site index and Pauli letter to implement the
subsequent sign-flip construction. -/
def signFlipCircuit {n : ℕ} (i : Fin n) (a : Pauli1) : CliffordCircuit n :=
  match a with
  | .I => []
  | .X => [.S i, .S i]
  | .Y => [.H i, .S i, .S i, .H i]
  | .Z => [.H i, .S i, .S i, .H i]

/-- Keeps a Pauli word and adds two to its phase exponent, representing operator negation. -/
def negPauliElem {n : ℕ} (p : PauliElem n) : PauliElem n := ⟨p.word, p.phase + 2⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra
