/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardCoordinates
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizer
import Qatlib.Concepts.PauliClifford.ExactRank.ExactRankCollision
import Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

/-!
# Stabilizer tableau construction data

This module defines the coordinate conversions, Pauli predicates, and matrix expressions used to
construct stabilizer tableaux. The equivalence `regVecEquiv` identifies Boolean registers with
vectors over GF(2), while `amplitudeFn` and `stateOfFn` transport amplitudes between these
coordinates.

The definitions `stabilizerProjector`, `pauliBranchProjector`, and `feedbackTableau` provide the
algebraic data for stabilizer projection and measurement updates. The binary description follows
the stabilizer formalism of [DehaeneDeMoor2003]; the definition `ConsistentTableau` requires
Hermitian decoded rows and pairwise commuting matrices.

## Main statements

* `regVecEquiv`: equivalence between register and binary vector coordinates.
* `stabilizerProjector`: ordered product of factors `(1 + op g) / 2`.
* `pauliBranchProjector`: positive and negative Pauli branch expressions.
* `feedbackTableau`: replacement of one row by the branch-dependent measurement row.
* `zCanonicalTableau`: canonical tableau of single-site Z generators.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

/-- Convert a Boolean register to a vector over GF(2) by applying `boolZModEquiv` at each site. -/
def regToVec {n : ℕ} (r : Reg n) : BooleanVec n :=
  fun i => Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (r i)

/-- Convert a vector over GF(2) to a Boolean register using the inverse of `boolZModEquiv` at
each site. -/
def vecToReg {n : ℕ} (v : BooleanVec n) : Reg n :=
  fun i => Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm (v i)

/-- The equivalence between Boolean registers and vectors over GF(2) given by `regToVec` and
`vecToReg`. -/
def regVecEquiv {n : ℕ} : Reg n ≃ BooleanVec n where
  toFun := regToVec
  invFun := vecToReg
  left_inv := fun r => by
    funext i
    exact Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm_apply_apply (r i)
  right_inv := fun v => by
    funext i
    exact Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.apply_symm_apply (v i)

/-- Express the amplitudes of a register state in binary vector coordinates by precomposing with
`vecToReg`. -/
def amplitudeFn {n : ℕ} (ψ : QState (Reg n)) : BooleanVec n → ℂ :=
  fun x => ψ (vecToReg x)

/-- Interpret a complex function on binary vectors as register amplitudes by precomposing with
`regToVec`. -/
def stateOfFn {n : ℕ} (f : BooleanVec n → ℂ) : QState (Reg n) :=
  fun r => f (regToVec r)

/-- The Pauli element has phase zero or two, so its global scalar is a real sign. -/
def IsHermitianPauli {n : ℕ} (p : PauliElem n) : Prop :=
  p.phase = 0 ∨ p.phase = 2

/-- The binary symplectic pairing of the words of two Pauli elements is zero. -/
def pauliCommute {n : ℕ} (p q : PauliElem n) : Prop :=
  symplecticForm (symplecticX p.word, symplecticZ p.word)
    (symplecticX q.word, symplecticZ q.word) = 0

/-- The Pauli elements decoded from two tableau rows have zero binary symplectic pairing. -/
def rowsCommute {n : ℕ} (r s : Row n) : Prop :=
  pauliCommute r.decode s.decode

/-- The pair of binary X and Z coordinate vectors of the Pauli word decoded from a tableau row. -/
def rowSymp {n : ℕ} (r : Row n) : BooleanVec n × BooleanVec n :=
  (symplecticX r.decode.word, symplecticZ r.decode.word)

/-- The set of finite products of elements from `gs`, allowing repetitions and the empty
product. -/
def generatedGroup {n : ℕ} (gs : List (PauliElem n)) : Set (PauliElem n) :=
  { p | ∃ l : List (PauliElem n), (∀ g ∈ l, g ∈ gs) ∧ l.foldl PauliElem.mul 1 = p }

/-- Multiply the generators selected by the Boolean mask in increasing index order, with
identity for the empty selection. -/
def maskedProduct {n k : ℕ} (gs : Fin k → PauliElem n) (mask : Fin k → Bool) : PauliElem n :=
  (Finset.sort (Finset.univ : Finset (Fin k))).foldr
    (fun i acc => if mask i then (gs i).mul acc else acc) (1 : PauliElem n)

/-- Retrieve the Pauli generator at the given index of `gs`. -/
def generatorAt {n : ℕ} (gs : List (PauliElem n)) (i : Fin gs.length) : PauliElem n :=
  gs.getD i.1 (1 : PauliElem n)

/-- Recursively form the ordered product of factors `(1 + op g) / 2`, starting from the identity
matrix. -/
noncomputable def projectorAux {n : ℕ} : List (PauliElem n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => ((2 : ℂ)⁻¹) • (projectorAux gs + op g * projectorAux gs)

/-- The ordered product of the matrices `(1 + op g) / 2` for the listed Pauli elements, defined
by `projectorAux`. -/
noncomputable def stabilizerProjector {n : ℕ} (gs : List (PauliElem n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  projectorAux gs

/-- The matrix `(1 + op p) / 2` for branch `true`, and `(1 - op p) / 2` for branch `false`. -/
noncomputable def pauliBranchProjector {n : ℕ} (p : PauliElem n) (b : Bool) :
    Matrix (Reg n) (Reg n) ℂ :=
  match b with
  | true => ((2 : ℂ)⁻¹) • (1 + op p)
  | false => ((2 : ℂ)⁻¹) • (1 - op p)

/-- The distribution on Boolean values assigning probability one half to each value. -/
noncomputable def fairBitLaw : FinDist Bool where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by norm_num

/-- Every listed Pauli element has phase zero or two, and their matrix interpretations commute
pairwise. -/
def CommutingHermitianPaulis {n : ℕ} (gs : List (PauliElem n)) : Prop :=
  (∀ h ∈ gs, IsHermitianPauli h) ∧
    (∀ h ∈ gs, ∀ k ∈ gs, op h * op k = op k * op h)

/-- The list of Pauli elements obtained by decoding the tableau rows in index order. -/
def tableauGenerators {n m : ℕ} (t : Tableau n m) : List (PauliElem n) :=
  (List.finRange m).map (fun a : Fin m => (t a).decode)

/-- Every decoded tableau row has phase zero or two, and the decoded row matrices commute
pairwise. -/
def ConsistentTableau {n m : ℕ} (t : Tableau n m) : Prop :=
  (∀ a, IsHermitianPauli (t a).decode) ∧
    (∀ a b, op (t a).decode * op (t b).decode = op (t b).decode * op (t a).decode)

/-- The tableau row with zero X and Z coordinates and phase two, representing negative identity. -/
def minusIRow (n : ℕ) : Row n := ⟨fun _ => false, fun _ => false, 2⟩

/-- Encode `p` when `b` is `true`; when `b` is `false`, multiply its encoding by the negative
identity row. -/
def feedbackRow {n : ℕ} (p : PauliElem n) (b : Bool) : Row n :=
  if b then encode p else (encode p).mul (minusIRow n)

/-- Replace row `a` of `t` by `feedbackRow p b`, leaving every other row unchanged. -/
def feedbackTableau {n m : ℕ} (t : Tableau n m) (a : Fin m) (p : PauliElem n) (b : Bool) :
    Tableau n m :=
  fun a' => if a' = a then feedbackRow p b else t a'

/-- The tableau whose `m` rows are the phase-zero single-site Z generators on the first `m` of
`n` sites. -/
def zCanonicalTableau (n m : ℕ) (h : m ≤ n) : Tableau n m :=
  fun a => ⟨fun _ => false, fun k => decide (k = Fin.castLE h a), 0⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra
