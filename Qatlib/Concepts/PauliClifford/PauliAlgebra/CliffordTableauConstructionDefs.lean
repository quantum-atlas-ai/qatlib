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
set_option warningAsError false
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

def regToVec {n : ℕ} (r : Reg n) : BooleanVec n :=
  fun i => Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (r i)

def vecToReg {n : ℕ} (v : BooleanVec n) : Reg n :=
  fun i => Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm (v i)

def regVecEquiv {n : ℕ} : Reg n ≃ BooleanVec n where
  toFun := regToVec
  invFun := vecToReg
  left_inv := fun r => by
    funext i
    exact Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm_apply_apply (r i)
  right_inv := fun v => by
    funext i
    exact Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.apply_symm_apply (v i)

def amplitudeFn {n : ℕ} (ψ : QState (Reg n)) : BooleanVec n → ℂ :=
  fun x => ψ (vecToReg x)

def stateOfFn {n : ℕ} (f : BooleanVec n → ℂ) : QState (Reg n) :=
  fun r => f (regToVec r)

def IsHermitianPauli {n : ℕ} (p : PauliElem n) : Prop :=
  p.phase = 0 ∨ p.phase = 2

def pauliCommute {n : ℕ} (p q : PauliElem n) : Prop :=
  symplecticForm (symplecticX p.word, symplecticZ p.word)
    (symplecticX q.word, symplecticZ q.word) = 0

def rowsCommute {n : ℕ} (r s : Row n) : Prop :=
  pauliCommute r.decode s.decode

def rowSymp {n : ℕ} (r : Row n) : BooleanVec n × BooleanVec n :=
  (symplecticX r.decode.word, symplecticZ r.decode.word)

def generatedGroup {n : ℕ} (gs : List (PauliElem n)) : Set (PauliElem n) :=
  { p | ∃ l : List (PauliElem n), (∀ g ∈ l, g ∈ gs) ∧ l.foldl PauliElem.mul 1 = p }

def maskedProduct {n k : ℕ} (gs : Fin k → PauliElem n) (mask : Fin k → Bool) : PauliElem n :=
  (Finset.sort (Finset.univ : Finset (Fin k))).foldr
    (fun i acc => if mask i then (gs i).mul acc else acc) (1 : PauliElem n)

def generatorAt {n : ℕ} (gs : List (PauliElem n)) (i : Fin gs.length) : PauliElem n :=
  gs.getD i.1 (1 : PauliElem n)

noncomputable def projectorAux {n : ℕ} : List (PauliElem n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => ((2 : ℂ)⁻¹) • (projectorAux gs + op g * projectorAux gs)

noncomputable def stabilizerProjector {n : ℕ} (gs : List (PauliElem n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  projectorAux gs

noncomputable def pauliBranchProjector {n : ℕ} (p : PauliElem n) (b : Bool) :
    Matrix (Reg n) (Reg n) ℂ :=
  match b with
  | true => ((2 : ℂ)⁻¹) • (1 + op p)
  | false => ((2 : ℂ)⁻¹) • (1 - op p)

noncomputable def fairBitLaw : FinDist Bool where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by norm_num

def CommutingHermitianPaulis {n : ℕ} (gs : List (PauliElem n)) : Prop :=
  (∀ h ∈ gs, IsHermitianPauli h) ∧
    (∀ h ∈ gs, ∀ k ∈ gs, op h * op k = op k * op h)

def tableauGenerators {n m : ℕ} (t : Tableau n m) : List (PauliElem n) :=
  (List.finRange m).map (fun a : Fin m => (t a).decode)

def ConsistentTableau {n m : ℕ} (t : Tableau n m) : Prop :=
  (∀ a, IsHermitianPauli (t a).decode) ∧
    (∀ a b, op (t a).decode * op (t b).decode = op (t b).decode * op (t a).decode)

def minusIRow (n : ℕ) : Row n := ⟨fun _ => false, fun _ => false, 2⟩

def feedbackRow {n : ℕ} (p : PauliElem n) (b : Bool) : Row n :=
  if b then encode p else (encode p).mul (minusIRow n)

def feedbackTableau {n m : ℕ} (t : Tableau n m) (a : Fin m) (p : PauliElem n) (b : Bool) :
    Tableau n m :=
  fun a' => if a' = a then feedbackRow p b else t a'

def zCanonicalTableau (n m : ℕ) (h : m ≤ n) : Tableau n m :=
  fun a => ⟨fun _ => false, fun k => decide (k = Fin.castLE h a), 0⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra
