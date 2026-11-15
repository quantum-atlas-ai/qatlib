/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.CompressedOracleBounds
public import Qatlib.Concepts.BosonFock.BosonOperators.Basic
public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
public import Qatlib.Concepts.FreshFallback.BitScanLedger.ClassicalOracleWitnessBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs

open Matrix
open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open scoped BigOperators ComplexOrder

noncomputable instance instFockBasisFintype (N t : ℕ) : Fintype (FockBasis N t) :=
  inferInstanceAs (Fintype {v : Fin N → Fin (t + 1) // ∑ i, (v i : ℕ) = t})

noncomputable instance instFockBasisDecidableEq (N t : ℕ) : DecidableEq (FockBasis N t) :=
  fun a b => Classical.propDecidable (a = b)

abbrev MomentumBasis (n ℓ : ℕ) :=
  {w : Reg n → Fin (ℓ + 1) // ∑ x, (w x : ℕ) = ℓ}

noncomputable instance instMomentumBasisFintype (n ℓ : ℕ) : Fintype (MomentumBasis n ℓ) :=
  inferInstanceAs (Fintype {w : Reg n → Fin (ℓ + 1) // ∑ x, (w x : ℕ) = ℓ})

instance instMomentumBasisDecidableEq (n ℓ : ℕ) : DecidableEq (MomentumBasis n ℓ) :=
  inferInstanceAs (DecidableEq {w : Reg n → Fin (ℓ + 1) // ∑ x, (w x : ℕ) = ℓ})

def zeroMode (n : ℕ) : Reg n := fun _ => false

def momentumOccupation {n ℓ : ℕ} (u : MomentumBasis n ℓ) (x : Reg n) : ℕ :=
  (u.1 x : ℕ)

noncomputable def fockNumber (N t : ℕ) (x : Fin N) :
    Matrix (FockBasis N t) (FockBasis N t) ℂ :=
  Matrix.of fun p q => if p = q then Complex.ofReal ((p.1 x : ℕ)) else 0

noncomputable def fockOccupied (N t : ℕ) (x : Fin N) :
    Matrix (FockBasis N t) (FockBasis N t) ℂ :=
  Matrix.of fun p q => if p = q then (if p.1 x ≠ 0 then 1 else 0) else 0

noncomputable def fockGuessesOccupied {N t v : ℕ} (z : Fin v → Fin N) :
    Matrix (FockBasis N t) (FockBasis N t) ℂ :=
  Matrix.of fun p q => if p = q then (if ∀ i, p.1 (z i) ≠ 0 then 1 else 0) else 0

noncomputable def momentumNumber (n ℓ : ℕ) (x : Reg n) :
    Matrix (MomentumBasis n ℓ) (MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p => Complex.ofReal (momentumOccupation p x)

def condensate (n ℓ r : ℕ) (u : MomentumBasis n ℓ) : Prop :=
  ℓ ≤ momentumOccupation u (zeroMode n) + r

def quasiEven (n ℓ o : ℕ) (u : MomentumBasis n ℓ) : Prop :=
  ((Finset.univ.filter fun x : Reg n => x ≠ zeroMode n).filter
      fun x => momentumOccupation u x % 2 = 1).card ≤ o

def quasiEvenCondensate (n ℓ r o : ℕ) (u : MomentumBasis n ℓ) : Prop :=
  condensate n ℓ r u ∧ quasiEven n ℓ o u

instance instDecidableCondensate (n ℓ r : ℕ) (u : MomentumBasis n ℓ) :
    Decidable (condensate n ℓ r u) := by unfold condensate; infer_instance

instance instDecidableQuasiEven (n ℓ o : ℕ) (u : MomentumBasis n ℓ) :
    Decidable (quasiEven n ℓ o u) := by unfold quasiEven; infer_instance

instance instDecidableQuasiEvenCondensate (n ℓ r o : ℕ) (u : MomentumBasis n ℓ) :
    Decidable (quasiEvenCondensate n ℓ r o u) := by
  unfold quasiEvenCondensate; infer_instance

noncomputable def conProjector (n ℓ r : ℕ) : Matrix (MomentumBasis n ℓ) (MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p => if condensate n ℓ r p then 1 else 0

noncomputable def qeProjector (n ℓ o : ℕ) : Matrix (MomentumBasis n ℓ) (MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p => if quasiEven n ℓ o p then 1 else 0

noncomputable def qecProjector (n ℓ r o : ℕ) : Matrix (MomentumBasis n ℓ) (MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p => if quasiEvenCondensate n ℓ r o p then 1 else 0

abbrev GuessSpace (n v : ℕ) := Fin v → Reg n

noncomputable def lambdaSucc (n ℓ v : ℕ) :
    Matrix (MomentumBasis n ℓ) (MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p =>
    ∑ z : GuessSpace n v, if Function.Injective z then
      ∏ i, Complex.ofReal (momentumOccupation p (z i))
    else 0

noncomputable def lambdaSuccWeight (n ℓ v : ℕ) (z : GuessSpace n v)
    (u : MomentumBasis n ℓ) : ℝ :=
  if Function.Injective z then ∏ i, (momentumOccupation u (z i) : ℝ) else 0

noncomputable def lambdaSuccFull (n ℓ v : ℕ) :
    Matrix (GuessSpace n v × MomentumBasis n ℓ) (GuessSpace n v × MomentumBasis n ℓ) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.2 = q.2 then
      Complex.ofReal (lambdaSuccWeight n ℓ v p.1 p.2)
    else 0

noncomputable def qecProjectorFull (n ℓ r o v : ℕ) :
    Matrix (GuessSpace n v × MomentumBasis n ℓ) (GuessSpace n v × MomentumBasis n ℓ) ℂ :=
  Matrix.diagonal fun p => if quasiEvenCondensate n ℓ r o p.2 then 1 else 0

def momentumOccupiedModes {n ℓ : ℕ} (u : MomentumBasis n ℓ) : Finset (Reg n) :=
  Finset.univ.filter fun x => momentumOccupation u x ≠ 0

def momentumDistance {n ℓ : ℕ} (u w : MomentumBasis n ℓ) : ℝ :=
  ∑ x, |(momentumOccupation u x : ℝ) - (momentumOccupation w x : ℝ)|

abbrev QuerySchedule (N : ℕ) := List (Fin N)

def listCount {α : Type} [DecidableEq α] (x : α) : List α → ℕ
  | [] => 0
  | a :: l => (if a = x then 1 else 0) + listCount x l

def scheduleOccupation {N : ℕ} (sch : QuerySchedule N) (x : Fin N) : ℕ :=
  listCount x sch

def fockCreation {N : ℕ} (x : Fin N) (v : Fin N → ℕ) : Fin N → ℕ :=
  fun y => if y = x then v y + 1 else v y

def ValuedDatabase (I V : Type) := I → Option V

def valuedSupport {I V : Type} [Fintype I] [DecidableEq I] (db : ValuedDatabase I V) : Finset I :=
  Finset.univ.filter fun x => (db x).isSome

def valueCollision {I V : Type} [Fintype I] [DecidableEq I] (db : ValuedDatabase I V) : Prop :=
  ∃ x y : I, x ≠ y ∧ ∃ v : V, db x = some v ∧ db y = some v

def newElement {I V : Type} [Fintype I] [DecidableEq I] (db : ValuedDatabase I V) (x : I) (v : V) : Prop :=
  db x = some v ∧ ∀ y, y ≠ x → db y ≠ some v

def booleanValuedDatabase {I : Type} (d : I → Bool) : ValuedDatabase I Bool :=
  fun x => if d x then some true else none

abbrev MomentumFock (n ℓ : ℕ) := Qatlib.Concepts.BosonFock.BosonOperators.Occupation (2 ^ n) ℓ

def momentumMode (n : ℕ) (x : Fin (2 ^ n)) : Reg n := (bitVecEquiv n).symm x

def hadamardFock (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  relabelGate (bitVecEquiv n) (HadamardN n)

noncomputable def momentumCreation (n ℓ : ℕ) (y : Fin (2 ^ n)) :
    Matrix (MomentumFock n (ℓ + 1)) (MomentumFock n ℓ) ℂ :=
  ∑ x, hadamardFock n x y • Qatlib.Concepts.BosonFock.BosonOperators.create (2 ^ n) ℓ x

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
