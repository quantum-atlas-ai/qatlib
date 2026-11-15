/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
public import Qatlib.Concepts.BosonFock.BosonOperators.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.BosonFock.BosonOperators

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

def fibreCount {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) : ℕ :=
  (Finset.univ.filter (fun i => f i = x)).card

/-- Each fibre of a placement has cardinality at most its domain size. -/
theorem fibreCount_le {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) : fibreCount f x ≤ t := by
  have h : (Finset.univ.filter (fun i => f i = x)).card ≤ (Finset.univ : Finset (Fin t)).card :=
    Finset.card_le_univ _
  simpa [fibreCount] using! h

/-- The sum of all fibre counts of a placement equals its domain size. -/
theorem fibreCount_sum {N t : ℕ} (f : Fin t → Fin N) : ∑ x : Fin N, fibreCount f x = t := by
  classical
  have h : ∀ x : Fin N, fibreCount f x = ∑ i : Fin t, if f i = x then 1 else 0 := by
    intro x
    rw [fibreCount, Finset.card_eq_sum_ones]
    simp
  calc (∑ x : Fin N, fibreCount f x)
      = ∑ x : Fin N, ∑ i : Fin t, if f i = x then 1 else 0 := by simp_rw [h]
    _ = ∑ i : Fin t, ∑ x : Fin N, if f i = x then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ i : Fin t, 1 := by
      apply Fintype.sum_congr
      intro i
      show (∑ x ∈ (Finset.univ : Finset (Fin N)), (if f i = x then 1 else 0)) = 1
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro b _ hb
        rw [ite_eq_right (fun he => hb he.symm)]
      · intro h
        exact (h (Finset.mem_univ (f i))).elim
    _ = t := by simp

def placementProfile {N t : ℕ} (f : Fin t → Fin N) : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t :=
  ⟨fun x => ⟨fibreCount f x, Nat.lt_succ_of_le (fibreCount_le f x)⟩, by
    simpa using! (fibreCount_sum f)⟩

def profileOf {N t : ℕ} (k : Fin N → ℕ) (hk : ∑ x : Fin N, k x = t) :
    Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t :=
  ⟨fun x =>
    ⟨k x, Nat.lt_succ_of_le (by
      have h1 := Finset.single_le_sum (f := fun i => k i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)
      have h2 : k x ≤ ∑ x : Fin N, k x := h1
      omega)⟩, by simpa using! hk⟩

noncomputable def uniformMultisetProb (N t : ℕ) (v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) : ℝ :=
  (Nat.multinomial (Finset.univ : Finset (Fin N)) (fun x => (v.1 x : ℕ))) / (N : ℝ) ^ t

def uniformMultisetSupport {N t : ℕ} (v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) : Prop :=
  ∑ x : Fin N, (v.1 x : ℕ) = t

def uniformMultisetLaw {N t : ℕ} (f : Fin t → Fin N) : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t :=
  placementProfile f

def realisedOracle {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) : Bool :=
  decide (0 < fibreCount f x)

def multisetSuccess {N t v : ℕ} (z : Fin v → Fin N) (f : Fin t → Fin N) : Prop :=
  ∀ i, 0 < fibreCount f (z i)

noncomputable def multisetSuccessProb (N t v : ℕ) (z : Fin v → Fin N) : ℝ :=
  ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
    (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w

def duplicateValueQuery {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    (db : ValuedDatabase I V) (x : I) (v : V) : Prop :=
  db x = some v ∧ ∃ y : I, y ≠ x ∧ db y = some v

def valuedUpdate {I V : Type} [DecidableEq I] (db : ValuedDatabase I V) (x : I) (v : V) :
    ValuedDatabase I V :=
  fun y => if y = x then some v else db y

def decompressBlock {N t : ℕ} (p : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    ValuedDatabase (Fin N) Bool :=
  booleanValuedDatabase (fun x => decide (0 < (p.1 x : ℕ)))

def compressBlock {N : ℕ} (db : ValuedDatabase (Fin N) Bool) :
    Qatlib.Concepts.BosonFock.BosonOperators.Occupation N (∑ x : Fin N, (if db x = some true then 1 else 0)) :=
  ⟨fun x => ⟨if db x = some true then 1 else 0, by
      have h1 := Finset.single_le_sum (f := fun i => (if db i = some true then 1 else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
      have h2 : (if db x = some true then 1 else 0)
          ≤ ∑ x : Fin N, (if db x = some true then 1 else 0) := h1
      have h3 : (if db x = some true then 1 else 0) ≤ 1 := by split <;> omega
      omega⟩, by rfl⟩

def placementCompressedRegister {N t : ℕ} (f : Fin t → Fin N) :
    Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t :=
  ⟨fun x => ⟨scheduleOccupation (List.ofFn f) x, by
      have h1 := scheduleOccupation_le (List.ofFn f) x
      have h2 : scheduleOccupation (List.ofFn f) x ≤ t := by
        rw [List.length_ofFn] at h1
        exact h1
      omega⟩, by
    have h := scheduleOccupation_total (List.ofFn f)
    rw [List.length_ofFn] at h
    exact h⟩

/-- Each entry of a placement's compressed register is the occupation of that mode in its
associated schedule. -/
theorem placementCompressedRegister_val {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    ((placementCompressedRegister f).1 x : ℕ)
      = scheduleOccupation (List.ofFn f) x := rfl

def avoidWeight {N : ℕ} (T : Finset (Fin N)) (f : Fin N → ℕ) : ℝ :=
  if ∀ x ∈ T, f x = 0 then 1 else 0

noncomputable def multisetAvoidProb (N t : ℕ) (T : Finset (Fin N)) : ℝ :=
  Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
    (fun v => avoidWeight T (fun x => (v.1 x : ℕ)) * uniformMultisetProb N t v)

def queryRecord {N : ℕ} (l : List (Fin N)) : ValuedDatabase (Fin N) Bool :=
  fun x => if x ∈ l then some true else none

def recordQuery {N : ℕ} (db : ValuedDatabase (Fin N) Bool) (x : Fin N) :
    ValuedDatabase (Fin N) Bool :=
  valuedUpdate db x true

def registerOccupation {N : ℕ} (sch : QuerySchedule N) : Fin N → ℕ :=
  fun x => ((scheduleProfile sch).1 x : ℕ)

noncomputable def positionPerQueryNorm (_N t : ℕ) : ℝ := (t : ℝ)

noncomputable def positionMultiQueryBound (N t q : ℕ) : ℝ :=
  positionPerQueryNorm N t ^ q

def positionMultiQueryRecurrence (N t : ℕ) : Prop :=
  positionMultiQueryBound N t 0 = 1 ∧
    ∀ q : ℕ, positionMultiQueryBound N t (q + 1)
      = positionPerQueryNorm N t * positionMultiQueryBound N t q

abbrev PrefixBasis (N k : ℕ) := Fin k → Fin N

noncomputable def uniformPrefixState (N k : ℕ) : Qatlib.Foundations.PureStateMath.QState (PrefixBasis N k) :=
  fun _ => Complex.ofReal (Real.sqrt ((N ^ k : ℕ) : ℝ)⁻¹)

def prefixAvoidFinset (N k : ℕ) (T : Finset (Fin N)) : Finset (PrefixBasis N k) :=
  Fintype.piFinset (fun _ => (Finset.univ : Finset (Fin N)) \ T)

def occupiedModeCount {N t : ℕ} (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun x => 0 < (w.1 x : ℕ))).card

noncomputable def multisetOccupiedProb (N t : ℕ) (x : Fin N) : ℝ :=
  1 - multisetAvoidProb N t {x}

noncomputable def coupledOccupiedProb (N t k : ℕ) : ℝ :=
  ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
    uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k

noncomputable def randomGuessSuccessProb (N t v : ℕ) : ℝ :=
  ∑ z : Fin v → Fin N, ((N : ℝ) ^ v)⁻¹ * multisetSuccessProb N t v z

def oracleCollision {n : ℕ} (S U : Reg n → Bool) (x y : Reg n) : Prop :=
  S x = U x ∧ S y = U y ∧ x ≠ y

open Classical in

def collisionPositions {n : ℕ} (S U : Reg n → Bool) : Finset (Reg n) :=
  Finset.univ.filter fun x => ∃ y : Reg n, oracleCollision S U x y

def collisionSuccessEvent {n : ℕ} (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) : Finset (ForrSpace n W) :=
  Finset.univ.filter fun p : ForrSpace n W => p.1.1 ∈ collisionPositions S U

end Qatlib.Papers.QMAvsQCMA25.Forrelation
