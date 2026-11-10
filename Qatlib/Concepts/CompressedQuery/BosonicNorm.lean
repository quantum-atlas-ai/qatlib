/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.CompressedOracleBounds
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CompressedQuery.CompressOracle

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CompressedQuery.BosonicNorm

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev XorBasis (I W : Type) := (((I × Bool) × W) × (I → Bool))

abbrev JointBasis (I W : Type) (m Q : ℕ) := XorBasis I W × CutBasis m Q

def fockAction (m Q : ℕ) (i : Fin m) (creation : Bool) :
    Matrix (CutBasis m Q) (CutBasis m Q) ℂ :=
  cutWord m Q [(i, creation)]

def queryStep {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) {m Q : ℕ} (i : Fin m) (creation : Bool) :
    Matrix (JointBasis I W m Q) (JointBasis I W m Q) ℂ :=
  TensorGate (databaseXorOracle (I := I) (W := W) p) (fockAction m Q i creation)

def badRecordProjector {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    {m Q : ℕ} (threshold : ℕ) : Matrix (JointBasis I W m Q) (JointBasis I W m Q) ℂ :=
  Matrix.diagonal fun z => if threshold ≤ databaseCard z.1.2 then 1 else 0

def badRecordEvent {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    {m Q : ℕ} (threshold : ℕ) : Finset (JointBasis I W m Q) :=
  Finset.univ.filter fun z => threshold ≤ databaseCard z.1.2

def queryTrajectory {X : Type} [Fintype X] [DecidableEq X]
    (S : Matrix X X ℂ) : ℕ → QState X → QState X
  | 0, v => v
  | n + 1, v => ApplyGate S (queryTrajectory S n v)

theorem phaseQuery_unitary {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    compressedOracle (I := I) (W := W) p ∈ Matrix.unitaryGroup (XorBasis I W) ℂ := by
  have hF : decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact decompressGate_unitary p hp0 hp1
  have hFd : (decompressGate (I := I) p)ᴴ ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hF
  have hphase : jointPhaseOracle (I := I) (W := W) ∈ Matrix.unitaryGroup (XorBasis I W) ℂ :=
    phaseOracle_unitary (fun z : XorBasis I W => z.1.1.2 && z.2 z.1.1.1)
  unfold compressedOracle
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (tensorGate_unitary (Submonoid.one_mem _) hFd) hphase)
    (tensorGate_unitary (Submonoid.one_mem _) hF)

theorem targetH_unitary {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] :
    databaseTargetHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup (XorBasis I W) ℂ := by
  unfold databaseTargetHadamard controlHadamard
  exact tensorGate_unitary
    (tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

theorem physicalQuery_unitary {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p ∈ Matrix.unitaryGroup (XorBasis I W) ℂ := by
  unfold databaseXorOracle
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ targetH_unitary (phaseQuery_unitary p hp0 hp1)) targetH_unitary

theorem physicalQuery_normalized {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : QState (XorBasis I W)) (hv : Normalized v) :
    Normalized (ApplyGate (databaseXorOracle p) v) :=
  normalized_applyGate (physicalQuery_unitary p hp0 hp1) hv

theorem fockAction_norm_le (m Q : ℕ) (i : Fin m) (creation : Bool) :
    ‖fockAction m Q i creation‖ ≤ Real.sqrt Q := by
  have h := (BosonOperators.sector_and_polynomial_norm_bounds).2.2.2 m Q
    [(1, [(i, creation)])]
  simpa [fockAction] using! h

theorem queryStep_norm_le {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m Q : ℕ} (i : Fin m) (creation : Bool) :
    ‖queryStep (I := I) (W := W) (Q := Q) p i creation‖ ≤ Real.sqrt Q := by
  rw [queryStep, l2_norm_tensorGate]
  have hq := l2_norm_unitary_le_one
    (physicalQuery_unitary (I := I) (W := W) p hp0 hp1)
  have hf := fockAction_norm_le m Q i creation
  exact (mul_le_mul hq hf (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem legacyQueryStep_zero_cutoff {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (i : Fin m) (creation : Bool) :
    queryStep (I := I) (W := W) (Q := 0) p i creation = 0 := by
  apply norm_eq_zero.mp
  have h := queryStep_norm_le (I := I) (W := W) (Q := 0) p hp0 hp1 i creation
  exact le_antisymm (by simpa using! h) (norm_nonneg _)

theorem legacyQueryStep_zero_notNormalized {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (i : Fin m) (creation : Bool) (v : QState (JointBasis I W m 0)) :
    ¬ Normalized (ApplyGate (queryStep (I := I) (W := W) (Q := 0) p i creation) v) := by
  rw [legacyQueryStep_zero_cutoff p hp0 hp1 i creation]
  simp [ApplyGate, Normalized]

def legacyCounterexampleBasis : JointBasis (Fin 1) Unit 1 0 :=
  (((((0 : Fin 1), false), ()), fun _ => false), ⟨0, vacuum 1⟩)

theorem legacyQueryStep_counterexample :
    Normalized (Ket legacyCounterexampleBasis) ∧
    ¬ Normalized (ApplyGate (queryStep (I := Fin 1) (W := Unit) (Q := 0)
      0 (0 : Fin 1) true) (Ket legacyCounterexampleBasis)) := by
  exact ⟨normalized_ket _,
      legacyQueryStep_zero_notNormalized 0 (by norm_num) (by norm_num) 0 true _⟩

theorem badRecordProjector_norm_le {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {m Q : ℕ} (threshold : ℕ) :
    ‖badRecordProjector (I := I) (W := W) (m := m) (Q := Q) threshold‖ ≤ 1 := by
  rw [badRecordProjector, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro z
  by_cases h : threshold ≤ databaseCard z.1.2 <;> simp [h]

theorem badRecordProjector_apply {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {m Q : ℕ} (threshold : ℕ)
    (v : QState (JointBasis I W m Q)) (z : JointBasis I W m Q) :
    ApplyGate (badRecordProjector (I := I) (W := W) threshold) v z =
      if threshold ≤ databaseCard z.1.2 then v z else 0 := by
  simp [badRecordProjector, ApplyGate, Matrix.mulVec_diagonal]

theorem badRecordProjector_mass {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {m Q : ℕ} (threshold : ℕ)
    (v : QState (JointBasis I W m Q)) :
    MeasureProb (ApplyGate (badRecordProjector (I := I) (W := W) threshold) v) Finset.univ =
      MeasureProb v (badRecordEvent (I := I) (W := W) threshold) := by
  simp [MeasureProb, BornProb, badRecordEvent, Finset.sum_filter,
    badRecordProjector_apply, apply_ite]

theorem bornMass_eq_norm_sq {X : Type} [Fintype X] [DecidableEq X] (v : QState X) :
    MeasureProb v Finset.univ = ‖toEuclidean_fromVec v‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rfl

theorem queryTrajectory_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (S : Matrix X X ℂ) {c : ℝ} (hS : ‖S‖ ≤ c) (hc : 0 ≤ c) (steps : ℕ)
    (v : QState X) :
    ‖toEuclidean_fromVec (queryTrajectory S steps v)‖ ≤
      c ^ steps * ‖toEuclidean_fromVec v‖ := by
  induction steps with
  | zero => simp [queryTrajectory]
  | succ steps ih =>
      rw [queryTrajectory]
      calc
        ‖toEuclidean_fromVec (ApplyGate S (queryTrajectory S steps v))‖
            ≤ ‖S‖ * ‖toEuclidean_fromVec (queryTrajectory S steps v)‖ :=
          l2_norm_mulVec_fromVec_le _ _
        _ ≤ c * (c ^ steps * ‖toEuclidean_fromVec v‖) :=
          mul_le_mul hS ih (norm_nonneg _) hc
        _ = c ^ (steps + 1) * ‖toEuclidean_fromVec v‖ := by ring

theorem badRecord_single_step_norm {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m Q : ℕ} (i : Fin m) (creation : Bool) (threshold : ℕ)
    (v : QState (JointBasis I W m Q)) :
    ‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
      (ApplyGate (queryStep (I := I) (W := W) p i creation) v))‖ ≤
        Real.sqrt Q * ‖toEuclidean_fromVec v‖ := by
  rw [← applyGate_mul]
  calc
    ‖toEuclidean_fromVec (ApplyGate
        (badRecordProjector (I := I) (W := W) threshold *
          queryStep (I := I) (W := W) p i creation) v)‖
        ≤ ‖badRecordProjector (I := I) (W := W) threshold *
            queryStep (I := I) (W := W) p i creation‖ * ‖toEuclidean_fromVec v‖ :=
      l2_norm_mulVec_fromVec_le _ _
    _ ≤ (‖badRecordProjector (I := I) (W := W) threshold‖ *
          ‖queryStep (I := I) (W := W) p i creation‖) * ‖toEuclidean_fromVec v‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * Real.sqrt Q) * ‖toEuclidean_fromVec v‖ := by
      gcongr
      · exact badRecordProjector_norm_le threshold
      · exact queryStep_norm_le p hp0 hp1 i creation
    _ = Real.sqrt Q * ‖toEuclidean_fromVec v‖ := by ring

theorem badRecord_multi_step_norm {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m Q : ℕ} (i : Fin m) (creation : Bool) (threshold steps : ℕ)
    (v : QState (JointBasis I W m Q)) :
    ‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
      (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v))‖ ≤
        (Real.sqrt Q) ^ steps * ‖toEuclidean_fromVec v‖ := by
  calc
    ‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
        (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v))‖
        ≤ ‖badRecordProjector (I := I) (W := W) threshold‖ *
            ‖toEuclidean_fromVec
              (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)‖ :=
      l2_norm_mulVec_fromVec_le _ _
    _ ≤ 1 * ‖toEuclidean_fromVec
          (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)‖ :=
      mul_le_mul_of_nonneg_right (badRecordProjector_norm_le threshold) (norm_nonneg _)
    _ = ‖toEuclidean_fromVec
          (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)‖ := one_mul _
    _ ≤ (Real.sqrt Q) ^ steps * ‖toEuclidean_fromVec v‖ :=
      queryTrajectory_norm_le _ (queryStep_norm_le p hp0 hp1 i creation)
        (Real.sqrt_nonneg _) steps v

theorem badRecord_multi_step_probability {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m Q : ℕ} (i : Fin m) (creation : Bool) (threshold steps : ℕ)
    (v : QState (JointBasis I W m Q)) :
    MeasureProb (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)
        (badRecordEvent (I := I) (W := W) threshold) ≤
      (Q : ℝ) ^ steps * MeasureProb v Finset.univ := by
  have hnorm := badRecord_multi_step_norm p hp0 hp1 i creation threshold steps v
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hsqrt : ((Real.sqrt (Q : ℝ)) ^ steps) ^ 2 = (Q : ℝ) ^ steps := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg Q)]
  rw [← badRecordProjector_mass]
  calc
    MeasureProb (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
        (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)) Finset.univ
        = ‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
            (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v))‖ ^ 2 :=
      bornMass_eq_norm_sq _
    _ ≤ ((Real.sqrt Q) ^ steps * ‖toEuclidean_fromVec v‖) ^ 2 := hsq
    _ = ((Real.sqrt Q) ^ steps) ^ 2 * MeasureProb v Finset.univ := by
      rw [bornMass_eq_norm_sq]
      ring
    _ = (Q : ℝ) ^ steps * MeasureProb v Finset.univ := by rw [hsqrt]

theorem badRecord_multi_step_probability_normalized {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m Q : ℕ} (i : Fin m) (creation : Bool) (threshold steps : ℕ)
    (v : QState (JointBasis I W m Q)) (hv : Normalized v) :
    MeasureProb (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)
        (badRecordEvent (I := I) (W := W) threshold) ≤ (Q : ℝ) ^ steps := by
  have h := badRecord_multi_step_probability p hp0 hp1 i creation threshold steps v
  have hmass : MeasureProb v Finset.univ = 1 := by
    simpa [MeasureProb, Normalized] using! hv
  rw [hmass, mul_one] at h
  exact h

theorem frontier1 {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m Q : ℕ}
    (i : Fin m) (creation : Bool) (threshold steps : ℕ)
    (v : QState (JointBasis I W m Q)) :
    (‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
        (ApplyGate (queryStep (I := I) (W := W) p i creation) v))‖ ≤
          Real.sqrt Q * ‖toEuclidean_fromVec v‖) ∧
    (‖toEuclidean_fromVec (ApplyGate (badRecordProjector (I := I) (W := W) threshold)
        (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v))‖ ≤
          (Real.sqrt Q) ^ steps * ‖toEuclidean_fromVec v‖) ∧
    (MeasureProb (queryTrajectory (queryStep (I := I) (W := W) p i creation) steps v)
        (badRecordEvent (I := I) (W := W) threshold) ≤
      (Q : ℝ) ^ steps * MeasureProb v Finset.univ) :=
  ⟨badRecord_single_step_norm p hp0 hp1 i creation threshold v,
    badRecord_multi_step_norm p hp0 hp1 i creation threshold steps v,
    badRecord_multi_step_probability p hp0 hp1 i creation threshold steps v⟩

section PhysicalRecords

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def recordProjector (k : ℕ) : Matrix (XorBasis I W) (XorBasis I W) ℂ :=
  Matrix.diagonal fun z => if k ≤ databaseCard z.2 then 1 else 0

def recordLow (k : ℕ) : Matrix (XorBasis I W) (XorBasis I W) ℂ := 1 - recordProjector k

def recordEvent (k : ℕ) : Finset (XorBasis I W) :=
  Finset.univ.filter (fun z => k ≤ databaseCard z.2)

def recordAmplitude (k : ℕ) (v : QState (XorBasis I W)) : ℝ :=
  ‖toEuclidean_fromVec (ApplyGate (recordProjector k) v)‖

theorem recordProjector_norm (k : ℕ) : ‖recordProjector (I := I) (W := W) k‖ ≤ 1 := by
  rw [recordProjector, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro z
  by_cases h : k ≤ databaseCard z.2 <;> simp [h]

omit [Fintype W] in

theorem recordLow_diagonal (k : ℕ) : recordLow (I := I) (W := W) k =
    Matrix.diagonal (fun z => if k ≤ databaseCard z.2 then (0 : ℂ) else 1) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hx : k ≤ databaseCard x.2 <;> simp [recordLow, recordProjector, hx]
  · simp [recordLow, recordProjector, hxy]

theorem recordLow_norm (k : ℕ) : ‖recordLow (I := I) (W := W) k‖ ≤ 1 := by
  rw [recordLow_diagonal, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro z
  by_cases h : k ≤ databaseCard z.2 <;> simp [h]

omit [Fintype W] in

theorem recordProjector_zero : recordProjector (I := I) (W := W) 0 = 1 := by
  ext x y
  simp [recordProjector, Matrix.diagonal_apply, Matrix.one_apply]

theorem recordProjector_apply (k : ℕ) (v : QState (XorBasis I W)) (z : XorBasis I W) :
    ApplyGate (recordProjector k) v z = if k ≤ databaseCard z.2 then v z else 0 := by
  simp [recordProjector, ApplyGate, Matrix.mulVec_diagonal]

theorem recordProjector_mass (k : ℕ) (v : QState (XorBasis I W)) :
    MeasureProb (ApplyGate (recordProjector k) v) Finset.univ = MeasureProb v (recordEvent k) := by
  simp [MeasureProb, BornProb, recordEvent, Finset.sum_filter, recordProjector_apply, apply_ite]

theorem recordEvent_eq_amplitude_sq (k : ℕ) (v : QState (XorBasis I W)) :
    MeasureProb v (recordEvent k) = recordAmplitude k v ^ 2 := by
  rw [← recordProjector_mass, bornMass_eq_norm_sq]
  rfl

omit [Fintype W] in

theorem recordProjector_tensor (k : ℕ) : recordProjector (I := I) (W := W) k =
    TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      (Matrix.diagonal (fun d : I → Bool => if k ≤ databaseCard d then (1 : ℂ) else 0)) := by
  ext ⟨a,d⟩ ⟨b,e⟩
  by_cases ha : a = b <;> by_cases hd : d = e <;>
    simp [recordProjector, TensorGate, ha, hd]

theorem recordProjector_algorithm_commute (k : ℕ) (U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) :
    recordProjector k * TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) =
      TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) * recordProjector k := by
  simp only [recordProjector_tensor, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

theorem recordProjector_targetH_commute (k : ℕ) :
    recordProjector (I := I) (W := W) k * databaseTargetHadamard =
      databaseTargetHadamard * recordProjector k :=
  recordProjector_algorithm_commute k controlHadamard

def recordCoupling (p : ℝ) : ℝ := 2 * Real.sqrt (p * (1 - p))

theorem recordCoupling_nonneg (p : ℝ) : 0 ≤ recordCoupling p :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

def flipDatabase (j : I) (d : I → Bool) : I → Bool := Function.update d j (!(d j))

omit [Fintype I] in

theorem flipDatabase_twice (j : I) (d : I → Bool) : flipDatabase j (flipDatabase j d) = d := by
  funext k
  by_cases hk : k = j
  · subst k; simp [flipDatabase]
  · simp [flipDatabase, hk]

omit [Fintype I] in

theorem flipDatabase_ne (j : I) (d : I → Bool) : d ≠ flipDatabase j d := by
  intro h
  have hh := congrFun h j
  simp [flipDatabase] at hh

omit [Fintype I] in

theorem flipDatabase_off (j : I) (d : I → Bool) (k : I) (hk : k ≠ j) : flipDatabase j d k = d k := by
  simp [flipDatabase, hk]

omit [Fintype I] in

theorem flipDatabase_of_offeq {j : I} {d e : I → Bool}
    (hrest : ∀ k, k ≠ j → d k = e k) (hne : d ≠ e) : d = flipDatabase j e := by
  have hj : d j ≠ e j := by
    intro hj
    apply hne
    funext k
    by_cases hk : k = j
    · simpa only [hk] using! hj
    · exact hrest k hk
  funext k
  by_cases hk : k = j
  · subst k
    simp [flipDatabase]
    cases hd : d j <;> cases he : e j <;> simp_all
  · simpa only [flipDatabase, Function.update_of_ne hk] using! hrest k hk

def recordFlip (z : XorBasis I W) : XorBasis I W :=
  if z.1.1.2 then (z.1, flipDatabase z.1.1.1 z.2) else z

omit [Fintype I] [Fintype W] [DecidableEq W] in

theorem recordFlip_involutive : Function.Involutive (recordFlip (I := I) (W := W)) := by
  rintro ⟨⟨⟨j,b⟩,w⟩,d⟩
  cases b with
  | false => rfl
  | true => change (((j,true),w), flipDatabase j (flipDatabase j d)) = _; rw [flipDatabase_twice]

def recordFlipGate : Matrix (XorBasis I W) (XorBasis I W) ℂ := permMatrix recordFlip

theorem recordFlipGate_unitary : recordFlipGate (I := I) (W := W) ∈ Matrix.unitaryGroup (XorBasis I W) ℂ :=
  permMatrix_unitary recordFlip_involutive

omit [Fintype W] in

theorem recordFlipGate_entry (q q' : (I × Bool) × W) (d e : I → Bool) :
    recordFlipGate (q,d) (q',e) =
      if q = q' then
        if q.1.2 then (if d = flipDatabase q.1.1 e then 1 else 0)
        else if d = e then 1 else 0
      else 0 := by
  by_cases hq : q = q'
  · subst q'
    cases hb : q.1.2 <;> simp [recordFlipGate, permMatrix, recordFlip, hb]
  · cases hb : q'.1.2 <;> simp [recordFlipGate, permMatrix, recordFlip, hb, hq]

end PhysicalRecords

section PhysicalCross

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def phaseDiagonal (p : ℝ) : Matrix (XorBasis I W) (XorBasis I W) ℂ :=
  Matrix.diagonal fun z =>
    if z.1.1.2 then (if z.2 z.1.1.1 then (2 * p - 1 : ℝ) else 1 - 2 * p)
    else (1 - recordCoupling p : ℝ)

theorem phaseQuery_decomposition (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    compressedOracle (I := I) (W := W) p = phaseDiagonal p + (recordCoupling p : ℂ) • recordFlipGate := by
  ext ⟨q,d⟩ ⟨q',e⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, recordFlipGate_entry]
  by_cases hq : q = q'
  · subst q'
    rcases q with ⟨⟨j,b⟩,w⟩
    rw [compressed_oracle_entry p hp0 hp1]
    cases b with
    | false =>
      by_cases hde : d = e
      · subst e
        simp only [phaseDiagonal, Matrix.diagonal_apply, Bool.false_eq_true, if_false]
        push_cast
        ring
      · simp [phaseDiagonal, hde]
    | true =>
      by_cases hde : d = e
      · subst e
        have hf := flipDatabase_ne j d
        cases hd : d j <;>
          simp [phaseDiagonal, hf, compressedQueryEntry, hd, recordCoupling]
      · by_cases hrest : ∀ k, k ≠ j → d k = e k
        · have hf : d = flipDatabase j e := flipDatabase_of_offeq hrest hde
          have hj : d j ≠ e j := by
            rw [hf]
            simp [flipDatabase]
          cases hd : d j <;> cases he : e j <;>
            simp_all [phaseDiagonal, compressedQueryEntry, recordCoupling]
        · have hf : d ≠ flipDatabase j e := by
            intro h
            apply hrest
            intro k hk
            rw [h, flipDatabase_off j e k hk]
          simp [phaseDiagonal, hde, hrest, hf]
  · rw [compressed_oracle_offdiag p q q' d e hq]
    simp [phaseDiagonal, hq]

theorem recordProjector_diagonal_cross (k : ℕ) (d : XorBasis I W → ℂ) :
    recordProjector k * Matrix.diagonal d * recordLow k = 0 := by
  rw [recordLow_diagonal]
  simp only [recordProjector, Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases h : k ≤ databaseCard x.2 <;> simp [Matrix.diagonal_apply, h]

def recordCross (k : ℕ) (Q : Matrix (XorBasis I W) (XorBasis I W) ℂ) :=
  recordProjector k * Q * recordLow k

theorem recordCross_phase (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    recordCross (I := I) (W := W) k (compressedOracle p) =
      (recordCoupling p : ℂ) • (recordProjector k * recordFlipGate * recordLow k) := by
  rw [recordCross, phaseQuery_decomposition p hp0 hp1, Matrix.mul_add, Matrix.add_mul]
  have hdiag : recordProjector (I := I) (W := W) k * phaseDiagonal p * recordLow k = 0 :=
    recordProjector_diagonal_cross k _
  rw [hdiag, zero_add, Matrix.mul_smul, Matrix.smul_mul]

theorem opNorm_mul_contractions {X : Type} [Fintype X] [DecidableEq X] (A B : Matrix X X ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 := by
  calc ‖A * B‖ ≤ ‖A‖ * ‖B‖ := Matrix.l2_opNorm_mul _ _
       _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

end PhysicalCross

section LocalBoson

def singleOccupation (n : ℕ) : Occupation 1 n :=
  ⟨fun _ => ⟨n, Nat.lt_succ_self n⟩, by simp⟩

theorem singleOccupation_unique (n : ℕ) (s : Occupation 1 n) : s = singleOccupation n := by
  apply Subtype.ext
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  apply Fin.ext
  have hs := s.property
  simpa only [Fin.sum_univ_one] using! hs

local instance singleModeUnique (n : ℕ) : Unique (Occupation 1 n) where
  default := singleOccupation n
  uniq := singleOccupation_unique n

def singleModeToBit : CutBasis 1 1 ≃ Bool :=
  (Equiv.sigmaUnique (Fin 2) (fun n => Occupation 1 n.val)).trans boolEquivFin2.symm

theorem singleModeToBit_symm (b : Bool) : singleModeToBit.symm b =
    ⟨boolEquivFin2 b, singleOccupation (boolEquivFin2 b).val⟩ := by
  simp [singleModeToBit]
  exact singleOccupation_unique _ _

def bitCreation : Matrix Bool Bool ℂ := relabelGate singleModeToBit (cutCreate 1 1 0)

theorem bitCreation_entry (a b : Bool) : bitCreation a b = if a && !b then 1 else 0 := by
  change cutCreate 1 1 0 (singleModeToBit.symm a) (singleModeToBit.symm b) = _
  rw [singleModeToBit_symm, singleModeToBit_symm]
  cases a <;> cases b <;>
    simp [cutCreate, singleOccupation, boolEquivFin2]

theorem bitCreation_norm : ‖bitCreation‖ ≤ 1 := by
  rw [bitCreation, l2_norm_relabelGate]
  have h := (BosonOperators.sector_and_polynomial_norm_bounds).2.2.1 1 1 (fun _ => (1 : ℂ))
  simpa using! h

variable {I : Type} [Fintype I] [DecidableEq I]

def databaseRaise (j : I) : Matrix (I → Bool) (I → Bool) ℂ :=
  relabelGate (Equiv.funSplitAt j Bool).symm
    (TensorGate bitCreation (1 : Matrix ({k : I // k ≠ j} → Bool) ({k : I // k ≠ j} → Bool) ℂ))

theorem databaseRaise_norm (j : I) : ‖databaseRaise j‖ ≤ 1 := by
  rw [databaseRaise, l2_norm_relabelGate, l2_norm_tensorGate]
  have hI :=
      l2_norm_unitary_le_one (Submonoid.one_mem (Matrix.unitaryGroup ({k : I // k ≠ j} → Bool) ℂ))
  exact (mul_le_mul bitCreation_norm hI (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end LocalBoson

section FibreNorm

variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def fibreGate (B : A → Matrix D D ℂ) : Matrix (A × D) (A × D) ℂ :=
  fun x y => if x.1 = y.1 then B x.1 x.2 y.2 else 0

omit [DecidableEq D] in

theorem fibreGate_apply (B : A → Matrix D D ℂ) (v : QState (A × D)) (a : A) (d : D) :
    ApplyGate (fibreGate B) v (a,d) = ApplyGate (B a) (fun e => v (a,e)) d := by
  simp [fibreGate, ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem fibreGate_norm_le (B : A → Matrix D D ℂ) (c : ℝ) (hc : 0 ≤ c) (hB : ∀ a, ‖B a‖ ≤ c) :
    ‖fibreGate B‖ ≤ c := by
  apply l2_opNorm_le_of_mulVec_le hc
  intro v
  have hslice (a : A) : MeasureProb (ApplyGate (B a) (fun e => v (a,e))) Finset.univ ≤
      c ^ 2 * MeasureProb (fun e => v (a,e)) Finset.univ := by
    have hn := (l2_norm_mulVec_fromVec_le (B a) (fun e => v (a,e))).trans
      (mul_le_mul_of_nonneg_right (hB a) (norm_nonneg _))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [bornMass_eq_norm_sq, bornMass_eq_norm_sq]
    simpa only [mul_pow] using! hs
  have hwhole : MeasureProb (ApplyGate (fibreGate B) v) Finset.univ ≤ c ^ 2 * MeasureProb v Finset.univ := by
    simp only [MeasureProb, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    simpa only [MeasureProb, BornProb, fibreGate_apply, Finset.mul_sum] using! hslice a
  rw [bornMass_eq_norm_sq, bornMass_eq_norm_sq] at hwhole
  have hn := norm_nonneg (toEuclidean_fromVec (ApplyGate (fibreGate B) v))
  have hi := norm_nonneg (toEuclidean_fromVec v)
  apply (sq_le_sq₀ hn (mul_nonneg hc hi)).mp
  simpa only [mul_pow] using! hwhole

end FibreNorm

section ControlledBoson

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in

theorem databaseRaise_entry (j : I) (d e : I → Bool) :
    databaseRaise j d e = if e j then 0 else if d = flipDatabase j e then 1 else 0 := by
  change bitCreation (d j) (e j) *
    (1 : Matrix ({k : I // k ≠ j} → Bool) ({k : I // k ≠ j} → Bool) ℂ)
      (fun k => d k.val) (fun k => e k.val) = _
  rw [bitCreation_entry, Matrix.one_apply]
  have hr : (fun k : {k : I // k ≠ j} => d k.val) = (fun k => e k.val) ↔
      ∀ k, k ≠ j → d k = e k := by
    constructor
    · intro h k hk; exact congrFun h ⟨k,hk⟩
    · intro h; funext k; exact h k.val k.property
  simp only [hr]
  cases he : e j with
  | true => simp
  | false =>
    cases hd : d j with
    | false =>
      have hf : d ≠ flipDatabase j e := by
        intro h
        have hh := congrFun h j
        simp [flipDatabase, hd, he] at hh
      simp [hf]
    | true =>
      have hf : d = flipDatabase j e ↔ ∀ k, k ≠ j → d k = e k := by
        constructor
        · intro h k hk; rw [h, flipDatabase_off j e k hk]
        · intro h
          apply flipDatabase_of_offeq h
          intro hde
          have hh := congrFun hde j
          simp [hd, he] at hh
      simp [hf]

def recordRaiseGate : Matrix (XorBasis I W) (XorBasis I W) ℂ :=
  fibreGate (fun q : (I × Bool) × W => if q.1.2 then databaseRaise q.1.1 else 0)

theorem recordRaiseGate_norm : ‖recordRaiseGate (I := I) (W := W)‖ ≤ 1 := by
  apply fibreGate_norm_le _ 1 zero_le_one
  intro q
  cases hb : q.1.2 <;> simp only [Bool.false_eq_true, if_false, if_true]
  · simp
  · exact databaseRaise_norm q.1.1

omit [Fintype W] in

theorem recordRaiseGate_entry (q q' : (I × Bool) × W) (d e : I → Bool) :
    recordRaiseGate (q,d) (q',e) =
      if q = q' then
        if q.1.2 then (if e q.1.1 then 0 else if d = flipDatabase q.1.1 e then 1 else 0)
        else 0
      else 0 := by
  by_cases hq : q = q'
  · subst q'
    cases hb : q.1.2 <;> simp [recordRaiseGate, fibreGate, hb, databaseRaise_entry]
  · simp [recordRaiseGate, fibreGate, hq]

omit [Fintype W] [DecidableEq W] in

theorem flipDatabase_support (j : I) (d : I → Bool) :
    databaseSupport (flipDatabase j d) =
      if d j then (databaseSupport d).erase j else insert j (databaseSupport d) := by
  ext k
  by_cases hk : k = j
  · subst k
    cases hd : d j <;> simp [databaseSupport, flipDatabase, hd]
  · cases hd : d j <;> simp [databaseSupport, flipDatabase, hd, hk]

omit [Fintype W] [DecidableEq W] in

theorem flipDatabase_card_true (j : I) (d : I → Bool) (hd : d j = true) :
    databaseCard (flipDatabase j d) + 1 = databaseCard d := by
  have hj : j ∈ databaseSupport d := by simp [databaseSupport, hd]
  have hh := Finset.card_erase_add_one hj
  simpa only [databaseCard, flipDatabase_support, hd, if_true] using! hh

theorem recordCross_flip_raise (k : ℕ) :
    recordProjector (I := I) (W := W) k * recordFlipGate * recordLow k =
      recordProjector k * recordRaiseGate * recordLow k := by
  ext ⟨q,d⟩ ⟨q',e⟩
  simp only [recordProjector, recordLow_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : k ≤ databaseCard d
  · by_cases hy : k ≤ databaseCard e
    · simp [hy]
    · have hde : d ≠ e := by intro h; have hh := congrArg databaseCard h; omega
      by_cases hq : q = q'
      · subst q'
        cases hb : q.1.2 with
        | false => simp [recordFlipGate_entry, recordRaiseGate_entry, hb, hde]
        | true =>
          by_cases hf : d = flipDatabase q.1.1 e
          · have he : e q.1.1 = false := by
              cases he : e q.1.1 with
              | false => rfl
              | true =>
                have hcard := flipDatabase_card_true q.1.1 e he
                rw [← hf] at hcard
                omega
            simp [recordFlipGate_entry, recordRaiseGate_entry, hb, hf, he]
          · simp [recordFlipGate_entry, recordRaiseGate_entry, hb, hf]
      · simp [recordFlipGate_entry, recordRaiseGate_entry, hq]
  · simp [hx]

theorem phaseCross_bosonic_norm (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖recordCross (I := I) (W := W) k (compressedOracle p)‖ ≤ recordCoupling p := by
  rw [recordCross_phase k p hp0 hp1, recordCross_flip_raise, norm_smul]
  have hc : ‖(recordCoupling p : ℂ)‖ = recordCoupling p := by
    simp [Complex.norm_real, abs_of_nonneg (recordCoupling_nonneg p)]
  rw [hc]
  have hraise := recordRaiseGate_norm (I := I) (W := W)
  have hP := recordProjector_norm (I := I) (W := W) k
  have hL := recordLow_norm (I := I) (W := W) k
  have hh := opNorm_mul_contractions _ _ (opNorm_mul_contractions _ _ hP hraise) hL
  exact (mul_le_mul_of_nonneg_left hh (recordCoupling_nonneg p)).trans_eq (mul_one _)

end ControlledBoson

section PhysicalCross

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem recordCross_phase_norm (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖recordCross (I := I) (W := W) k (compressedOracle p)‖ ≤ recordCoupling p :=
  phaseCross_bosonic_norm k p hp0 hp1

theorem recordLow_targetH_commute (k : ℕ) :
    recordLow (I := I) (W := W) k * databaseTargetHadamard = databaseTargetHadamard * recordLow k := by
  simp only [recordLow, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    recordProjector_targetH_commute]

theorem recordCross_xor_eq (k : ℕ) (p : ℝ) :
    recordCross (I := I) (W := W) k (databaseXorOracle p) =
      databaseTargetHadamard * recordCross k (compressedOracle p) * databaseTargetHadamard := by
  unfold recordCross databaseXorOracle
  calc
    recordProjector k * (databaseTargetHadamard * compressedOracle p * databaseTargetHadamard) * recordLow k =
        (recordProjector k * databaseTargetHadamard) * compressedOracle p * (databaseTargetHadamard * recordLow k) := by noncomm_ring
    _ = (databaseTargetHadamard * recordProjector k) * compressedOracle p * (recordLow k * databaseTargetHadamard) := by
      rw [recordProjector_targetH_commute, recordLow_targetH_commute]
    _ = databaseTargetHadamard * (recordProjector k * compressedOracle p * recordLow k) * databaseTargetHadamard := by noncomm_ring

theorem recordCross_xor_norm (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖recordCross (I := I) (W := W) k (databaseXorOracle p)‖ ≤ recordCoupling p := by
  rw [recordCross_xor_eq]
  have hH := l2_norm_unitary_le_one (targetH_unitary (I := I) (W := W))
  have hC := recordCross_phase_norm (I := I) (W := W) k p hp0 hp1
  calc
    ‖databaseTargetHadamard * recordCross k (compressedOracle p) * databaseTargetHadamard‖ ≤
        (‖databaseTargetHadamard (I := I) (W := W)‖ * ‖recordCross k (compressedOracle p)‖) *
          ‖databaseTargetHadamard (I := I) (W := W)‖ := by
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * recordCoupling p) * 1 :=
      mul_le_mul (mul_le_mul hH hC (norm_nonneg _) zero_le_one) hH (norm_nonneg _)
        (by simpa only [one_mul] using! recordCoupling_nonneg p)
    _ = recordCoupling p := by ring

end PhysicalCross

section PhysicalRecurrence

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem physicalQuery_card_step (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x y : XorBasis I W) (h : databaseXorOracle p x y ≠ 0) :
    databaseCard x.2 ≤ databaseCard y.2 + 1 := by
  rcases x with ⟨⟨⟨j,b⟩,w⟩,d⟩
  rcases y with ⟨⟨⟨j',a⟩,w'⟩,e⟩
  by_cases hj : j = j'
  · subst j'
    by_cases hw : w = w'
    · subst w'
      exact databaseXorOracle_card_step p hp0 hp1 j b a w d e h
    · exact False.elim (h (databaseXorOracle_offblock p j j b a w w' d e (Or.inr hw)))
  · exact False.elim (h (databaseXorOracle_offblock p j j' b a w w' d e (Or.inl hj)))

theorem recordCross_crop (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    recordCross (I := I) (W := W) (k + 1) (databaseXorOracle p) =
      recordCross (k + 1) (databaseXorOracle p) * recordProjector k := by
  ext x y
  simp only [recordCross, recordProjector, recordLow_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  by_cases hy : k ≤ databaseCard y.2
  · simp [hy]
  · by_cases hx : k + 1 ≤ databaseCard x.2
    · have hz : databaseXorOracle p x y = 0 := by
        by_contra hz
        have hh := physicalQuery_card_step p hp0 hp1 x y hz
        omega
      simp [hz]
    · simp [hx]

theorem recordCross_decompose (k : ℕ) (Q : Matrix (XorBasis I W) (XorBasis I W) ℂ) :
    recordProjector k * Q = recordProjector k * Q * recordProjector k + recordCross k Q := by
  unfold recordCross recordLow
  noncomm_ring

theorem physicalQuery_amplitude_recurrence (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (XorBasis I W)) :
    recordAmplitude (k + 1) (ApplyGate (databaseXorOracle p) v) ≤
      recordAmplitude (k + 1) v + recordCoupling p * recordAmplitude k v := by
  let P : Matrix (XorBasis I W) (XorBasis I W) ℂ := recordProjector (k + 1)
  let Q := databaseXorOracle (I := I) (W := W) p
  let C := recordCross (I := I) (W := W) (k + 1) Q
  have hPQ : ‖P * Q‖ ≤ 1 := opNorm_mul_contractions _ _
    (recordProjector_norm _) (l2_norm_unitary_le_one (physicalQuery_unitary p hp0 hp1))
  have hhigh : ‖toEuclidean_fromVec (ApplyGate (P * Q * P) v)‖ ≤ recordAmplitude (k + 1) v := by
    rw [applyGate_mul]
    exact (l2_norm_mulVec_fromVec_le _ _).trans
      ((mul_le_mul_of_nonneg_right hPQ (norm_nonneg _)).trans_eq (one_mul _))
  have hlow : ‖toEuclidean_fromVec (ApplyGate C v)‖ ≤ recordCoupling p * recordAmplitude k v := by
    have hcrop : C = C * recordProjector k := recordCross_crop k p hp0 hp1
    have hv : ApplyGate C v = ApplyGate C (ApplyGate (recordProjector k) v) := by
      rw [← applyGate_mul, ← hcrop]
    rw [hv]
    exact (l2_norm_mulVec_fromVec_le _ _).trans
      (mul_le_mul_of_nonneg_right (recordCross_xor_norm (k + 1) p hp0 hp1) (norm_nonneg _))
  have hvec : ApplyGate (P * Q) v = ApplyGate (P * Q * P) v + ApplyGate C v := by
    have hm : P * Q = P * Q * P + C := recordCross_decompose (k + 1) Q
    exact (congrArg (fun M : Matrix (XorBasis I W) (XorBasis I W) ℂ => ApplyGate M v) hm).trans
      (Matrix.add_mulVec (P * Q * P) C v)
  change ‖toEuclidean_fromVec (ApplyGate P (ApplyGate Q v))‖ ≤ _
  rw [← applyGate_mul, hvec]
  change ‖toEuclidean_fromVec (ApplyGate (P * Q * P) v) + toEuclidean_fromVec (ApplyGate C v)‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add hhigh hlow)

theorem recordAmplitude_algorithm_le (k : ℕ)
    (U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ) (v : QState (XorBasis I W)) :
    recordAmplitude k (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) v) ≤ recordAmplitude k v := by
  unfold recordAmplitude
  rw [← applyGate_mul, recordProjector_algorithm_commute, applyGate_mul]
  have hu : TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) ∈ Matrix.unitaryGroup (XorBasis I W) ℂ :=
    tensorGate_unitary hU (Submonoid.one_mem _)
  have ht := l2_norm_unitary_le_one hu
  exact (l2_norm_mulVec_fromVec_le _ _).trans
    ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_eq (one_mul _))

end PhysicalRecurrence

section PhysicalRuns

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

abbrev AlgorithmMatrix (I W : Type) := Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ

def algorithmGatesValid (gates : List (AlgorithmMatrix I W)) : Prop :=
  ∀ U ∈ gates, U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ

def physicalInitial (ψ : QState ((I × Bool) × W)) : QState (XorBasis I W) :=
  TensorState ψ (Ket (fun _ => false))

def physicalRun (p : ℝ) (gates : List (AlgorithmMatrix I W)) (v : QState (XorBasis I W)) : QState (XorBasis I W) :=
  gates.foldl (fun state U => ApplyGate (databaseXorOracle p)
    (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) state)) v

theorem physicalRun_append (p : ℝ) (gates : List (AlgorithmMatrix I W)) (U : AlgorithmMatrix I W)
    (v : QState (XorBasis I W)) :
    physicalRun p (gates ++ [U]) v = ApplyGate (databaseXorOracle p)
      (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) (physicalRun p gates v)) := by
  simp [physicalRun, List.foldl_append]

theorem physicalRun_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (gates : List (AlgorithmMatrix I W)) (hG : algorithmGatesValid gates)
    (v : QState (XorBasis I W)) (hv : Normalized v) : Normalized (physicalRun p gates v) := by
  induction gates generalizing v with
  | nil => exact hv
  | cons U gates ih =>
    have hU := hG U (by simp)
    have htail : algorithmGatesValid gates := fun V hV => hG V (by simp [hV])
    have hu := normalized_applyGate (tensorGate_unitary hU
      (show (1 : Matrix (I → Bool) (I → Bool) ℂ) ∈ Matrix.unitaryGroup (I → Bool) ℂ from Submonoid.one_mem _)) hv
    have hq := physicalQuery_normalized p hp0 hp1 _ hu
    exact ih htail _ hq

theorem normalized_euclidean_norm {X : Type} [Fintype X] [DecidableEq X]
    (v : QState X) (hv : Normalized v) : ‖toEuclidean_fromVec v‖ = 1 := by
  have hm : MeasureProb v Finset.univ = 1 := by simpa [MeasureProb, Normalized] using! hv
  have hs := bornMass_eq_norm_sq v
  have hn := norm_nonneg (toEuclidean_fromVec v)
  nlinarith

theorem recordAmplitude_zero (v : QState (XorBasis I W)) : recordAmplitude 0 v = ‖toEuclidean_fromVec v‖ := by
  simp only [recordAmplitude, recordProjector_zero, applyGate_one]

theorem physicalInitial_normalized (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) :
    Normalized (physicalInitial ψ) := normalized_tensorState hψ (normalized_ket _)

theorem recordAmplitude_initial_pos (k : ℕ) (ψ : QState ((I × Bool) × W)) :
    recordAmplitude (k + 1) (physicalInitial ψ) = 0 := by
  have hz : ApplyGate (recordProjector (k + 1)) (physicalInitial ψ) = 0 := by
    funext z
    rcases z with ⟨q,d⟩
    rw [recordProjector_apply]
    by_cases hd : d = (fun _ => false)
    · subst d
      simp [databaseCard, databaseSupport]
    · simp [physicalInitial, TensorState, Ket, hd]
  simp [recordAmplitude, hz, toEuclidean_fromVec]

theorem physicalRun_binomial (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) :
    ∀ (gates : List (AlgorithmMatrix I W)), algorithmGatesValid gates → ∀ k,
      recordAmplitude k (physicalRun p gates (physicalInitial ψ)) ≤
        (Nat.choose gates.length k : ℝ) * recordCoupling p ^ k := by
  intro gates
  induction gates using List.reverseRecOn with
  | nil =>
    intro _ k
    cases k with
    | zero =>
      rw [show physicalRun p [] (physicalInitial ψ) = physicalInitial ψ from rfl,
        recordAmplitude_zero, normalized_euclidean_norm _ (physicalInitial_normalized ψ hψ)]
      simp
    | succ k =>
      rw [show physicalRun p [] (physicalInitial ψ) = physicalInitial ψ from rfl,
        recordAmplitude_initial_pos]
      simp
  | append_singleton gates U ih =>
    intro hG k
    have htail : algorithmGatesValid gates := fun V hV => hG V (by simp [hV])
    have hU := hG U (by simp)
    have hc := recordCoupling_nonneg p
    cases k with
    | zero =>
      rw [recordAmplitude_zero, normalized_euclidean_norm _
        (physicalRun_normalized p hp0 hp1 (gates ++ [U]) hG _ (physicalInitial_normalized ψ hψ))]
      simp
    | succ k =>
      rw [physicalRun_append]
      have hs := physicalQuery_amplitude_recurrence k p hp0 hp1
        (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) (physicalRun p gates (physicalInitial ψ)))
      have hh := recordAmplitude_algorithm_le (k + 1) U hU (physicalRun p gates (physicalInitial ψ))
      have hl := recordAmplitude_algorithm_le k U hU (physicalRun p gates (physicalInitial ψ))
      have hstep := hs.trans (add_le_add hh (mul_le_mul_of_nonneg_left hl hc))
      calc
        _ ≤ recordAmplitude (k + 1) (physicalRun p gates (physicalInitial ψ)) +
            recordCoupling p * recordAmplitude k (physicalRun p gates (physicalInitial ψ)) := hstep
        _ ≤ (Nat.choose gates.length (k + 1) : ℝ) * recordCoupling p ^ (k + 1) +
            recordCoupling p * ((Nat.choose gates.length k : ℝ) * recordCoupling p ^ k) :=
          add_le_add (ih htail (k + 1)) (mul_le_mul_of_nonneg_left (ih htail k) hc)
        _ = (Nat.choose (gates ++ [U]).length (k + 1) : ℝ) * recordCoupling p ^ (k + 1) := by
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.choose_succ_succ,
              Nat.cast_add]
          rw [pow_succ]
          ring

theorem physicalRun_bad_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ)
    (gates : List (AlgorithmMatrix I W)) (hG : algorithmGatesValid gates) (k : ℕ) :
    MeasureProb (physicalRun p gates (physicalInitial ψ)) (recordEvent k) ≤
      (Nat.choose gates.length k : ℝ) ^ 2 * recordCoupling p ^ (2 * k) := by
  have h := physicalRun_binomial p hp0 hp1 ψ hψ gates hG k
  have hs :=
      pow_le_pow_left₀
      (show 0 ≤ recordAmplitude k (physicalRun p gates (physicalInitial ψ)) from norm_nonneg _) h 2
  rw [recordEvent_eq_amplitude_sq]
  calc
    _ ≤ ((Nat.choose gates.length k : ℝ) * recordCoupling p ^ k) ^ 2 := hs
    _ = (Nat.choose gates.length k : ℝ) ^ 2 * recordCoupling p ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]

end PhysicalRuns

section PhysicalLaw

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def physicalCircuit (gates : List (AlgorithmMatrix I W)) : Circuit ((I × Bool) × W) :=
  gates.flatMap (fun U => [.gate U, .query])

theorem physicalCircuit_run (p : ℝ) (gates : List (AlgorithmMatrix I W)) (v : QState (XorBasis I W)) :
    Run (databaseXorOracle p) (tensorLiftCircuit (physicalCircuit gates)) v = physicalRun p gates v := by
  induction gates generalizing v with
  | nil => rfl
  | cons U gates ih =>
    simp only [physicalCircuit, List.flatMap_cons, List.cons_append, List.nil_append,
      tensorLiftCircuit, List.map_cons, tensorLiftStep, run_gate, run_query]
    exact ih _

theorem physicalRun_eq_databaseXorRun (p : ℝ) (gates : List (AlgorithmMatrix I W))
    (ψ : QState ((I × Bool) × W)) :
    physicalRun p gates (physicalInitial ψ) = databaseXorRun p (physicalCircuit gates) ψ :=
  (physicalCircuit_run p gates (physicalInitial ψ)).symm

theorem physicalRun_oracle_law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (gates : List (AlgorithmMatrix I W)) (ψ : QState ((I × Bool) × W))
    (q : (I × Bool) × W) (x : I → Bool) :
    ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p))
      (physicalRun p gates (physicalInitial ψ)) (q,x) =
        bernoulliState p x * Run (workspaceBitOracle x) (physicalCircuit gates) ψ q := by
  rw [physicalRun_eq_databaseXorRun]
  exact databaseXor_fullstate p hp0 hp1 (physicalCircuit gates) ψ q x

end PhysicalLaw

section PhysicalFrontier

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem recordCoupling_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    recordCoupling p ^ 2 = 4 * p * (1 - p) := by
  unfold recordCoupling
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hp0 (sub_nonneg.mpr hp1))]
  ring

theorem physicalFrontier (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ)
    (gates : List (AlgorithmMatrix I W)) (hG : algorithmGatesValid gates) :
    Normalized (physicalRun p gates (physicalInitial ψ)) ∧
    (∀ q x,
      ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p))
        (physicalRun p gates (physicalInitial ψ)) (q,x) =
          bernoulliState p x * Run (workspaceBitOracle x) (physicalCircuit gates) ψ q) ∧
    (∀ k U, U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ →
      recordAmplitude (k + 1) (physicalRun p (gates ++ [U]) (physicalInitial ψ)) ≤
        recordAmplitude (k + 1) (physicalRun p gates (physicalInitial ψ)) +
          recordCoupling p * recordAmplitude k (physicalRun p gates (physicalInitial ψ))) ∧
    (∀ k, recordAmplitude k (physicalRun p gates (physicalInitial ψ)) ≤
      (Nat.choose gates.length k : ℝ) * recordCoupling p ^ k) ∧
    (∀ k, MeasureProb (physicalRun p gates (physicalInitial ψ)) (recordEvent k) ≤
      (Nat.choose gates.length k : ℝ) ^ 2 * recordCoupling p ^ (2 * k)) := by
  refine ⟨physicalRun_normalized p hp0 hp1 gates hG _ (physicalInitial_normalized ψ hψ),
    physicalRun_oracle_law p hp0 hp1 gates ψ, ?_,
    physicalRun_binomial p hp0 hp1 ψ hψ gates hG,
    physicalRun_bad_probability p hp0 hp1 ψ hψ gates hG⟩
  intro k U hU
  rw [physicalRun_append]
  have hs := physicalQuery_amplitude_recurrence k p hp0 hp1
    (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) (physicalRun p gates (physicalInitial ψ)))
  have hh := recordAmplitude_algorithm_le (k + 1) U hU (physicalRun p gates (physicalInitial ψ))
  have hl := recordAmplitude_algorithm_le k U hU (physicalRun p gates (physicalInitial ψ))
  exact hs.trans (add_le_add hh (mul_le_mul_of_nonneg_left hl (recordCoupling_nonneg p)))

end PhysicalFrontier

section RepeatedQueries

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem physicalTargetH_square : databaseTargetHadamard (I := I) (W := W) * databaseTargetHadamard = 1 := by
  simp only [databaseTargetHadamard, controlHadamard, tensorGate_mul, Matrix.one_mul,
    hadamard_mul_self, tensorGate_one]

theorem physicalPhase_square : jointPhaseOracle (I := I) (W := W) * jointPhaseOracle = 1 := by
  simp only [jointPhaseOracle, Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases h : x.1.1.2 = true ∧ x.2 x.1.1.1 = true <;> simp [h]
  · simp [hxy]

theorem compressedQuery_square (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    compressedOracle (I := I) (W := W) p * compressedOracle p = 1 := by
  let S : Matrix (XorBasis I W) (XorBasis I W) ℂ := TensorGate
    (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)
  have hF : decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact decompressGate_unitary p hp0 hp1
  have hS : S ∈ Matrix.unitaryGroup (XorBasis I W) ℂ := tensorGate_unitary (Submonoid.one_mem _) hF
  have hSS : S * Sᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hS
  have hSS' : Sᴴ * S = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hS
  have hdef : compressedOracle p = Sᴴ * jointPhaseOracle * S := by
    simp [S, compressedOracle, tensorGate_conjTranspose]
  rw [hdef]
  calc
    (Sᴴ * jointPhaseOracle * S) * (Sᴴ * jointPhaseOracle * S) =
        Sᴴ * jointPhaseOracle * (S * Sᴴ) * jointPhaseOracle * S := by noncomm_ring
    _ = Sᴴ * (jointPhaseOracle * jointPhaseOracle) * S := by rw [hSS]; noncomm_ring
    _ = 1 := by rw [physicalPhase_square, Matrix.mul_one, hSS']

theorem physicalQuery_square (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p * databaseXorOracle p = 1 := by
  let H := databaseTargetHadamard (I := I) (W := W)
  let C := compressedOracle (I := I) (W := W) p
  change (H * C * H) * (H * C * H) = 1
  have hH : H * H = 1 := physicalTargetH_square
  have hC : C * C = 1 := compressedQuery_square p hp0 hp1
  calc
    (H * C * H) * (H * C * H) = H * C * (H * H) * C * H := by noncomm_ring
    _ = H * (C * C) * H := by rw [hH]; noncomm_ring
    _ = 1 := by rw [hC, Matrix.mul_one, hH]

theorem physicalRun_repeat (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : QState (XorBasis I W)) :
    physicalRun p [1,1] v = v := by
  simp only [physicalRun, List.foldl_cons, List.foldl_nil, tensorGate_one, applyGate_one]
  rw [← applyGate_mul, physicalQuery_square p hp0 hp1, applyGate_one]

end RepeatedQueries

end Qatlib.Concepts.CompressedQuery.BosonicNorm
