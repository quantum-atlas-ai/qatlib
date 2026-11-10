/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch
import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.CoherentSim.CleanQPEBands
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.WalkSearch.CountedWalk
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

def dataTagUpdate {H : Type} (b : ℕ) (d : H → Reg b) (p : H × Reg b) : H × Reg b :=
  (p.1, fun i => p.2 i ^^ d p.1 i)

noncomputable def dataTagGate {H : Type} [DecidableEq H] (b : ℕ) (d : H → Reg b) :
    Matrix (H × Reg b) (H × Reg b) ℂ := permMatrix (dataTagUpdate b d)

noncomputable def dataTagEmbed {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (ψ : QState H) : QState (H × Reg b) :=
  dataTagGate b d *ᵥ TensorState ψ (Ket (fun _ : Fin b => false))

noncomputable def dataTagWalk {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) : Matrix (H × Reg b) (H × Reg b) ℂ :=
  dataTagGate b d * TensorGate W (1 : Matrix (Reg b) (Reg b) ℂ) * (dataTagGate b d)ᴴ

noncomputable def dataTagMarked {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (S : Finset H) : Finset (H × Reg b) :=
  Finset.univ.filter (fun p => p.1 ∈ S)

noncomputable def dataTagSzegedyWord {I : Type} [Fintype I] [DecidableEq I]
    (b : ℕ) (d : (I × I) → Reg b) (j : I) : List (AdjointStep ((I × I) × Reg b)) :=
  [.gate (dataTagGate b d)] ++
    phaseLiftWord (fun A => TensorGate A (1 : Matrix (Reg b) (Reg b) ℂ)) (countedSzegedyWord j) ++
    [.gate ((dataTagGate b d)ᴴ)]

theorem dataTagUpdate_involutive {H : Type} (b : ℕ) (d : H → Reg b) :
    Function.Involutive (dataTagUpdate b d) := by
  rintro ⟨x,w⟩
  refine Prod.ext rfl ?_
  funext i
  simp [dataTagUpdate]

theorem dataTagGate_unitary {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) : dataTagGate b d ∈ Matrix.unitaryGroup (H × Reg b) ℂ :=
  permMatrix_unitary (dataTagUpdate_involutive b d)

theorem dataTagGate_adjoint {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) : (dataTagGate b d)ᴴ = dataTagGate b d :=
  permMatrix_conjTranspose (dataTagUpdate_involutive b d)

private theorem tagXor_zero (b : ℕ) (x y : Reg b) :
    (fun i => x i ^^ y i) = (fun _ => false) ↔ x = y := by
  constructor
  · intro h; funext i; have hi := congrFun h i
    cases hx : x i <;> cases hy : y i <;> simp_all
  · rintro rfl; simp

theorem dataTagEmbed_apply {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (ψ : QState H) (p : H × Reg b) :
    dataTagEmbed b d ψ p = if p.2 = d p.1 then ψ p.1 else 0 := by
  change ApplyGate (permMatrix (dataTagUpdate b d)) _ p = _
  rw [applyGate_permMatrix (dataTagUpdate_involutive b d)]
  simp only [TensorState, dataTagUpdate, Ket, tagXor_zero, mul_ite, mul_one, mul_zero]

theorem data_tag_reversible_clean_embedding (H : Type) [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) :
    Function.Involutive (dataTagUpdate b d) ∧
    dataTagGate b d ∈ Matrix.unitaryGroup (H × Reg b) ℂ ∧
    (∀ ψ : QState H, ∀ p : H × Reg b,
      dataTagEmbed b d ψ p = if p.2 = d p.1 then ψ p.1 else 0) ∧
    (∀ ψ : QState H, ‖toEuclidean_fromVec (dataTagEmbed b d ψ)‖ =
      ‖toEuclidean_fromVec ψ‖) := by
  refine ⟨dataTagUpdate_involutive b d, dataTagGate_unitary b d,
    dataTagEmbed_apply b d, ?_⟩
  intro ψ
  change ‖toEuclidean_fromVec (ApplyGate (dataTagGate b d) _)‖ = _
  rw [norm_applyGate_of_mem_unitaryGroup (dataTagGate_unitary b d), tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _), mul_one]

theorem data_augmented_szegedy_actual_word_and_update_cost
    (I : Type) [Fintype I] [DecidableEq I] (b : ℕ) (d : (I × I) → Reg b)
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ)
    (hP : IsTransitionMatrix P) (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hprep : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    evaluate (TensorGate U (1 : Matrix (Reg b) (Reg b) ℂ)) (dataTagSzegedyWord b d j) =
      dataTagWalk b d (SzegedyWalk P) ∧
    adjointQueryCount (dataTagSzegedyWord b d j) = 4 ∧
    adjointGateCount (dataTagSzegedyWord b d j) = 6 := by
  have he := phaseLiftWord_evaluate (fun A : Matrix (I × I) (I × I) ℂ => TensorGate A
    (1 : Matrix (Reg b) (Reg b) ℂ))
    (by exact tensorGate_one)
    (by intro A B; rw [tensorGate_mul, Matrix.one_mul])
    (by intro A; simp [tensorGate_conjTranspose]) U (countedSzegedyWord j)
  refine ⟨?_, ?_, ?_⟩
  · simp only [dataTagSzegedyWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_one]
    rw [he, counted_szegedy_actual_walk_semantics P j U hP hU hprep]
    unfold dataTagWalk
    rfl
  · simp [dataTagSzegedyWord, adjointQueryCount_append, adjointQueryCount,
      (phaseLiftWord_counts _ _).1, (counted_szegedy_actual_word_and_counts j).2.1]
  · simp [dataTagSzegedyWord, adjointGateCount_append, adjointGateCount,
      (phaseLiftWord_counts _ _).2, (counted_szegedy_actual_word_and_counts j).2.2]

theorem dataTagWalk_embed {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) (ψ : QState H) :
    dataTagWalk b d W *ᵥ dataTagEmbed b d ψ = dataTagEmbed b d (W *ᵥ ψ) := by
  have hi : (dataTagGate b d)ᴴ * dataTagGate b d = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (dataTagGate_unitary b d)
  unfold dataTagWalk dataTagEmbed
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc (dataTagGate b d * TensorGate W 1) (dataTagGate b d)ᴴ
    (dataTagGate b d), hi, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  change ApplyGate (dataTagGate b d) (ApplyGate (TensorGate W 1) (TensorState ψ _)) = _
  rw [applyGate_tensorGate, applyGate_one]
  rfl

theorem dataTagMark_apply {H : Type} [Fintype H] [DecidableEq H] (S : Finset H)
    (ψ : QState H) (x : H) : (preparedMark S *ᵥ ψ) x = if x ∈ S then -ψ x else ψ x := by
  simp only [preparedMark, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Projector, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem dataTagMark_embed {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (ψ : QState H) (S : Finset H) :
    preparedMark (dataTagMarked b S) *ᵥ dataTagEmbed b d ψ =
      dataTagEmbed b d (preparedMark S *ᵥ ψ) := by
  funext ⟨x,w⟩
  simp only [dataTagMark_apply, dataTagEmbed_apply, dataTagMarked, Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem dataTagMeasure {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (ψ : QState H) (S : Finset H) :
    MeasureProb (dataTagEmbed b d ψ) (dataTagMarked b S) = MeasureProb ψ S := by
  simp only [MeasureProb, dataTagMarked, Finset.sum_filter, BornProb, dataTagEmbed_apply]
  rw [Fintype.sum_prod_type]
  have hs : ∀ x : H, (∑ w : Reg b, if x ∈ S then
      ‖if w = d x then ψ x else 0‖ ^ 2 else 0) = if x ∈ S then ‖ψ x‖ ^ 2 else 0 := by
    intro x
    have hw : ∀ w : Reg b, ‖if w = d x then ψ x else 0‖ ^ 2 =
        if w = d x then ‖ψ x‖ ^ 2 else 0 := by
      intro w; split_ifs <;> simp
    simp only [hw]
    by_cases hx : x ∈ S <;> simp [hx]
  simp only [hs]
  exact Finset.sum_ite_mem Finset.univ S (fun x => ‖ψ x‖ ^ 2) |>.trans (by simp)

theorem data_augmented_walk_reachable_transport_and_mark
    (H : Type) [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (W : Matrix H H ℂ) (ψ : QState H) (S : Finset H) :
    dataTagWalk b d W *ᵥ dataTagEmbed b d ψ = dataTagEmbed b d (W *ᵥ ψ) ∧
    preparedMark (dataTagMarked b S) *ᵥ dataTagEmbed b d ψ =
      dataTagEmbed b d (preparedMark S *ᵥ ψ) ∧
    MeasureProb (dataTagEmbed b d ψ) (dataTagMarked b S) = MeasureProb ψ S :=
  ⟨dataTagWalk_embed b d W ψ, dataTagMark_embed b d ψ S, dataTagMeasure b d ψ S⟩

theorem dataTagWalk_mul {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (A B : Matrix H H ℂ) :
    dataTagWalk b d (A * B) = dataTagWalk b d A * dataTagWalk b d B := by
  have hi : (dataTagGate b d)ᴴ * dataTagGate b d = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (dataTagGate_unitary b d)
  unfold dataTagWalk
  rw [show TensorGate (A * B) (1 : Matrix (Reg b) (Reg b) ℂ) =
    TensorGate A 1 * TensorGate B 1 from by rw [tensorGate_mul, Matrix.one_mul]]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dataTagGate b d)ᴴ (dataTagGate b d), hi, Matrix.one_mul]

theorem dataTagWalk_one {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) : dataTagWalk b d (1 : Matrix H H ℂ) = 1 := by
  unfold dataTagWalk
  rw [tensorGate_one, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp (dataTagGate_unitary b d)

theorem dataTagWalk_adjoint {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (A : Matrix H H ℂ) :
    dataTagWalk b d Aᴴ = (dataTagWalk b d A)ᴴ := by
  simp only [dataTagWalk, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    tensorGate_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_assoc]

private theorem dataTagGate_mul_apply {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (A : Matrix (H × Reg b) (H × Reg b) ℂ)
    (p q : H × Reg b) : (dataTagGate b d * A) p q = A (dataTagUpdate b d p) q := by
  change ApplyGate (permMatrix (dataTagUpdate b d)) (fun r => A r q) p = _
  exact applyGate_permMatrix (dataTagUpdate_involutive b d) _ p

private theorem mul_dataTagGate_apply {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (A : Matrix (H × Reg b) (H × Reg b) ℂ)
    (p q : H × Reg b) : (A * dataTagGate b d) p q = A p (dataTagUpdate b d q) := by
  change (∑ r, A p r * (if r = dataTagUpdate b d q then (1 : ℂ) else 0)) = _
  simp

theorem dataTagWalk_apply {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) (d : H → Reg b) (A : Matrix H H ℂ) (p q : H × Reg b) :
    dataTagWalk b d A p q =
      if (fun i => p.2 i ^^ d p.1 i) = (fun i => q.2 i ^^ d q.1 i)
      then A p.1 q.1 else 0 := by
  unfold dataTagWalk
  rw [dataTagGate_adjoint, mul_dataTagGate_apply, dataTagGate_mul_apply]
  simp [tensorGate_apply, dataTagUpdate, Matrix.one_apply]

theorem dataTagSzegedyWord_wellFormed {I : Type} [Fintype I] [DecidableEq I]
    (b : ℕ) (d : (I × I) → Reg b) (j : I) :
    WellFormedAdjointCircuit (dataTagSzegedyWord b d j) := by
  unfold dataTagSzegedyWord
  apply WellFormedAdjointCircuit.append
  · apply WellFormedAdjointCircuit.append
    · simp [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil,
        dataTagGate_unitary]
    · exact phaseLiftWord_wellFormed _ (fun _ h => tensorGate_unitary h (by simp))
        (countedSzegedyWord_wellFormed j)
  · simp [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil,
      dataTagGate_adjoint, dataTagGate_unitary]

end Qatlib.Concepts.WalkSearch.CountedWalk
