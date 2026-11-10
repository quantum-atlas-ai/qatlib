/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CountedWalk.DataAugmentedSzegedy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

def dataFlagTagSplit (A H : Type) (b : ℕ) :
    (A × (Bool × (H × Reg b))) ≃ ((A × (Bool × H)) × Reg b) where
  toFun p := ((p.1,(p.2.1,p.2.2.1)),p.2.2.2)
  invFun p := (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def dataFlagMatrix {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (U : Matrix (A × (Bool × H)) (A × (Bool × H)) ℂ) :
    Matrix (A × (Bool × (H × Reg b))) (A × (Bool × (H × Reg b))) ℂ :=
  relabelGate (dataFlagTagSplit A H b).symm
    (dataTagWalk b (fun p : A × (Bool × H) => d p.2.2) U)

noncomputable def dataFlagEmbed {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (ψ : QState (A × (Bool × H))) : QState (A × (Bool × (H × Reg b))) :=
  relabelState (dataFlagTagSplit A H b).symm
    (dataTagEmbed b (fun p : A × (Bool × H) => d p.2.2) ψ)

theorem dataFlagMatrix_apply {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (U : Matrix (A × (Bool × H)) (A × (Bool × H)) ℂ)
    (p q : A × (Bool × (H × Reg b))) :
    dataFlagMatrix b d U p q =
      if (fun i => p.2.2.2 i ^^ d p.2.2.1 i) = (fun i => q.2.2.2 i ^^ d q.2.2.1 i)
      then U (p.1,(p.2.1,p.2.2.1)) (q.1,(q.2.1,q.2.2.1)) else 0 := by
  exact dataTagWalk_apply b _ U _ _

theorem dataFlagEmbed_apply {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (ψ : QState (A × (Bool × H))) (p : A × (Bool × (H × Reg b))) :
    dataFlagEmbed b d ψ p = if p.2.2.2 = d p.2.2.1
      then ψ (p.1,(p.2.1,p.2.2.1)) else 0 :=
  dataTagEmbed_apply b _ ψ _

theorem dataFlagMatrix_one {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b) :
    dataFlagMatrix (A := A) b d 1 = 1 := by
  rw [dataFlagMatrix, dataTagWalk_one,
      Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one]

theorem dataFlagMatrix_mul {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (U V : Matrix (A × (Bool × H)) (A × (Bool × H)) ℂ) :
    dataFlagMatrix b d (U * V) = dataFlagMatrix b d U * dataFlagMatrix b d V := by
  rw [dataFlagMatrix, dataTagWalk_mul,
      Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]
  rfl

theorem dataFlagMatrix_adjoint {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (U : Matrix (A × (Bool × H)) (A × (Bool × H)) ℂ) :
    dataFlagMatrix b d Uᴴ = (dataFlagMatrix b d U)ᴴ := by
  rw [dataFlagMatrix, dataTagWalk_adjoint]
  rfl

theorem dataFlagMatrix_embed {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (U : Matrix (A × (Bool × H)) (A × (Bool × H)) ℂ) (ψ : QState (A × (Bool × H))) :
    ApplyGate (dataFlagMatrix b d U) (dataFlagEmbed b d ψ) =
      dataFlagEmbed b d (ApplyGate U ψ) := by
  rw [dataFlagMatrix, dataFlagEmbed, applyGate_relabelGate]
  exact congrArg (relabelState (dataFlagTagSplit A H b).symm) (dataTagWalk_embed b _ U ψ)

private theorem tagXor_cancel_iff (b : ℕ) (x y z : Reg b) :
    (fun i => x i ^^ z i) = (fun i => y i ^^ z i) ↔ x = y := by
  constructor
  · intro h; funext i; have hi := congrFun h i
    cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all
  · rintro rfl; rfl

theorem dataFlagMatrix_oracle {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) :
    dataFlagMatrix (A := A) b d (parallelOracle (controlOracle W)) =
      parallelOracle (controlOracle (dataTagWalk b d W)) := by
  ext ⟨a,c,x,w⟩ ⟨a',c',x',w'⟩
  cases c <;> cases c' <;> by_cases hx : x = x' <;>
    simp [dataFlagMatrix_apply, parallelOracle, controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select,
      Matrix.one_apply, Prod.ext_iff, dataTagWalk_apply, hx,
      tagXor_cancel_iff]
  all_goals split_ifs <;> simp_all

theorem dataFlagMatrix_phaseGate {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b) (Q : Matrix A A ℂ) :
    dataFlagMatrix b d (TensorGate Q (1 : Matrix (Bool × H) (Bool × H) ℂ)) =
      TensorGate Q (1 : Matrix (Bool × (H × Reg b)) (Bool × (H × Reg b)) ℂ) := by
  ext ⟨a,c,x,w⟩ ⟨a',c',x',w'⟩
  cases c <;> cases c' <;> by_cases hx : x = x' <;>
    simp [dataFlagMatrix_apply, tensorGate_apply, Matrix.one_apply, Prod.ext_iff, hx,
      tagXor_cancel_iff, mul_ite]

theorem dataFlagMatrix_threshold {H : Type} [Fintype H] [DecidableEq H]
    (b M n : ℕ) (d : H → Reg b) :
    dataFlagMatrix b d (permMatrix (phaseThresholdFlip (I := H) M n)) =
      permMatrix (phaseThresholdFlip (I := H × Reg b) M n) := by
  ext ⟨a,c,x,w⟩ ⟨a',c',x',w'⟩
  by_cases hx : x = x' <;>
    simp [dataFlagMatrix_apply, permMatrix, phaseThresholdFlip, Prod.ext_iff, hx,
      tagXor_cancel_iff]
  all_goals split_ifs <;> simp_all

noncomputable def dataFlagCircuit {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b) :
    Circuit (A × (Bool × H)) → Circuit (A × (Bool × (H × Reg b))) :=
  List.map (fun s => match s with
    | .gate U => .gate (dataFlagMatrix b d U)
    | .query => .query)

theorem dataFlagCircuit_counted {H : Type} [Fintype H] [DecidableEq H]
    (b M : ℕ) (d : H → Reg b) :
    dataFlagCircuit b d (countedPhaseCircuit (I := H) M) = countedPhaseCircuit (I := H × Reg b) M := by
  have hl : ∀ n, dataFlagCircuit b d (phaseThresholdLoop (I := H) M n) =
      phaseThresholdLoop (I := H × Reg b) M n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [phaseThresholdLoop, phaseThresholdBlock, dataFlagCircuit, List.map_append,
        dataFlagMatrix_threshold, ← ih]
  simp only [countedPhaseCircuit, dataFlagCircuit, List.map_append, List.map_cons, List.map_nil,
    dataFlagMatrix_phaseGate]
  rw [show List.map _ (phaseThresholdLoop (I := H) M (M-1)) =
    dataFlagCircuit b d (phaseThresholdLoop (I := H) M (M-1)) from rfl, hl]

theorem dataFlagCircuit_compile {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b) (cs : Circuit (A × (Bool × H))) :
    phaseLiftWord (dataFlagMatrix b d) (phaseCompileCircuit cs) =
      phaseCompileCircuit (dataFlagCircuit b d cs) := by
  simp only [phaseLiftWord, phaseCompileCircuit, dataFlagCircuit, List.map_reverse, List.map_map]
  congr 2
  funext s
  cases s <;> rfl

theorem dataFlagMatrix_qpe {H : Type} [Fintype H] [DecidableEq H]
    (b M : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) :
    dataFlagMatrix b d (evaluate (parallelOracle (controlOracle W))
      (phaseCompileCircuit (countedPhaseCircuit (I := H) M))) =
    evaluate (parallelOracle (controlOracle (dataTagWalk b d W)))
      (phaseCompileCircuit (countedPhaseCircuit (I := H × Reg b) M)) := by
  rw [← phaseLiftWord_evaluate (dataFlagMatrix b d) (dataFlagMatrix_one b d)
    (dataFlagMatrix_mul b d) (dataFlagMatrix_adjoint b d), dataFlagMatrix_oracle,
    dataFlagCircuit_compile, dataFlagCircuit_counted]

theorem dataFlagMatrix_tail {H : Type} [Fintype H] [DecidableEq H]
    (b M k : ℕ) (d : H → Reg b)
    (U : Matrix (PhaseReflectionSpace H M k) (PhaseReflectionSpace H M k) ℂ) :
    dataFlagMatrix b d (phaseTailGate M k U) = phaseTailGate M k (dataFlagMatrix b d U) := by
  ext p q
  simp only [dataFlagMatrix_apply, phaseTailGate, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  dsimp [phaseTailSplit]
  simp only [tensorGate_apply, dataFlagMatrix_apply]
  split_ifs <;> simp

theorem dataFlagMatrix_head {H : Type} [Fintype H] [DecidableEq H]
    (b M k : ℕ) (d : H → Reg b)
    (U : Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ) :
    dataFlagMatrix b d (phaseHeadGate M k U) = phaseHeadGate M k (dataFlagMatrix b d U) := by
  ext p q
  simp only [dataFlagMatrix_apply, phaseHeadGate, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  dsimp [phaseHeadSplit, phaseTailSplit]
  simp only [tensorGate_apply, dataFlagMatrix_apply]
  split_ifs <;> simp

theorem dataFlagMatrix_detection {H : Type} [Fintype H] [DecidableEq H]
    (b M k : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) :
    dataFlagMatrix b d (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k)) =
      evaluate (parallelOracle (controlOracle (dataTagWalk b d W))) (phaseDetectionWord M k) := by
  induction k with
  | zero => simp [phaseDetectionWord, evaluate, dataFlagMatrix_one]
  | succ k ih =>
    rw [phaseDetectionWord_evaluate_succ, dataFlagMatrix_mul, dataFlagMatrix_tail,
      dataFlagMatrix_head, ih, dataFlagMatrix_qpe, phaseDetectionWord_evaluate_succ]

theorem dataFlagMatrix_diagonal {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (f : A × (Bool × H) → ℂ) :
    dataFlagMatrix b d (Matrix.diagonal f) =
      Matrix.diagonal (fun p : A × (Bool × (H × Reg b)) => f (p.1,(p.2.1,p.2.2.1))) := by
  ext ⟨a,c,x,w⟩ ⟨a',c',x',w'⟩
  cases c <;> cases c' <;> by_cases ha : a = a' <;> by_cases hx : x = x' <;>
    simp [dataFlagMatrix_apply, Matrix.diagonal_apply, Prod.ext_iff, ha, hx, tagXor_cancel_iff]

private theorem phaseZero_diagonal {H : Type} [Fintype H] [DecidableEq H] (M k : ℕ) :
    phaseZeroReflection (I := H) M k = Matrix.diagonal
      (fun p : PhaseReflectionSpace H M k => if ∀ j, (p.1 j).val = 0 then (1 : ℂ) else -1) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases hp : ∀ j, (p.1 j).val = 0 <;>
      norm_num [phaseZeroReflection, ReflectionAbout, Projector, phaseZeroEvent, hp]
  · simp [phaseZeroReflection, ReflectionAbout, Projector, hpq]

theorem dataFlagMatrix_zeroReflection {H : Type} [Fintype H] [DecidableEq H]
    (b M k : ℕ) (d : H → Reg b) :
    dataFlagMatrix b d (phaseZeroReflection (I := H) M k) =
      phaseZeroReflection (I := H × Reg b) M k := by
  rw [phaseZero_diagonal, phaseZero_diagonal, dataFlagMatrix_diagonal]

theorem dataFlagMatrix_reflection {H : Type} [Fintype H] [DecidableEq H]
    (b M k : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) :
    dataFlagMatrix b d (evaluate (parallelOracle (controlOracle W)) (phaseReflectionWord M k)) =
      evaluate (parallelOracle (controlOracle (dataTagWalk b d W))) (phaseReflectionWord M k) := by
  simp only [phaseReflectionWord, evaluate_append, evaluate_adjointCircuit,
    evaluate, instructionMatrix, Matrix.mul_one]
  rw [dataFlagMatrix_mul, dataFlagMatrix_mul, dataFlagMatrix_adjoint,
    dataFlagMatrix_detection, dataFlagMatrix_zeroReflection]

theorem dataFlagMatrix_freshLift {H : Type} [Fintype H] [DecidableEq H]
    (b M k t : ℕ) (d : H → Reg b)
    (U : Matrix (PhaseReflectionSpace H M k) (PhaseReflectionSpace H M k) ℂ) :
    dataFlagMatrix b d (relabelGate (phaseFreshActionSplit H M k t).symm
      (TensorGate (1 : Matrix (Fin (k*t) → Fin M) (Fin (k*t) → Fin M) ℂ) U)) =
    relabelGate (phaseFreshActionSplit (H × Reg b) M k t).symm
      (TensorGate (1 : Matrix (Fin (k*t) → Fin M) (Fin (k*t) → Fin M) ℂ)
        (dataFlagMatrix b d U)) := by
  ext p q
  simp only [dataFlagMatrix_apply, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [phaseFreshActionSplit, Equiv.trans_apply, Equiv.prodAssoc_apply,
      Equiv.prodCongr_apply, Equiv.prodComm_apply, Equiv.refl_apply, Prod.map, Prod.swap, id_eq]
  simp only [tensorGate_apply, dataFlagMatrix_apply]
  split_ifs <;> simp

theorem dataFlagMatrix_freshReflection {H : Type} [Fintype H] [DecidableEq H]
    (b M k t : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) :
    dataFlagMatrix b d (phaseFreshReflectionMatrix W M k t) =
      phaseFreshReflectionMatrix (dataTagWalk b d W) M k t := by
  rw [phaseFreshReflectionMatrix, dataFlagMatrix_freshLift, dataFlagMatrix_reflection]
  rfl

theorem dataFlagEmbed_initial {H : Type} [Fintype H] [DecidableEq H]
    (b M n : ℕ) (d : H → Reg b) (ψ : QState H) :
    phaseReflectionEmbed M n (dataTagEmbed b d ψ) =
      dataFlagEmbed b d (phaseReflectionEmbed M n ψ) := by
  funext p
  simp only [phaseReflectionEmbed, dataTagEmbed_apply, dataFlagEmbed_apply]
  split_ifs <;> rfl

theorem dataFlagEmbed_fresh {H : Type} [Fintype H] [DecidableEq H]
    (b M k t : ℕ) (hM : 0 < M) (d : H → Reg b)
    (ψ : QState (PhaseReflectionSpace H M (k*t))) :
    phaseFreshAppend M k t hM (dataFlagEmbed b d ψ) =
      dataFlagEmbed b d (phaseFreshAppend M k t hM ψ) := by
  funext p
  simp only [phaseFreshAppend, relabelState, Function.comp_apply, Equiv.symm_symm,
    TensorState, dataFlagEmbed_apply]
  simp only [phaseFreshSplit, Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, Prod.map, id_eq]
  split_ifs <;> simp

private theorem dataPhaseCheck_apply {H : Type} [Fintype H] [DecidableEq H]
    (S : Finset H) (M n : ℕ) (ψ : QState (PhaseReflectionSpace H M n))
    (p : PhaseReflectionSpace H M n) :
    ApplyGate (phaseSearchCheck S M n) ψ p = if p.2.2 ∈ S then -ψ p else ψ p := by
  rcases p with ⟨a,c,x⟩
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    phaseSearchCheck, parallelOracle]
  simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, tensorGate_apply,
      Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq]
  exact dataTagMark_apply S (fun y => ψ (a,c,y)) x

theorem dataFlagEmbed_check {H : Type} [Fintype H] [DecidableEq H]
    (b M n : ℕ) (d : H → Reg b) (S : Finset H)
    (ψ : QState (PhaseReflectionSpace H M n)) :
    ApplyGate (phaseSearchCheck (dataTagMarked b S) M n) (dataFlagEmbed b d ψ) =
      dataFlagEmbed b d (ApplyGate (phaseSearchCheck S M n) ψ) := by
  funext p
  simp only [dataPhaseCheck_apply, dataFlagEmbed_apply, dataTagMarked,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

theorem dataTagSearchState {H : Type} [Fintype H] [DecidableEq H]
    (b M k t : ℕ) (d : H → Reg b) (W : Matrix H H ℂ) (ψ : QState H) (S : Finset H) :
    phaseSearchState (dataTagWalk b d W) (dataTagEmbed b d ψ) (dataTagMarked b S) M k t =
      dataFlagEmbed b d (phaseSearchState W ψ S M k t) := by
  induction t with
  | zero => exact dataFlagEmbed_initial b M (k*0) d ψ
  | succ t ih =>
    by_cases hM : 0 < M
    · rw [phaseSearchState, dif_pos hM, phaseSearchState, dif_pos hM, ih,
        dataFlagEmbed_fresh, dataFlagEmbed_check, ← dataFlagMatrix_freshReflection,
        dataFlagMatrix_embed]
    · simp only [phaseSearchState, dif_neg hM]
      funext p
      simp [dataFlagEmbed_apply]

theorem dataFlagMeasure {A H : Type} [Fintype A] [DecidableEq A]
    [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (ψ : QState (A × (Bool × H))) (S : Finset H) :
    MeasureProb (dataFlagEmbed b d ψ)
      (Finset.univ.filter (fun p => p.2.2 ∈ dataTagMarked b S)) =
    MeasureProb ψ (Finset.univ.filter (fun p => p.2.2 ∈ S)) := by
  simp only [MeasureProb, Finset.sum_filter, dataTagMarked, Finset.mem_filter,
    Finset.mem_univ, true_and, BornProb, dataFlagEmbed_apply]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  have hw : ∀ w : Reg b, ‖if w = d x then ψ (a,c,x) else 0‖ ^ 2 =
      if w = d x then ‖ψ (a,c,x)‖ ^ 2 else 0 := by
    intro w; split_ifs <;> simp
  simp only [hw]
  by_cases hx : x ∈ S <;> simp [hx]

theorem data_augmented_actual_phase_search_event_transport
    (H : Type) [Fintype H] [DecidableEq H] (b : ℕ) (d : H → Reg b)
    (W : Matrix H H ℂ) (ψ : QState H) (S : Finset H) (M k t : ℕ)
    (_hM : 2 ≤ M) (_hW : W ∈ Matrix.unitaryGroup H ℂ) :
    MeasureProb (phaseSearchState (dataTagWalk b d W) (dataTagEmbed b d ψ)
      (dataTagMarked b S) M k t)
      (Finset.univ.filter (fun x => x.2.2 ∈ dataTagMarked b S)) =
    MeasureProb (phaseSearchState W ψ S M k t) (Finset.univ.filter (fun x => x.2.2 ∈ S)) := by
  rw [dataTagSearchState, dataFlagMeasure]

theorem data_augmented_uniform_three_actual_find_consumer
    (b : ℕ) (d : (Fin 3 × Fin 3) → Reg b) :
    let P : Fin 3 → Fin 3 → ℝ := fun _ _ => 1/3
    let ψ : QState (Fin 3 × Fin 3) := fun _ => (1/3 : ℂ)
    let S := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = 0)
    MeasureProb (phaseSearchState (dataTagWalk b d (SzegedyWalk P))
      (dataTagEmbed b d ψ) (dataTagMarked b S) 2 1 1)
      (Finset.univ.filter (fun x => x.2.2 ∈ dataTagMarked b S)) = 25/27 := by
  (try dsimp only)
  have hP : IsTransitionMatrix (fun _ _ : Fin 3 => (1/3 : ℝ)) := by
    norm_num [IsTransitionMatrix, Fin.sum_univ_succ]
  rw [data_augmented_actual_phase_search_event_transport _ b d _ _ _ 2 1 1
    (by decide) (szegedyWalk_unitary _ hP)]
  exact phase_search_uniform_three_actual_consumer.1

theorem data_augmented_qpe_actual_controlled_updates_and_paid_inverse
    (I : Type) [Fintype I] [DecidableEq I] (b M : ℕ) (d : (I × I) → Reg b)
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ)
    (hM : 0 < M) (hP : IsTransitionMatrix P) (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hprep : ∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) :
    let O := TensorGate U (1 : Matrix (Reg b) (Reg b) ℂ)
    let word := cleanQPEWord M (dataTagSzegedyWord b d j)
    WellFormedAdjointCircuit word ∧ adjointQueryCount word = 4*(M-1) ∧
    adjointGateCount word = 8*(M-1)+2 ∧
    adjointQueryCount (adjointCircuit word) = 4*(M-1) ∧
    adjointGateCount (adjointCircuit word) = 8*(M-1)+2 ∧
    ∀ ξ : QState (Fin M × (Bool × ((I × I) × Reg b))),
      evaluate (TensorGate (1 : Operator M) (controlOracle O)) word *ᵥ ξ =
      Run (TensorGate (1 : Operator M) (controlOracle (dataTagWalk b d (SzegedyWalk P))))
        (countedPhaseCircuit M) ξ := by
  (try dsimp only)
  have hb := data_augmented_szegedy_actual_word_and_update_cost I b d P j U hP hU hprep
  have hc := clean_qpe_actual_expansion_semantics_and_paid_inverse ((I × I) × Reg b) M
    (TensorGate U (1 : Matrix (Reg b) (Reg b) ℂ)) (dataTagSzegedyWord b d j) hM
    (dataTagSzegedyWord_wellFormed b d j)
  (try dsimp only at hc)
  rw [hb.2.1, hb.2.2, hb.1] at hc
  refine ⟨hc.1, ?_, ?_, ?_, ?_, hc.2.2.2.2.2⟩
  · rw [hc.2.1]; omega
  · rw [hc.2.2.1]; omega
  · rw [hc.2.2.2.1, hc.2.1]; omega
  · rw [hc.2.2.2.2.1, hc.2.2.1]; omega

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
