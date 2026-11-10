/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.MatrixAccess.FrameFilterUse

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable def frameLiftStep {H : Type} [Fintype H] [DecidableEq H] :
    AdjointStep H → AdjointStep (Bool × H)
  | .gate G => .gate (TensorGate (1 : Matrix Bool Bool ℂ) G)
  | .forward => .forward
  | .backward => .backward

noncomputable def frameFilteredWord {H M : Type} [Fintype H] [DecidableEq H] [Fintype M]
    [DecidableEq M] (F : Matrix H M ℂ) (ca cb : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  cb.map frameLiftStep ++ [.gate (frameFlagFilter F)] ++ ca.map frameLiftStep

private theorem parallelOracle_bool_eq {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) :
    parallelOracle (J := Bool) O = TensorGate (1 : Matrix Bool Bool ℂ) O :=
  parallelOracle_eq_kronecker O

private theorem evaluate_frameLift {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (parallelOracle (J := Bool) O) (cs.map frameLiftStep) =
      TensorGate (1 : Matrix Bool Bool ℂ) (evaluate O cs) := by
  induction cs with
  | nil => simp [evaluate, tensorGate_one]
  | cons s cs ih =>
    cases s with
    | gate G =>
      simp only [List.map_cons, frameLiftStep, evaluate, instructionMatrix, ih]
      rw [tensorGate_mul, Matrix.one_mul]
    | forward =>
      simp only [List.map_cons, frameLiftStep, evaluate, instructionMatrix, ih]
      rw [parallelOracle_bool_eq, tensorGate_mul, Matrix.one_mul]
    | backward =>
      simp only [List.map_cons, frameLiftStep, evaluate, instructionMatrix, ih]
      rw [parallelOracle_adjoint, parallelOracle_bool_eq, tensorGate_mul, Matrix.one_mul]

private theorem adjointQueryCount_map_frameLiftStep {H : Type} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) :
    adjointQueryCount (cs.map frameLiftStep) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    cases s <;> simp [List.map_cons, adjointQueryCount, ih, frameLiftStep]

private theorem adjointGateCount_map_frameLiftStep {H : Type} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) :
    adjointGateCount (cs.map frameLiftStep) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    cases s <;> simp [List.map_cons, adjointGateCount, ih, frameLiftStep]

theorem frame_filter_actual_body_substitution_and_cost (H M : Type) [Fintype H]
    [DecidableEq H] [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (O : Matrix H H ℂ)
    (ca cb : List (AdjointStep H)) :
    evaluate (parallelOracle (J := Bool) O) (frameFilteredWord F ca cb) =
      frameFilteredProduct F (evaluate O ca) (evaluate O cb) ∧
    adjointQueryCount (frameFilteredWord F ca cb) =
      adjointQueryCount ca + adjointQueryCount cb ∧
    adjointGateCount (frameFilteredWord F ca cb) =
      adjointGateCount ca + adjointGateCount cb + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [frameFilteredWord, evaluate_append, evaluate_append, evaluate_frameLift,
      evaluate_frameLift]
    simp only [evaluate, instructionMatrix, Matrix.mul_one]
    rw [frameFilteredProduct, Matrix.mul_assoc]
  · rw [frameFilteredWord, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_map_frameLiftStep, adjointQueryCount_map_frameLiftStep]
    simp only [adjointQueryCount]
    omega
  · rw [frameFilteredWord, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_map_frameLiftStep, adjointGateCount_map_frameLiftStep]
    simp only [adjointGateCount]
    omega

noncomputable def plusFrameCol : Matrix Bool (Fin 1) ℂ :=
  Matrix.replicateCol (Fin 1) (ApplyGate Hadamard (Ket false))

def zeroFrameCol : Matrix Bool (Fin 1) ℂ := Matrix.replicateCol (Fin 1) (Ket false)

theorem plusFrameCol_apply (b : Bool) (i : Fin 1) :
    plusFrameCol b i = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [plusFrameCol, Matrix.replicateCol_apply, applyGate_hadamard_ket_false, Plus,
    hadamard_apply_false]

theorem zeroFrameCol_apply (b : Bool) (i : Fin 1) :
    zeroFrameCol b i = if b = false then (1 : ℂ) else 0 := rfl

private theorem star_inv_sqrt2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal]

theorem plusFrameCol_isIsometry : IsIsometry plusFrameCol := by
  show (plusFrameCol)ᴴ * plusFrameCol = 1
  ext o m
  have hom : o = m := Subsingleton.elim o m
  subst m
  have h1 : ∀ h : Bool, star ((plusFrameCol h o)) * plusFrameCol h o = (1 / 2 : ℂ) := by
    intro h
    rw [plusFrameCol_apply, star_inv_sqrt2, inv_sqrt2_mul_self]
    norm_num
  show ∑ h : Bool, star ((plusFrameCol h o)) * plusFrameCol h o
      = (1 : Matrix (Fin 1) (Fin 1) ℂ) o o
  rw [Fintype.sum_bool, h1, h1, Matrix.one_apply_eq]
  norm_num

theorem zeroFrameCol_isIsometry : IsIsometry zeroFrameCol := by
  show (zeroFrameCol)ᴴ * zeroFrameCol = 1
  ext o m
  have hom : o = m := Subsingleton.elim o m
  subst m
  have h1 : ∀ h : Bool, star ((zeroFrameCol h o)) * zeroFrameCol h o
      = if h = false then (1 : ℂ) else 0 := by
    intro h
    rw [zeroFrameCol_apply]
    cases h <;> simp
  show ∑ h : Bool, star ((zeroFrameCol h o)) * zeroFrameCol h o
      = (1 : Matrix (Fin 1) (Fin 1) ℂ) o o
  rw [Fintype.sum_bool, h1, h1, Matrix.one_apply_eq]
  simp

private theorem rangeProjector_plusFrameCol_apply (x y : Bool) :
    rangeProjector plusFrameCol x y = 1 / 2 := by
  have h1 : ∀ m : Fin 1, plusFrameCol x m * (plusFrameColᴴ) m y = 1 / 2 := by
    intro m
    have hy : (plusFrameColᴴ) m y = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [Matrix.conjTranspose_apply, plusFrameCol_apply, star_inv_sqrt2]
    rw [plusFrameCol_apply x m, hy, inv_sqrt2_mul_self]
    norm_num
  show (plusFrameCol * plusFrameColᴴ) x y = 1 / 2
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin 1)]
  · exact h1 0
  · intro m _ hm
    exact absurd (Subsingleton.elim m 0) hm
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem frame_filter_noncoordinate_actual_leakage_consumer :
    let F : Matrix Bool (Fin 1) ℂ := Matrix.replicateCol (Fin 1) (ApplyGate Hadamard (Ket false))
    let R : Matrix Bool (Fin 1) ℂ := Matrix.replicateCol (Fin 1) (Ket false)
    compress R (1 : Matrix Bool Bool ℂ) R = 1 ∧
      compress (flagFrame R) (frameFilteredProduct F 1 1) (flagFrame R) =
        (1 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      MeasureProb (ApplyGate (frameFilteredProduct F 1 1) (Ket (false, false))) {(false, false)} =
        1 / 4 := by
  intro F R
  have hFd : F = plusFrameCol := rfl
  have hRd : R = zeroFrameCol := rfl
  rw [hFd, hRd]
  have hcorner := frame_filtered_rectangular_corner_product Bool (Fin 1) (Fin 1) (Fin 1)
    zeroFrameCol plusFrameCol zeroFrameCol 1 1
  have hc1 : compress zeroFrameCol (1 : Matrix Bool Bool ℂ) plusFrameCol =
      Matrix.of fun _ _ => (Real.sqrt 2 : ℂ)⁻¹ := by
    ext o m
    show ((zeroFrameCol)ᴴ * (1 : Matrix Bool Bool ℂ) * plusFrameCol) o m
      = (Matrix.of fun _ _ => (Real.sqrt 2 : ℂ)⁻¹ : Matrix (Fin 1) (Fin 1) ℂ) o m
    rw [Matrix.mul_assoc, Matrix.one_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, zeroFrameCol_apply,
      plusFrameCol_apply, Fintype.sum_bool]
    simp
  have hc2 : compress plusFrameCol (1 : Matrix Bool Bool ℂ) zeroFrameCol =
      Matrix.of fun _ _ => (Real.sqrt 2 : ℂ)⁻¹ := by
    ext o m
    show ((plusFrameCol)ᴴ * (1 : Matrix Bool Bool ℂ) * zeroFrameCol) o m
      = (Matrix.of fun _ _ => (Real.sqrt 2 : ℂ)⁻¹ : Matrix (Fin 1) (Fin 1) ℂ) o m
    rw [Matrix.mul_assoc, Matrix.one_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, zeroFrameCol_apply,
      plusFrameCol_apply, star_inv_sqrt2, Fintype.sum_bool]
    simp
  refine ⟨?_, ?_, ?_⟩
  · show (zeroFrameCol)ᴴ * (1 : Matrix Bool Bool ℂ) * zeroFrameCol = 1
    rw [Matrix.mul_one]
    exact zeroFrameCol_isIsometry
  · rw [hcorner, hc1, hc2]
    ext o m
    simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.smul_apply,
      Matrix.one_apply]
    have hom : o = m := Subsingleton.elim o m
    subst hom
    rw [inv_sqrt2_mul_self]
    norm_num
  · have hW : frameFilteredProduct plusFrameCol (1 : Matrix Bool Bool ℂ)
        (1 : Matrix Bool Bool ℂ) = frameFlagFilter plusFrameCol := by
      rw [frameFilteredProduct, tensorGate_one, Matrix.one_mul, Matrix.mul_one]
    rw [hW]
    have h1 := (frame_filter_actual_unitary_and_success_block Bool (Fin 1) plusFrameCol
      plusFrameCol_isIsometry).2 false false
    have hamp : ApplyGate (frameFlagFilter plusFrameCol) (Ket (false, false)) (false, false)
        = 1 / 2 := by
      show ∑ z : Bool × Bool,
          frameFlagFilter plusFrameCol (false, false) z * Ket (false, false) z = 1 / 2
      rw [Finset.sum_eq_single (false, false)]
      · rw [ket_self, h1, rangeProjector_plusFrameCol_apply, mul_one]
      · intro z _ hz
        rw [ket_ne hz, mul_zero]
      · simp
    show MeasureProb (ApplyGate (frameFlagFilter plusFrameCol) (Ket (false, false)))
        {(false, false)} = 1 / 4
    simp only [MeasureProb, BornProb, Finset.sum_singleton, hamp]
    norm_num

private theorem relabel_prodComm_cnot_apply (p q : Bool × Bool) :
    relabelGate (Equiv.prodComm Bool Bool) CNOT p q =
      if p = (q.1 ^^ q.2, q.2) then (1 : ℂ) else 0 := by
  obtain ⟨pf, py⟩ := p
  obtain ⟨qf, qy⟩ := q
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, CNOT, permMatrix, cnotFlip,
    Equiv.prodComm, Prod.ext_iff, and_comm]

private theorem hadamard_mul_relabel_cnot_entry (b' x' c y : Bool) :
    (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
        relabelGate (Equiv.prodComm Bool Bool) CNOT) (b', x') (c, y) =
      if b' = (c ^^ y) then Hadamard x' y else 0 := by
  rcases b' <;> rcases x' <;> rcases c <;> rcases y <;>
    simp [Matrix.mul_apply, TensorGate, Matrix.one_apply,
      relabel_prodComm_cnot_apply, Hadamard]

private theorem circuit_entry (b' x' b x : Bool) :
    ((TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
        relabelGate (Equiv.prodComm Bool Bool) CNOT) *
      TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) (b', x') (b, x) =
      if b' = b then 1 / 2 else if x' = x then 1 / 2 else -(1 / 2) := by
  have hstep : ∀ c y : Bool,
      (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
          relabelGate (Equiv.prodComm Bool Bool) CNOT) (b', x') (c, y) *
        TensorGate (1 : Matrix Bool Bool ℂ) Hadamard (c, y) (b, x) =
      if b' = (c ^^ y) ∧ c = b then Hadamard x' y * Hadamard y x else 0 := by
    intro c y
    rw [hadamard_mul_relabel_cnot_entry b' x' c y]
    rcases b' <;> rcases x' <;> rcases b <;> rcases x <;> rcases c <;> rcases y <;>
      simp [TensorGate, Hadamard]
  show ∑ s : Bool × Bool,
      (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
          relabelGate (Equiv.prodComm Bool Bool) CNOT) (b', x') s *
        TensorGate (1 : Matrix Bool Bool ℂ) Hadamard s (b, x) = _
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun y _ => hstep c y, Fintype.sum_bool, Fintype.sum_bool]
  rcases b' <;> rcases x' <;> rcases b <;> rcases x <;>
    simp [Hadamard] <;> norm_num [sqrt2_sq, inv_sqrt2_mul_self]

private theorem three_local_filter_entries (b' x' b x : Bool) :
    ((TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
        relabelGate (Equiv.prodComm Bool Bool) CNOT) *
      TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) (b', x') (b, x) =
      frameFlagFilter plusFrameCol (b', x') (b, x) := by
  rw [circuit_entry b' x' b x]
  simp only [frameFlagFilter, Matrix.add_apply, Matrix.sub_apply, TensorGate,
    Matrix.kronecker_apply, Matrix.one_apply, rangeProjector_plusFrameCol_apply, PauliX,
    permMatrix]
  rcases b' <;> rcases x' <;> rcases b <;> rcases x <;> simp <;> norm_num

theorem frame_filter_noncoordinate_three_local_gate_consumer :
    let F : Matrix Bool (Fin 1) ℂ := Matrix.replicateCol (Fin 1) (ApplyGate Hadamard (Ket false))
    let C : Circuit (Bool × Bool) :=
      [.gate (TensorGate 1 Hadamard), .gate (relabelGate (Equiv.prodComm Bool Bool) CNOT),
       .gate (TensorGate 1 Hadamard)]
    (∀ ψ : QState (Bool × Bool),
        Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) C ψ = ApplyGate (frameFlagFilter F) ψ) ∧
      QueryCount C = 0 ∧ GateCount C = 3 := by
  intro F C
  have hFd : F = plusFrameCol := rfl
  refine ⟨fun ψ => ?_, rfl, rfl⟩
  show ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (ApplyGate (relabelGate (Equiv.prodComm Bool Bool) CNOT)
        (ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) ψ)) =
    ApplyGate (frameFlagFilter F) ψ
  rw [hFd, ← applyGate_mul, ← applyGate_mul]
  have hEq : (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard *
      relabelGate (Equiv.prodComm Bool Bool) CNOT) *
    TensorGate (1 : Matrix Bool Bool ℂ) Hadamard = frameFlagFilter plusFrameCol := by
    ext ⟨b', x'⟩ ⟨b, x⟩
    exact three_local_filter_entries b' x' b x
  rw [hEq]

end Qatlib.Concepts.MatrixAccess.FrameFilterUse
