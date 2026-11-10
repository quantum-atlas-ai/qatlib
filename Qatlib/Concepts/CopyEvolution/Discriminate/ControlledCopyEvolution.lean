/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.CopyEvolution.Discriminate.ConditionalOutput
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option maxHeartbeats 800000

namespace Qatlib.Concepts.CopyEvolution.Discriminate

variable {D : ℕ}

open Matrix
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
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder Kronecker

noncomputable def controlDataEquiv (D : ℕ) : Bool × Fin D ≃ Fin (2 * D) :=
  (Equiv.prodCongr boolEquivFin2 (Equiv.refl (Fin D))).trans finProdFinEquiv

@[simp] theorem controlDataEquiv_apply (D : ℕ) (b : Bool) (i : Fin D) :
    controlDataEquiv D (b, i) = (i : ℕ) + D * (if b then 1 else 0) := by
  cases b <;> simp [controlDataEquiv, finProdFinEquiv, boolEquivFin2]

noncomputable def relabelLM {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ :=
  MatrixMap.submatrix ℂ e.symm

@[simp] theorem relabelLM_apply {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) : relabelLM e A = relabelGate e A := rfl

private theorem relabel_star {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ) : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

private theorem relabel_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.one_apply]

private theorem relabel_mul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (U V : Matrix I I ℂ) :
    relabelGate e U * relabelGate e V = relabelGate e (U * V) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Equiv.sum_comp e.symm (fun k : I => U (e.symm i) k * V k (e.symm j))]

private theorem relabel_unitary {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have h : Uᴴ * U = 1 := by
    have h' := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, relabel_star, relabel_mul, h,
    relabel_one]

private theorem one_unitary {D : ℕ} : (1 : Operator D) ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (by ext i j; simp [Matrix.one_apply])

noncomputable def controlledSwapRawGate (D : ℕ) (θ : ℝ) :
    Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ :=
  select (fun b : Bool => if b then partialSwapMatrix D θ else 1)

noncomputable def copyAssociator (D : ℕ) : Bool × (Fin D × Fin D) ≃ (Bool × Fin D) × Fin D where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun q := (q.1.1, (q.1.2, q.2))
  left_inv p := by rcases p with ⟨b, i, c⟩; rfl
  right_inv q := by rcases q with ⟨⟨b, i⟩, c⟩; rfl

theorem controlledSwapRawGate_unitarity (D : ℕ) (θ : ℝ) :
    controlledSwapRawGate D θ ∈ Matrix.unitaryGroup (Bool × (Fin D × Fin D)) ℂ := by
  apply select_unitary
  intro b
  cases b
  · simp
  · simpa using! partialSwapMatrix_unitary D θ

noncomputable def controlledSwapGateTensor (D : ℕ) (θ : ℝ) :
    Matrix (Fin (2 * D) × Fin D) (Fin (2 * D) × Fin D) ℂ :=
  relabelGate ((copyAssociator D).trans
      ((controlDataEquiv D).prodCongr (Equiv.refl (Fin D)))) (controlledSwapRawGate D θ)

theorem controlledSwapGateTensor_conjTranspose_mul (D : ℕ) (θ : ℝ) :
    (controlledSwapGateTensor D θ)ᴴ * controlledSwapGateTensor D θ = 1 := by
  have hG : controlledSwapGateTensor D θ ∈ Matrix.unitaryGroup (Fin (2 * D) × Fin D) ℂ :=
    relabel_unitary _ (controlledSwapRawGate_unitarity D θ)
  have h := (Matrix.mem_unitaryGroup_iff').mp hG
  rwa [Matrix.star_eq_conjTranspose] at h

noncomputable def copyControlledEvolution (ρ : Operator D) (t : ℝ) : Operator (2 * D) :=
  relabelGate (controlDataEquiv D) (controlOracle (hamiltonianEvolution ρ t))

theorem copyControlledEvolution_conjTranspose_mul (ρ : Operator D) (hρ : ρ.IsHermitian)
    (t : ℝ) :
    (copyControlledEvolution ρ t)ᴴ * copyControlledEvolution ρ t = 1 := by
  have hG : copyControlledEvolution ρ t ∈ Matrix.unitaryGroup (Fin (2 * D)) ℂ :=
    relabel_unitary _ (controlOracle_unitary (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hρ t))
  have h := (Matrix.mem_unitaryGroup_iff').mp hG
  rwa [Matrix.star_eq_conjTranspose] at h

theorem copyControlledEvolution_unitarity (ρ : Operator D) (hρ : ρ.IsHermitian) (t : ℝ) :
    copyControlledEvolution ρ t ∈ Matrix.unitaryGroup (Fin (2 * D)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact copyControlledEvolution_conjTranspose_mul ρ hρ t

noncomputable def tensorWithCopyRegister (ρ : Operator D) (n : ℕ) :
    MatrixMap (Fin n) (Fin n × Fin D) ℂ where
  toFun M := TensorGate M ρ
  map_add' := by
    intro M N
    ext
    simp [TensorGate, add_mul]
  map_smul' := by
    intro c M
    ext
    simp [TensorGate, mul_assoc]

theorem completelyPositive_tensorWithCopyRegister (ρ : Operator D) (hρ : ρ.PosSemidef)
    (n : ℕ) : MatrixMap.IsCompletelyPositive (tensorWithCopyRegister ρ n) := by
  have h₁ : ∀ (x y : Matrix (Fin n) (Fin n) ℂ),
      (fun M : Matrix (Fin n) (Fin n) ℂ => M ⊗ₖ ρ) (x + y)
        = (fun M => M ⊗ₖ ρ) x + (fun M => M ⊗ₖ ρ) y := by
    intro x y
    simp [Matrix.add_kronecker]
  have h₂ : ∀ (m : ℂ) (x : Matrix (Fin n) (Fin n) ℂ),
      (fun M : Matrix (Fin n) (Fin n) ℂ => M ⊗ₖ ρ) (m • x)
        = m • (fun M => M ⊗ₖ ρ) x := by
    intro m x
    simp [Matrix.smul_kronecker]
  have h := MatrixMap.kron_kronecker_const (A := Fin n) (d := Fin D) hρ (h₁ := h₁) (h₂ := h₂)
  convert! h using 1

theorem tensorWithCopyRegister_apply (ρ : Operator D) (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    tensorWithCopyRegister ρ n M = TensorGate M ρ := rfl

theorem conjMap_apply {n : Type*} [Fintype n] [DecidableEq n] (U M : Matrix n n ℂ) :
    MatrixMap.conj U M = U * M * Uᴴ := rfl

noncomputable def traceRightRegisterLM' {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] :
    MatrixMap (d₁ × d₂) d₁ ℂ :=
  (CPTPMap.traceRight (d₁ := d₁) (d₂ := d₂)).toLinearMap

theorem traceRightRegisterLM'_apply {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    traceRightRegisterLM' M = Matrix.traceRight M := by
  ext i j
  simp only [traceRightRegisterLM', CPTPMap.traceRight, CPTPMap.compose, CPTPMap.traceLeft,
    CPTPMap.SWAP, CPTPMap.ofEquiv, MatrixMap.submatrix, LinearMap.comp_apply, Matrix.traceLeft]
  rfl

noncomputable def traceRightRegisterLM (D : ℕ) :
    MatrixMap (Fin (2 * D) × Fin D) (Fin (2 * D)) ℂ :=
  traceRightRegisterLM'

theorem completelyPositive_traceRightRegisterLM (D : ℕ) :
    MatrixMap.IsCompletelyPositive (traceRightRegisterLM D) :=
  (CPTPMap.traceRight (d₁ := Fin (2 * D)) (d₂ := Fin D)).cp

theorem traceRightRegisterLM_apply (D : ℕ) (M : Matrix (Fin (2 * D) × Fin D) (Fin (2 * D) × Fin D) ℂ) :
    traceRightRegisterLM D M = Matrix.traceRight M := traceRightRegisterLM'_apply M

noncomputable def controlledCopyChannelMap (ρ : Operator D) (θ : ℝ) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  (traceRightRegisterLM D).comp
    ((MatrixMap.conj (controlledSwapGateTensor D θ)).comp
      (tensorWithCopyRegister ρ (2 * D)))

theorem completelyPositive_controlledCopyChannelMap (ρ : Operator D) (hρ : ρ.PosSemidef)
    (θ : ℝ) : CompletelyPositive (controlledCopyChannelMap ρ θ) :=
  (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mpr
    (MatrixMap.IsCompletelyPositive.comp
      (MatrixMap.IsCompletelyPositive.comp
        (completelyPositive_tensorWithCopyRegister ρ hρ (2 * D))
        (MatrixMap.congruence_CP (A := Fin (2 * D) × Fin D) (B := Fin (2 * D) × Fin D)
          (controlledSwapGateTensor D θ)))
      (completelyPositive_traceRightRegisterLM D))

theorem tracePreserving_controlledCopyChannelMap (ρ : Operator D) (hρ : Matrix.trace ρ = 1)
    (θ : ℝ) : TracePreserving (controlledCopyChannelMap ρ θ) := by
  intro σ
  have hmap : controlledCopyChannelMap ρ θ σ
      = Matrix.traceRight ((controlledSwapGateTensor D θ) *
        TensorGate σ ρ *
        (controlledSwapGateTensor D θ)ᴴ) := by
    rw [controlledCopyChannelMap, LinearMap.comp_apply, LinearMap.comp_apply,
      traceRightRegisterLM_apply, conjMap_apply, tensorWithCopyRegister_apply]
  rw [hmap]
  calc Matrix.trace (Matrix.traceRight
        ((controlledSwapGateTensor D θ) * TensorGate σ ρ *
          (controlledSwapGateTensor D θ)ᴴ))
      = Matrix.trace ((controlledSwapGateTensor D θ) * TensorGate σ ρ *
          (controlledSwapGateTensor D θ)ᴴ) :=
      Matrix.traceRight_trace (controlledSwapGateTensor D θ * TensorGate σ ρ *
        (controlledSwapGateTensor D θ)ᴴ)
    _ = Matrix.trace ((controlledSwapGateTensor D θ)ᴴ *
          (controlledSwapGateTensor D θ) * TensorGate σ ρ) := by
      apply Matrix.trace_mul_cycle
    _ = Matrix.trace (TensorGate σ ρ) := by
        rw [controlledSwapGateTensor_conjTranspose_mul D θ, Matrix.one_mul]
    _ = Matrix.trace σ * Matrix.trace ρ := Matrix.trace_kronecker σ ρ
    _ = Matrix.trace σ := by rw [hρ, mul_one]

noncomputable def controlledCopyChannel (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (θ : ℝ) : QuantumChannel (2 * D) (2 * D) where
  map := controlledCopyChannelMap ρ θ
  completelyPositive := completelyPositive_controlledCopyChannelMap ρ hρ.1 θ
  tracePreserving := tracePreserving_controlledCopyChannelMap ρ hρ.2 θ

noncomputable def traceRightB (M : Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ) :
    Matrix (Bool × Fin D) (Bool × Fin D) ℂ :=
  fun x y => ∑ c, M (x.1, (x.2, c)) (y.1, (y.2, c))

@[simp] theorem traceRightB_apply
    (M : Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ) (x y : Bool × Fin D) :
    traceRightB M x y = ∑ c, M (x.1, (x.2, c)) (y.1, (y.2, c)) := rfl

noncomputable def tensorCopyB (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ :=
  fun x y => A (x.1, x.2.1) (y.1, y.2.1) * ρ x.2.2 y.2.2

@[simp] theorem tensorCopyB_apply (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)
    (x y : Bool × (Fin D × Fin D)) :
    tensorCopyB ρ A x y = A (x.1, x.2.1) (y.1, y.2.1) * ρ x.2.2 y.2.2 := rfl

noncomputable def controlledCopyRawMap (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    Matrix (Bool × Fin D) (Bool × Fin D) ℂ :=
  traceRightB (controlledSwapRawGate D θ * tensorCopyB ρ A *
    (controlledSwapRawGate D θ)ᴴ)

theorem ketFalseTensor_eq_select (D : ℕ) (X : Operator D) :
    TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X = select (fun b : Bool => if b then 0 else X) := by
  ext ⟨b, i⟩ ⟨b', i'⟩
  cases b <;> cases b' <;>
    simp [select, Matrix.of_apply, tensorGate_apply, outerProduct_apply,
        Qatlib.Foundations.PureStateMath.Ket]

theorem ketFalseTensor_copyB (D : ℕ) (X : Operator D) (ρ : Operator D) :
    tensorCopyB ρ (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X)
      = select (fun b : Bool => if b then 0 else TensorGate X ρ) := by
  ext ⟨b, i, c⟩ ⟨b', i', c'⟩
  cases b <;> cases b' <;>
    simp [select, Matrix.of_apply, tensorCopyB_apply, tensorGate_apply, outerProduct_apply,
      Qatlib.Foundations.PureStateMath.Ket, Complex.star_def]

theorem rawGate_select (D : ℕ) (θ : ℝ) :
    controlledSwapRawGate D θ
      = select (fun b : Bool => if b then partialSwapMatrix D θ else 1) := rfl

private theorem select_conj_select (V W' : Bool → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    select V * select W' * (select V)ᴴ
      = select (fun b => V b * W' b * (V b)ᴴ) := by
  rw [parallel_select_mul, parallel_select_adjoint, parallel_select_mul]

private theorem rawGate_conj_false (D : ℕ) (θ : ℝ) :
    ∀ M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) * M *
        (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)ᴴ = M := by
  intro M
  rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

private theorem rawGate_conj_zero (D : ℕ) (θ : ℝ) :
    partialSwapMatrix D θ * (0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) *
        (partialSwapMatrix D θ)ᴴ
      = 0 := by
  rw [Matrix.mul_zero, Matrix.zero_mul]

private theorem sum_diag_eq (ρ : Operator D) (c : ℂ) (hρ : Matrix.trace ρ = 1) :
    ∑ x, c * ρ x x = c := by
  have h : (∑ x, ρ x x) = Matrix.trace ρ := by
    symm
    exact Finset.sum_congr rfl fun i _ => Matrix.diag_apply ρ i
  rw [← Finset.mul_sum, h, hρ, mul_one]

private theorem traceRightB_ketFalse_select (D : ℕ) (X : Operator D) (ρ : Operator D)
    (hρ : Matrix.trace ρ = 1) :
    traceRightB (select (fun b : Bool => if b then 0 else TensorGate X ρ))
      = select (fun b : Bool => if b then 0 else X) := by
  ext ⟨b, i⟩ ⟨b', i'⟩
  cases b <;> cases b'
  · simp only [select, Matrix.of_apply, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      traceRightB_apply, tensorGate_apply]
    exact sum_diag_eq ρ (X i i') hρ
  · simp [select, Matrix.of_apply, traceRightB_apply]
  · simp [select, Matrix.of_apply, traceRightB_apply]
  · simp [select, Matrix.of_apply, traceRightB_apply]

theorem controlledCopyRawMap_ketFalse (D : ℕ) (ρ : Operator D) (θ : ℝ) (X : Operator D)
    (hρ : Matrix.trace ρ = 1) :
    controlledCopyRawMap ρ θ (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X)
      = TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X := by
  have hconj : controlledSwapRawGate D θ *
        tensorCopyB ρ (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X) *
        (controlledSwapRawGate D θ)ᴴ
      = select (fun b : Bool => if b then 0 else TensorGate X ρ) := by
    rw [rawGate_select, ketFalseTensor_copyB,
      select_conj_select (fun b : Bool => if b then partialSwapMatrix D θ else 1)
        (fun b : Bool => if b then 0 else TensorGate X ρ)]
    apply congrArg (fun f : Bool → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ => select f)
    funext b
    cases b
    · simp [rawGate_conj_false]
    · simp [rawGate_conj_zero]
  unfold controlledCopyRawMap
  rw [hconj, ketFalseTensor_eq_select, traceRightB_ketFalse_select D X ρ hρ]

noncomputable def copyRelabelEquiv (D : ℕ) : Bool × (Fin D × Fin D) ≃ Fin (2 * D) × Fin D :=
  (copyAssociator D).trans ((controlDataEquiv D).prodCongr (Equiv.refl (Fin D)))

theorem copyRelabelEquiv_apply (D : ℕ) (b : Bool) (i c : Fin D) :
    copyRelabelEquiv D (b, (i, c)) = ((controlDataEquiv D (b, i)), c) := rfl

theorem copyRelabelEquiv_symm_apply (D : ℕ) (p : Fin (2 * D)) (c : Fin D) :
    (copyRelabelEquiv D).symm (p, c)
      = (((controlDataEquiv D).symm p).1, (((controlDataEquiv D).symm p).2, c)) := rfl

theorem relabelGate_apply' {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) (i j : J) :
    relabelGate e A i j = A (e.symm i) (e.symm j) := rfl

theorem tensorCopyB_relabel (D : ℕ) (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    relabelGate (copyRelabelEquiv D) (tensorCopyB ρ A)
      = TensorGate (relabelGate (controlDataEquiv D) A) ρ := by
  ext ⟨r, c⟩ ⟨r', c'⟩
  simp only [tensorCopyB_apply, relabelGate_apply', copyRelabelEquiv_symm_apply,
    tensorGate_apply]

theorem traceRightB_relabel (D : ℕ)
    (M : Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ) :
    relabelGate (controlDataEquiv D) (traceRightB M)
      = Matrix.traceRight (relabelGate (copyRelabelEquiv D) M) := by
  ext p q
  simp only [Matrix.traceRight, Matrix.of_apply, traceRightB_apply, relabelGate_apply',
    copyRelabelEquiv_symm_apply]

theorem controlledCopyChannelMap_relabel (D : ℕ) (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    controlledCopyChannelMap ρ θ (relabelGate (controlDataEquiv D) A)
      = relabelGate (controlDataEquiv D) (controlledCopyRawMap ρ θ A) := by
  unfold controlledCopyChannelMap controlledCopyRawMap
  rw [LinearMap.comp_apply, LinearMap.comp_apply, traceRightRegisterLM_apply, conjMap_apply,
    tensorWithCopyRegister_apply]
  rw [controlledSwapGateTensor]
  rw [relabel_star]
  rw [← tensorCopyB_relabel D ρ A]
  simp only [copyRelabelEquiv]
  rw [relabel_mul, relabel_mul]
  rw [traceRightB_relabel D]
  rfl

theorem select_mul_apply {J : Type} [Fintype J] (V : Bool → Matrix J J ℂ)
    (M : Matrix (Bool × J) (Bool × J) ℂ) (b c : Bool) (u v : J) :
    (select V * M) (b, u) (c, v)
      = (V b * M.submatrix (fun p => (b, p)) (fun q => (c, q))) u v := by
  cases b <;> cases c <;>
    simp [Matrix.mul_apply, select, Matrix.of_apply, Matrix.submatrix_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false]

theorem select_conj_apply {J : Type} [Fintype J] (V : Bool → Matrix J J ℂ)
    (M : Matrix (Bool × J) (Bool × J) ℂ) (b c : Bool) (u v : J) :
    (select V * M * (select V)ᴴ) (b, u) (c, v)
      = (V b * M.submatrix (fun p => (b, p)) (fun q => (c, q)) * (V c)ᴴ) u v := by
  cases b <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      select_mul_apply, select, Matrix.of_apply, Matrix.submatrix_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false,
      Finset.mul_sum, Finset.sum_mul]

theorem controlledCopyRawMap_sandwich (D : ℕ) (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (b c : Bool) (u v : Fin D × Fin D) :
    (controlledSwapRawGate D θ * tensorCopyB ρ A * (controlledSwapRawGate D θ)ᴴ) (b, u) (c, v)
      = ((if b then partialSwapMatrix D θ else 1) *
          (tensorCopyB ρ A).submatrix (fun p => (b, p)) (fun q => (c, q)) *
          (if c then partialSwapMatrix D θ else 1)ᴴ) u v := by
  rw [rawGate_select, select_conj_apply]

theorem controlledCopyRawMap_ff (D : ℕ) (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (i j : Fin D)
    (hρ : Matrix.trace ρ = 1) :
    controlledCopyRawMap ρ θ A (false, i) (false, j) = A (false, i) (false, j) := by
  have hstep : ∀ c : Fin D,
      (controlledSwapRawGate D θ * tensorCopyB ρ A * (controlledSwapRawGate D θ)ᴴ)
        (false, (i, c)) (false, (j, c)) = A (false, i) (false, j) * ρ c c := by
    intro c
    rw [rawGate_select, select_conj_apply]
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, Matrix.mul_apply, Matrix.submatrix_apply, tensorCopyB_apply,
      Matrix.one_apply]
    rw [Fintype.sum_eq_single (j, c)]
    · simp
    · intro x hx
      rw [if_neg hx]
      ring
  unfold controlledCopyRawMap
  rw [traceRightB_apply]
  simp only [Prod.fst, Prod.snd]
  rw [Fintype.sum_congr _ _ (fun c => hstep c)]
  exact sum_diag_eq ρ (A (false, i) (false, j)) hρ

theorem traceRight_swap_conj (σ ρ : Operator D) (θ : ℝ) (hρ : Matrix.trace ρ = 1)
    (i j : Fin D) :
    Matrix.traceRight (TensorGate σ ρ * (partialSwapMatrix D θ)ᴴ) i j
      = (Real.cos θ) • σ i j + (Complex.I * (Real.sin θ : ℂ)) • (σ * ρ) i j := by
  rw [partialSwapMatrix_conjTranspose]
  have hneg : partialSwapMatrix D (-θ)
      = (Real.cos θ : ℂ) • 1 + (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D := by
    simp only [partialSwapMatrix, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    module
  have htrace : (∑ x : Fin D, ρ x x : ℂ) = 1 := by
    have h : (∑ x : Fin D, ρ x x : ℂ) = Matrix.trace ρ := by
      symm
      exact Finset.sum_congr rfl fun i _ => Matrix.diag_apply ρ i
    rw [h, hρ]
  rw [hneg, Matrix.mul_add, Matrix.mul_smul, ← partialTrace_eq_traceRight,
    partialTrace_add, partialTrace_smul, Matrix.mul_one]
  rw [Matrix.mul_smul, partialTrace_smul,
    (partial_swap_cross_partial_traces σ ρ).1]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.trace, partialTrace_tensorGate]
  simp [htrace]

theorem traceRight_swap (σ ρ : Operator D) (θ : ℝ) (hρ : Matrix.trace ρ = 1)
    (i j : Fin D) :
    Matrix.traceRight (partialSwapMatrix D θ * TensorGate σ ρ) i j
      = (Real.cos θ) • σ i j - (Complex.I * (Real.sin θ : ℂ)) • (ρ * σ) i j := by
  have htrace : (∑ x : Fin D, ρ x x : ℂ) = 1 := by
    have h : (∑ x : Fin D, ρ x x : ℂ) = Matrix.trace ρ := by
      symm
      exact Finset.sum_congr rfl fun i _ => Matrix.diag_apply ρ i
    rw [h, hρ]
  simp only [partialSwapMatrix, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul, ← partialTrace_eq_traceRight, partialTrace_sub, partialTrace_smul,
    (partial_swap_cross_partial_traces σ ρ).2]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.trace, partialTrace_tensorGate,
    Matrix.one_apply, one_mul, neg_smul, smul_eq_mul]
  simp [htrace]

private def AFT (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) : Operator D :=
  A.submatrix (fun p => (false, p)) (fun q => (true, q))

theorem controlledCopyRawMap_ft (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (i j : Fin D)
    (hρ : Matrix.trace ρ = 1) :
    controlledCopyRawMap ρ θ A (false, i) (true, j)
      = (Real.cos θ) • A (false, i) (true, j)
        + (Complex.I * (Real.sin θ : ℂ)) • (AFT A * ρ) i j := by
  have htrace : (∑ x : Fin D, ρ x x : ℂ) = 1 := by
    have h : (∑ x : Fin D, ρ x x : ℂ) = Matrix.trace ρ := by
      symm
      exact Finset.sum_congr rfl fun i _ => Matrix.diag_apply ρ i
    rw [h, hρ]
  have hstep : ∀ c : Fin D,
      (controlledSwapRawGate D θ * tensorCopyB ρ A * (controlledSwapRawGate D θ)ᴴ)
        (false, (i, c)) (true, (j, c))
      = (TensorGate (AFT A) ρ * (partialSwapMatrix D θ)ᴴ) (i, c) (j, c) := by
    intro c
    rw [rawGate_select, select_conj_apply]
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.submatrix_apply,
      tensorCopyB_apply, AFT, TensorGate, Matrix.kroneckerMap_apply, Fintype.sum_eq_single]
  have hmain : controlledCopyRawMap ρ θ A (false, i) (true, j)
      = Matrix.traceRight (TensorGate (AFT A) ρ * (partialSwapMatrix D θ)ᴴ) i j := by
    unfold controlledCopyRawMap
    rw [traceRightB_apply]
    simp only [Prod.fst, Prod.snd]
    rw [Fintype.sum_congr _ _ (fun c => hstep c)]
    rfl
  rw [hmain, traceRight_swap_conj _ _ _ hρ]
  simp only [Matrix.smul_apply, Matrix.trace, partialTrace_tensorGate, AFT,
    Matrix.submatrix_apply]

private def ATT (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) : Operator D :=
  A.submatrix (fun p => (true, p)) (fun q => (true, q))

theorem controlledCopyRawMap_tt (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (i j : Fin D) :
    controlledCopyRawMap ρ θ A (true, i) (true, j)
      = partialSwapOutput ρ θ (ATT A) i j := by
  have hstep : ∀ c : Fin D,
      (controlledSwapRawGate D θ * tensorCopyB ρ A * (controlledSwapRawGate D θ)ᴴ)
        (true, (i, c)) (true, (j, c))
      = (partialSwapMatrix D θ * TensorGate (ATT A) ρ *
          (partialSwapMatrix D θ)ᴴ) (i, c) (j, c) := by
    intro c
    rw [rawGate_select, select_conj_apply]
    simp only [Bool.true_eq_false, ↓reduceIte, Matrix.mul_apply, Matrix.submatrix_apply,
      tensorCopyB_apply, ATT, TensorGate, Matrix.kroneckerMap_apply]
  have hmain : controlledCopyRawMap ρ θ A (true, i) (true, j)
      = Matrix.traceRight
          (partialSwapMatrix D θ * TensorGate (ATT A) ρ * (partialSwapMatrix D θ)ᴴ) i j := by
    unfold controlledCopyRawMap
    rw [traceRightB_apply]
    simp only [Prod.fst, Prod.snd]
    rw [Fintype.sum_congr _ _ (fun c => hstep c)]
    rfl
  rw [hmain, partialSwapOutput, ← partialTrace_eq_traceRight]

def AFtf (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) : Operator D :=
  A.submatrix (fun p => (true, p)) (fun q => (false, q))

private theorem copyB_submatrix_tf (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    (tensorCopyB ρ A).submatrix (fun p => (true, p)) (fun q => (false, q))
      = TensorGate (AFtf A) ρ := by
  ext x y
  simp only [Matrix.submatrix_apply, tensorCopyB_apply, AFtf, TensorGate,
    Matrix.kroneckerMap_apply]

theorem controlledCopyRawMap_tf (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (i j : Fin D) :
    controlledCopyRawMap ρ θ A (true, i) (false, j)
      = Matrix.traceRight (partialSwapMatrix D θ * TensorGate (AFtf A) ρ) i j := by
  have hstep : ∀ c : Fin D,
      (controlledSwapRawGate D θ * tensorCopyB ρ A * (controlledSwapRawGate D θ)ᴴ)
        (true, (i, c)) (false, (j, c))
      = (partialSwapMatrix D θ * TensorGate (AFtf A) ρ) (i, c) (j, c) := by
    intro c
    rw [rawGate_select, select_conj_apply, copyB_submatrix_tf]
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.conjTranspose_one, Matrix.mul_one]
  have hmain : controlledCopyRawMap ρ θ A (true, i) (false, j)
      = Matrix.traceRight (partialSwapMatrix D θ * TensorGate (AFtf A) ρ) i j := by
    unfold controlledCopyRawMap
    rw [traceRightB_apply]
    simp only [Prod.fst, Prod.snd]
    rw [Fintype.sum_congr _ _ (fun c => hstep c)]
    rfl
  exact hmain

theorem controlledCopyRawMap_tf_entry (ρ : Operator D) (θ : ℝ)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) (i j : Fin D)
    (hρ : Matrix.trace ρ = 1) :
    controlledCopyRawMap ρ θ A (true, i) (false, j)
      = (Real.cos θ) • AFtf A i j
        - (Complex.I * (Real.sin θ : ℂ)) • (ρ * AFtf A) i j := by
  rw [controlledCopyRawMap_tf, traceRight_swap _ _ _ hρ]

noncomputable def copyMapPower {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d) :
    ℕ → Operator d →ₗ[ℂ] Operator d
  | 0 => LinearMap.id
  | k + 1 => T.comp (copyMapPower T k)

noncomputable def copyChannelPower {d : ℕ} (T : QuantumChannel d d) :
    ℕ → QuantumChannel d d
  | 0 => QuantumChannel.id d
  | k + 1 => T.comp (copyChannelPower T k)

@[simp] theorem copyChannelPower_map {d : ℕ} (T : QuantumChannel d d) (k : ℕ) :
    (copyChannelPower T k).map = copyMapPower T.map k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change T.map.comp (copyChannelPower T k).map = T.map.comp (copyMapPower T.map k)
    rw [ih]

noncomputable def controlledCopyRun (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) (n : ℕ) : QuantumChannel (2 * D) (2 * D) :=
  copyChannelPower (controlledCopyChannel ρ hρ (t / (n : ℝ))) n

noncomputable def controlledCopyRunMap (ρ : Operator D) (t : ℝ) (n : ℕ) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  copyMapPower (controlledCopyChannelMap ρ (t / (n : ℝ))) n

@[simp] theorem controlledCopyRun_map (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) (n : ℕ) :
    (controlledCopyRun ρ hρ t n).map = controlledCopyRunMap ρ t n :=
  copyChannelPower_map _ n

@[simp] theorem controlledCopyRun_zero (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) : (controlledCopyRun ρ hρ t 0).map = LinearMap.id := rfl

theorem copyControlledEvolution_add (ρ : Operator D) (s t : ℝ) :
    copyControlledEvolution ρ (s + t) =
      copyControlledEvolution ρ s * copyControlledEvolution ρ t := by
  rw [copyControlledEvolution, copyControlledEvolution, copyControlledEvolution,
    relabel_mul, controlOracle_mul]
  congr 2
  exact hamiltonianEvolution_add ρ s t

@[simp] theorem copyControlledEvolution_zero (ρ : Operator D) :
    copyControlledEvolution ρ 0 = 1 := by
  simp [copyControlledEvolution, hamiltonianEvolution, relabel_one]

theorem copyControlledEvolution_pow (ρ : Operator D) (t : ℝ) (n : ℕ) :
    (copyControlledEvolution ρ t) ^ n = copyControlledEvolution ρ ((n : ℝ) * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← copyControlledEvolution_add]
    congr 1
    push_cast
    ring

section ControlledTaylor

open scoped Matrix.Norms.L2Operator

private theorem trueControl_norm_le_one :
    ‖outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)‖ ≤ 1 := by
  have he : outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool) =
      Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0) := by
    ext b c
    cases b <;> cases c <;> simp [outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket,
        Matrix.diagonal_apply]
  rw [he, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro b; cases b <;> simp)

noncomputable def controlledSwapGenerator (D : ℕ) :
    Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ :=
  TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) (swapRegisterMatrix D)

private theorem controlledSwapGenerator_norm (D : ℕ) :
    ‖controlledSwapGenerator D‖ ≤ 1 := by
  rw [controlledSwapGenerator, l2_norm_tensorGate]
  have hs : ‖swapRegisterMatrix D‖ ≤ 1 :=
    l2_norm_unitary_le_one (by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        swapRegisterMatrix_conjTranspose, swapRegisterMatrix_mul_self])
  nlinarith [trueControl_norm_le_one, norm_nonneg (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)),
    norm_nonneg (swapRegisterMatrix D)]

noncomputable def controlledSwapProjector (D : ℕ) :
    Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ :=
  TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool))
    (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)

private theorem controlledSwapProjector_norm (D : ℕ) :
    ‖controlledSwapProjector D‖ ≤ 1 := by
  rw [controlledSwapProjector, l2_norm_tensorGate]
  nlinarith [trueControl_norm_le_one,
    (l2_norm_one_le : ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ ≤ 1),
    norm_nonneg (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)),
    norm_nonneg (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)]

theorem controlledSwapRawGate_expansion (D : ℕ) (θ : ℝ) :
    controlledSwapRawGate D θ = 1 +
      ((Real.cos θ : ℂ) - 1) • controlledSwapProjector D -
      (Complex.I * (Real.sin θ : ℂ)) • controlledSwapGenerator D := by
  ext ⟨b, i, j⟩ ⟨c, k, l⟩
  cases b <;> cases c <;>
    simp [controlledSwapRawGate, select, controlledSwapProjector, controlledSwapGenerator,
      outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, tensorGate_apply, partialSwapMatrix, Matrix.one_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply] <;> split_ifs <;> ring

private theorem controlled_trig_quadratic (θ : ℝ) :
    |Real.cos θ - 1| ≤ θ ^ 2 ∧ |Real.sin θ - θ| ≤ θ ^ 2 := by
  have hx (x : ℝ) (hx : x ∈ segment ℝ 0 θ) : |x| ≤ |θ| := by
    rcases le_or_gt 0 θ with hθ | hθ
    · rw [mem_segment_iff_wbtw, wbtw_iff_of_le hθ] at hx
      rw [abs_of_nonneg hθ, abs_of_nonneg hx.1]
      exact hx.2
    · rw [segment_symm, mem_segment_iff_wbtw,
        wbtw_iff_of_le (by linarith : θ ≤ 0)] at hx
      rw [abs_of_nonpos (by linarith : θ ≤ 0), abs_of_nonpos hx.2]
      linarith
  have hsin (x : ℝ) : |Real.sin x| ≤ |x| := by
    simpa using! Real.abs_sin_sub_sin_le x 0
  have hcos (x : ℝ) : |Real.cos x - 1| ≤ |x| := by
    simpa using! Real.abs_cos_sub_cos_le x 0
  have h0 : (0 : ℝ) ∈ segment ℝ 0 θ := left_mem_segment ℝ 0 θ
  have hθ : θ ∈ segment ℝ 0 θ := right_mem_segment ℝ 0 θ
  constructor
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Real.cos) (s := segment ℝ 0 θ)
      (fun x _ => (Real.hasDerivAt_cos x).differentiableAt)
      (fun x h => by
        rw [(Real.hasDerivAt_cos x).deriv, norm_neg, Real.norm_eq_abs]
        exact (hsin x).trans (hx x h))
      (convex_segment (0 : ℝ) θ) h0 hθ
    simpa [Real.norm_eq_abs, abs_mul_abs_self, ← sq] using! h
  · have hd (x : ℝ) : HasDerivAt (fun t => Real.sin t - t) (Real.cos x - 1) x :=
      (Real.hasDerivAt_sin x).sub (hasDerivAt_id x)
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun x => Real.sin x - x) (s := segment ℝ 0 θ)
      (fun x _ => (hd x).differentiableAt)
      (fun x h => by
        rw [(hd x).deriv, Real.norm_eq_abs]
        exact (hcos x).trans (hx x h))
      (convex_segment (0 : ℝ) θ) h0 hθ
    simpa [Real.norm_eq_abs, abs_mul_abs_self, ← sq] using! h

theorem controlledSwapRawGate_linear_and_quadratic (D : ℕ) (θ : ℝ) :
    ‖controlledSwapRawGate D θ - 1‖ ≤ 2 * |θ| ∧
      ‖controlledSwapRawGate D θ - 1 +
        (Complex.I * (θ : ℂ)) • controlledSwapGenerator D‖ ≤ 2 * θ ^ 2 := by
  have hc : ‖((Real.cos θ : ℂ) - 1)‖ = |Real.cos θ - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hs : ‖Complex.I * (Real.sin θ : ℂ)‖ = |Real.sin θ| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hr : ‖Complex.I * ((Real.sin θ : ℂ) - (θ : ℂ))‖ = |Real.sin θ - θ| := by
    rw [norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  constructor
  · have he : controlledSwapRawGate D θ - 1 =
        ((Real.cos θ : ℂ) - 1) • controlledSwapProjector D -
          (Complex.I * (Real.sin θ : ℂ)) • controlledSwapGenerator D := by
      rw [controlledSwapRawGate_expansion]
      abel
    rw [he]
    calc
      _ ≤ ‖((Real.cos θ : ℂ) - 1) • controlledSwapProjector D‖ +
          ‖(Complex.I * (Real.sin θ : ℂ)) • controlledSwapGenerator D‖ := norm_sub_le _ _
      _ ≤ |Real.cos θ - 1| + |Real.sin θ| := by
        rw [norm_smul, norm_smul, hc, hs]
        nlinarith [controlledSwapProjector_norm D, controlledSwapGenerator_norm D,
          abs_nonneg (Real.cos θ - 1), abs_nonneg (Real.sin θ)]
      _ ≤ 2 * |θ| := by
        have h1 := Real.abs_cos_sub_cos_le θ 0
        have h2 := Real.abs_sin_sub_sin_le θ 0
        simp only [Real.cos_zero, Real.sin_zero, sub_zero] at h1 h2
        linarith
  · have he : controlledSwapRawGate D θ - 1 +
        (Complex.I * (θ : ℂ)) • controlledSwapGenerator D =
        ((Real.cos θ : ℂ) - 1) • controlledSwapProjector D -
          (Complex.I * ((Real.sin θ : ℂ) - (θ : ℂ))) • controlledSwapGenerator D := by
      rw [controlledSwapRawGate_expansion]
      module
    rw [he]
    calc
      _ ≤ ‖((Real.cos θ : ℂ) - 1) • controlledSwapProjector D‖ +
          ‖(Complex.I * ((Real.sin θ : ℂ) - (θ : ℂ))) • controlledSwapGenerator D‖ := norm_sub_le _ _
      _ ≤ |Real.cos θ - 1| + |Real.sin θ - θ| := by
        rw [norm_smul, norm_smul, hc, hr]
        nlinarith [controlledSwapProjector_norm D, controlledSwapGenerator_norm D,
          abs_nonneg (Real.cos θ - 1), abs_nonneg (Real.sin θ - θ)]
      _ ≤ 2 * θ ^ 2 := by
        have h := controlled_trig_quadratic θ
        linarith [h.1, h.2]

private theorem controlled_sandwich_remainder
    {I : Type*} [Fintype I] [DecidableEq I]
    (U H X : Matrix I I ℂ) (θ : ℝ) (hH : H.IsHermitian)
    (hHn : ‖H‖ ≤ 1) (hU : ‖U‖ ≤ 1)
    (hlin : ‖U - 1‖ ≤ 2 * |θ|)
    (hquad : ‖U - 1 + (Complex.I * (θ : ℂ)) • H‖ ≤ 2 * θ ^ 2) :
    Matrix.traceNorm (U * X * Uᴴ - X +
      (Complex.I * (θ : ℂ)) • (H * X - X * H)) ≤
      6 * θ ^ 2 * Matrix.traceNorm X := by
  let A := (-Complex.I * (θ : ℂ)) • H
  have hXn : 0 ≤ Matrix.traceNorm X := Matrix.traceNorm_nonneg X
  have hAn : ‖A‖ ≤ |θ| := by
    simp only [A, norm_smul, norm_mul, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact (mul_le_mul_of_nonneg_left hHn (abs_nonneg θ)).trans_eq (mul_one _)
  have hAH : Aᴴ = -A := by
    simp only [A, Matrix.conjTranspose_smul, hH.eq]
    simp [RCLike.star_def, neg_smul, neg_mul]
  have hR : ‖U - 1 - A‖ ≤ 2 * θ ^ 2 := by
    simpa [A, neg_mul, neg_smul, sub_eq_add_neg] using! hquad
  have hUH : ‖Uᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have hdiffH : ‖Uᴴ - 1‖ ≤ 2 * |θ| := by
    rw [show Uᴴ - 1 = (U - 1)ᴴ by simp, Matrix.l2_opNorm_conjTranspose]
    exact hlin
  have hRH : ‖(U - 1 - A)ᴴ‖ ≤ 2 * θ ^ 2 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have he : U * X * Uᴴ - X + (Complex.I * (θ : ℂ)) • (H * X - X * H) =
      (U - 1 - A) * X * Uᴴ + A * X * (Uᴴ - 1) + X * (U - 1 - A)ᴴ := by
    have hm : (Complex.I * (θ : ℂ)) • (H * X - X * H) = -(A * X) + X * A := by
      simp [A, neg_mul, neg_smul, smul_sub, Matrix.smul_mul, Matrix.mul_smul,
        sub_eq_add_neg]
    rw [hm, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hAH]
    noncomm_ring
  rw [he]
  have h1 : Matrix.traceNorm ((U - 1 - A) * X * Uᴴ) ≤
      2 * θ ^ 2 * Matrix.traceNorm X := by
    calc
      _ ≤ ‖U - 1 - A‖ * Matrix.traceNorm X * ‖Uᴴ‖ := hamiltonian_traceNorm_sandwich_bound _ _ _
      _ ≤ (2 * θ ^ 2) * Matrix.traceNorm X * 1 := by gcongr
      _ = _ := mul_one _
  have h2 : Matrix.traceNorm (A * X * (Uᴴ - 1)) ≤
      2 * θ ^ 2 * Matrix.traceNorm X := by
    calc
      _ ≤ ‖A‖ * Matrix.traceNorm X * ‖Uᴴ - 1‖ := hamiltonian_traceNorm_sandwich_bound _ _ _
      _ ≤ |θ| * Matrix.traceNorm X * (2 * |θ|) := by gcongr
      _ = _ := by rw [← sq_abs]; ring
  have h3 : Matrix.traceNorm (X * (U - 1 - A)ᴴ) ≤
      2 * θ ^ 2 * Matrix.traceNorm X := by
    calc
      _ ≤ Matrix.traceNorm X * ‖(U - 1 - A)ᴴ‖ := Matrix.traceNorm_mul_le_traceNorm_opNorm _ _
      _ ≤ Matrix.traceNorm X * (2 * θ ^ 2) := by gcongr
      _ = _ := by ring
  have ht := (Matrix.traceNorm_add_le _ _).trans
    (add_le_add ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2)) h3)
  exact ht.trans_eq (by ring)

theorem controlledSwapGenerator_hermitian (D : ℕ) :
    (controlledSwapGenerator D).IsHermitian := by
  show (controlledSwapGenerator D)ᴴ = controlledSwapGenerator D
  simp only [controlledSwapGenerator, tensorGate_conjTranspose,
    swapRegisterMatrix_conjTranspose, (outerProduct_posSemidef (Qatlib.Foundations.PureStateMath.Ket true)).isHermitian.eq]

theorem controlledSwapRawGate_sandwich_remainder (D : ℕ) (θ : ℝ)
    (X : Matrix (Bool × (Fin D × Fin D)) (Bool × (Fin D × Fin D)) ℂ) :
    Matrix.traceNorm (controlledSwapRawGate D θ * X * (controlledSwapRawGate D θ)ᴴ - X +
      (Complex.I * (θ : ℂ)) • (controlledSwapGenerator D * X - X * controlledSwapGenerator D)) ≤
      6 * θ ^ 2 * Matrix.traceNorm X :=
  controlled_sandwich_remainder _ _ _ θ (controlledSwapGenerator_hermitian D)
    (controlledSwapGenerator_norm D)
    (l2_norm_unitary_le_one (controlledSwapRawGate_unitarity D θ))
    (controlledSwapRawGate_linear_and_quadratic D θ).1
    (controlledSwapRawGate_linear_and_quadratic D θ).2

end ControlledTaylor

def controlledCopyReferenceEquiv (D r : ℕ) :
    Fin r × (Fin (2 * D) × Fin D) ≃ (Fin r × Fin (2 * D)) × Fin D where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def controlledCopyReferenceGate (D r : ℕ) (θ : ℝ) :
    Matrix ((Fin r × Fin (2 * D)) × Fin D) ((Fin r × Fin (2 * D)) × Fin D) ℂ :=
  relabelGate (controlledCopyReferenceEquiv D r)
    (TensorGate (1 : Operator r) (controlledSwapGateTensor D θ))

theorem controlledCopy_reference_actual_bridge (D r : ℕ) (ρ : Operator D) (θ : ℝ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) :
    ChannelAmplification (controlledCopyChannelMap ρ θ) r X =
      Matrix.traceRight (controlledCopyReferenceGate D r θ * TensorGate X ρ *
        (controlledCopyReferenceGate D r θ)ᴴ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [ChannelAmplification, controlledCopyChannelMap, LinearMap.comp_apply,
    tensorWithCopyRegister_apply, conjMap_apply, traceRightRegisterLM_apply,
    controlledCopyReferenceGate, relabelGate_apply', Matrix.traceRight, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    tensorGate_apply, Matrix.one_apply]
  simp only [controlledCopyReferenceEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  simp [tensorGate_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, apply_ite, mul_ite, ite_mul]

section ControlledReferenceTaylor

open scoped Matrix.Norms.L2Operator

private theorem identity_tensor_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (A : Matrix I I ℂ) : ‖TensorGate (1 : Operator r) A‖ ≤ ‖A‖ := by
  rw [l2_norm_tensorGate]
  exact (mul_le_mul_of_nonneg_right l2_norm_one_le (norm_nonneg A)).trans_eq (one_mul _)

noncomputable def controlledCopyReferenceGenerator (D r : ℕ) :
    Matrix ((Fin r × Fin (2 * D)) × Fin D) ((Fin r × Fin (2 * D)) × Fin D) ℂ :=
  relabelGate (controlledCopyReferenceEquiv D r)
    (TensorGate (1 : Operator r)
      (relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D)))

private theorem controlledReferenceGenerator_hermitian (D r : ℕ) :
    (controlledCopyReferenceGenerator D r).IsHermitian := by
  have hraw := controlledSwapGenerator_hermitian D
  have hrel : (relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D)).IsHermitian :=
    hraw.submatrix (copyRelabelEquiv D).symm
  have ht : (TensorGate (1 : Operator r)
      (relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D))).IsHermitian := by
    show (TensorGate _ _)ᴴ = TensorGate _ _
    rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, hrel.eq]
  exact ht.submatrix (controlledCopyReferenceEquiv D r).symm

private theorem controlledReferenceGenerator_norm (D r : ℕ) :
    ‖controlledCopyReferenceGenerator D r‖ ≤ 1 := by
  rw [controlledCopyReferenceGenerator, l2_norm_relabelGate]
  exact (identity_tensor_norm_le r _).trans (by
    rw [l2_norm_relabelGate]
    exact controlledSwapGenerator_norm D)

private theorem controlledReferenceGate_norm (D r : ℕ) (θ : ℝ) :
    ‖controlledCopyReferenceGate D r θ‖ ≤ 1 := by
  rw [controlledCopyReferenceGate, l2_norm_relabelGate]
  apply (identity_tensor_norm_le r _).trans
  apply l2_norm_unitary_le_one
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact controlledSwapGateTensor_conjTranspose_mul D θ

private theorem controlledReferenceGate_remainder_shape (D r : ℕ) (θ : ℝ) (c : ℂ) :
    controlledCopyReferenceGate D r θ - 1 + c • controlledCopyReferenceGenerator D r =
      relabelGate (controlledCopyReferenceEquiv D r)
        (TensorGate (1 : Operator r)
          (relabelGate (copyRelabelEquiv D)
            (controlledSwapRawGate D θ - 1 + c • controlledSwapGenerator D))) := by
  have hid : relabelGate (controlledCopyReferenceEquiv D r)
      (TensorGate (1 : Operator r)
        (relabelGate (copyRelabelEquiv D) (1 : Matrix (Bool × (Fin D × Fin D))
          (Bool × (Fin D × Fin D)) ℂ))) = 1 := by
    rw [relabel_one, tensorGate_one, relabel_one]
  rw [controlledCopyReferenceGate, controlledCopyReferenceGenerator,
    controlledSwapGateTensor]
  change relabelGate _ _ - 1 + c • relabelGate _ _ = _
  rw [← hid]
  ext ⟨⟨a, i⟩, k⟩ ⟨⟨b, j⟩, l⟩
  simp only [relabelGate_apply', controlledCopyReferenceEquiv, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, tensorGate_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, copyRelabelEquiv]
  ring

theorem controlledCopyReferenceGate_sandwich_remainder (D r : ℕ) (θ : ℝ)
    (X : Matrix ((Fin r × Fin (2 * D)) × Fin D)
      ((Fin r × Fin (2 * D)) × Fin D) ℂ) :
    Matrix.traceNorm (controlledCopyReferenceGate D r θ * X *
      (controlledCopyReferenceGate D r θ)ᴴ - X + (Complex.I * (θ : ℂ)) •
        (controlledCopyReferenceGenerator D r * X - X * controlledCopyReferenceGenerator D r)) ≤
      6 * θ ^ 2 * Matrix.traceNorm X := by
  apply controlled_sandwich_remainder _ _ _ θ
    (controlledReferenceGenerator_hermitian D r) (controlledReferenceGenerator_norm D r)
    (controlledReferenceGate_norm D r θ)
  · have hs := controlledReferenceGate_remainder_shape D r θ 0
    simp only [zero_smul, add_zero] at hs
    rw [hs, l2_norm_relabelGate]
    exact (identity_tensor_norm_le r _).trans (by
      rw [l2_norm_relabelGate]
      exact (controlledSwapRawGate_linear_and_quadratic D θ).1)
  · rw [controlledReferenceGate_remainder_shape, l2_norm_relabelGate]
    exact (identity_tensor_norm_le r _).trans (by
      rw [l2_norm_relabelGate]
      exact (controlledSwapRawGate_linear_and_quadratic D θ).2)

end ControlledReferenceTaylor

section ControlledFirstOrder

open scoped Classical ComplexOrder Matrix.Norms.L2Operator

private theorem controlledSwapGenerator_select (D : ℕ) :
    controlledSwapGenerator D = select (fun b : Bool => if b then swapRegisterMatrix D else 0) := by
  ext ⟨b,i,j⟩ ⟨c,k,l⟩
  cases b <;> cases c <;> simp [controlledSwapGenerator, tensorGate_apply, select,
    outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket]

private theorem controlledDensityGenerator_select (D : ℕ) (ρ : Operator D) :
    TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ =
      select (fun b : Bool => if b then ρ else 0) := by
  ext ⟨b,i⟩ ⟨c,j⟩
  cases b <;> cases c <;> simp [tensorGate_apply, select, outerProduct_apply,
      Qatlib.Foundations.PureStateMath.Ket]

theorem controlledCopy_generator_trace_left (D : ℕ) (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    traceRightB (controlledSwapGenerator D * tensorCopyB ρ A) =
      TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ * A := by
  ext ⟨b,i⟩ ⟨c,j⟩
  rw [traceRightB_apply, controlledSwapGenerator_select,
    controlledDensityGenerator_select, select_mul_apply]
  simp only [Prod.fst, Prod.snd]
  have hs (k : Fin D) := select_mul_apply
    (fun b : Bool => if b then swapRegisterMatrix D else 0) (tensorCopyB ρ A)
      b c (i,k) (j,k)
  cases b with
  | false => simp [hs]
  | true =>
    simp only [hs, ↓reduceIte]
    let B : Operator D := A.submatrix (fun p => (true,p)) (fun q => (c,q))
    have hblock : (tensorCopyB ρ A).submatrix
        (fun p : Fin D × Fin D => (true,p)) (fun q => (c,q)) = TensorGate B ρ := by
      ext p q
      rfl
    rw [hblock]
    change Matrix.traceRight (swapRegisterMatrix D * TensorGate B ρ) i j = (ρ * B) i j
    rw [← partialTrace_eq_traceRight, (partial_swap_cross_partial_traces B ρ).2.1]

noncomputable def controlledCopyHamiltonian (D : ℕ) (ρ : Operator D) : Operator (2 * D) :=
  relabelGate (controlDataEquiv D) (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ)

private theorem generator_relabel_left (D : ℕ) (ρ : Operator D)
    (A : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) :
    Matrix.traceRight (relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D) *
      TensorGate (relabelGate (controlDataEquiv D) A) ρ) =
      controlledCopyHamiltonian D ρ * relabelGate (controlDataEquiv D) A := by
  rw [← tensorCopyB_relabel]
  have hm : relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D) *
      relabelGate (copyRelabelEquiv D) (tensorCopyB ρ A) =
      relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D * tensorCopyB ρ A) := by
    exact (Matrix.reindexAlgEquiv ℂ ℂ (copyRelabelEquiv D)).map_mul _ _ |>.symm
  rw [hm, ← traceRightB_relabel, controlledCopy_generator_trace_left]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (controlDataEquiv D)).map_mul _ _

theorem controlledCopy_generator_fin_left (D : ℕ) (ρ : Operator D) (X : Operator (2 * D)) :
    Matrix.traceRight (relabelGate (copyRelabelEquiv D) (controlledSwapGenerator D) *
      TensorGate X ρ) = controlledCopyHamiltonian D ρ * X := by
  have h := generator_relabel_left D ρ (relabelGate (controlDataEquiv D).symm X)
  have hround : relabelGate (controlDataEquiv D) (relabelGate (controlDataEquiv D).symm X) = X := by
    ext i j
    simp only [relabelGate_apply', Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [hround] at h
  exact h

private theorem spectator_generator_trace_left (D r : ℕ) (ρ : Operator D)
    (G : Matrix (Fin (2 * D) × Fin D) (Fin (2 * D) × Fin D) ℂ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) :
    Matrix.traceRight
      (relabelGate (controlledCopyReferenceEquiv D r) (TensorGate (1 : Operator r) G) *
        TensorGate X ρ) =
      fun p q => Matrix.traceRight
        (G * TensorGate (fun i j => X (p.1,i) (q.1,j)) ρ) p.2 q.2 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, relabelGate_apply', controlledCopyReferenceEquiv,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, tensorGate_apply, Matrix.one_apply]
  simp [tensorGate_apply, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum]

theorem controlledCopy_reference_generator_trace_left (D r : ℕ) (ρ : Operator D)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) :
    Matrix.traceRight (controlledCopyReferenceGenerator D r * TensorGate X ρ) =
      TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) * X := by
  rw [controlledCopyReferenceGenerator, spectator_generator_trace_left]
  ext ⟨a,i⟩ ⟨b,j⟩
  rw [controlledCopy_generator_fin_left]
  simp [Matrix.mul_apply, tensorGate_apply, Matrix.one_apply, Fintype.sum_prod_type]

private noncomputable def copySelectLM {I : Type*} [Fintype I] [DecidableEq I] :
    (Bool → Matrix I I ℂ) →ₗ[ℂ] Matrix (Bool × I) (Bool × I) ℂ where
  toFun := select
  map_add' := by
    intro A B
    ext ⟨a,i⟩ ⟨b,j⟩
    simp only [select, Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c A
    ext ⟨a,i⟩ ⟨b,j⟩
    simp [select, mul_ite]

private noncomputable def copySelectRingHom {I : Type*} [Fintype I] [DecidableEq I] :
    (Bool → Matrix I I ℂ) →+* Matrix (Bool × I) (Bool × I) ℂ where
  toFun := select
  map_zero' := by ext ⟨a,i⟩ ⟨b,j⟩; simp [select]
  map_one' := parallel_select_one
  map_add' := copySelectLM.map_add
  map_mul' := fun A B => (parallel_select_mul A B).symm

theorem copy_controlled_exp (D : ℕ) (ρ : Operator D) (θ : ℝ) :
    NormedSpace.exp ((-Complex.I * (θ : ℂ)) •
      TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ) =
      controlOracle (hamiltonianEvolution ρ θ) := by
  letI : NormedAlgebra ℚ (Matrix (Fin D) (Fin D) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hs : Continuous (copySelectRingHom (I := Fin D)) :=
    (copySelectLM (I := Fin D)).continuous_of_finiteDimensional
  have hm := NormedSpace.map_exp (copySelectRingHom (I := Fin D)) hs
    (fun b : Bool => if b then (-Complex.I * (θ : ℂ)) • ρ else 0)
  have he : select (fun b : Bool => if b then (-Complex.I * (θ : ℂ)) • ρ else 0) =
      (-Complex.I * (θ : ℂ)) • TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ := by
    ext ⟨a,i⟩ ⟨b,j⟩
    cases a <;> cases b <;> simp [select, outerProduct_apply,
        Qatlib.Foundations.PureStateMath.Ket, tensorGate_apply]
  rw [show copySelectRingHom (fun b : Bool => if b then
        (-Complex.I * (θ : ℂ)) • ρ else 0) =
      (-Complex.I * (θ : ℂ)) • TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ from he]
    at hm
  refine hm.symm.trans ?_
  change select (NormedSpace.exp _) = controlOracle _
  unfold controlOracle
  congr 1
  funext b
  have hp := NormedSpace.map_exp
    (Pi.evalRingHom (fun _ : Bool => Matrix (Fin D) (Fin D) ℂ) b)
    (continuous_apply b)
    (fun b : Bool => if b then (-Complex.I * (θ : ℂ)) • ρ else 0)
  refine hp.trans ?_
  cases b <;> simp only [Pi.evalRingHom_apply, Bool.false_eq_true, if_false, if_true,
      NormedSpace.exp_zero, hamiltonianEvolution]

private theorem relabel_exp {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    NormedSpace.exp (relabelGate e A) = relabelGate e (NormedSpace.exp A) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap.continuous_of_finiteDimensional A).symm

theorem copyControlledEvolution_hamiltonian (D : ℕ) (ρ : Operator D) (θ : ℝ) :
    copyControlledEvolution ρ θ = HamiltonianEvolution (controlledCopyHamiltonian D ρ) θ := by
  unfold copyControlledEvolution HamiltonianEvolution controlledCopyHamiltonian
  rw [show (-Complex.I * (θ : ℂ)) •
      relabelGate (controlDataEquiv D) (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ) =
      relabelGate (controlDataEquiv D)
        ((-Complex.I * (θ : ℂ)) • TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ) from rfl,
    relabel_exp, copy_controlled_exp]

private theorem copyHamiltonian_hermitian (D : ℕ) (ρ : Operator D) (hρ : ρ.IsHermitian) :
    (controlledCopyHamiltonian D ρ).IsHermitian := by
  have hh : (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ).IsHermitian := by
    show (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) ρ)ᴴ = _
    rw [tensorGate_conjTranspose, hρ.eq,
        (outerProduct_posSemidef (Qatlib.Foundations.PureStateMath.Ket true)).isHermitian.eq]
  exact hh.submatrix (controlDataEquiv D).symm

private theorem copyHamiltonian_norm_le_one (D : ℕ) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    ‖controlledCopyHamiltonian D ρ‖ ≤ 1 := by
  rw [controlledCopyHamiltonian, l2_norm_relabelGate, l2_norm_tensorGate]
  have hp : ‖outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)‖ ≤ 1 := by
    have he : outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool) =
        Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0) := by
      ext b c
      cases b <;> cases c <;> simp [outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket,
          Matrix.diagonal_apply]
    rw [he, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro b; cases b <;> simp)
  nlinarith [density_l2_opNorm_le_one ρ hρ,
    norm_nonneg (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)), norm_nonneg ρ]

theorem traceNorm_relabel_hermitian {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    (relabelGate e X).traceNorm = X.traceNorm := by
  have h1 := positive_trace_preserving_hermitian_trace_contraction
    (CPTPMap.ofEquiv e).toLinearMap (CPTPMap.ofEquiv e).pos (CPTPMap.ofEquiv e).TP hX
  have h2 := positive_trace_preserving_hermitian_trace_contraction
    (CPTPMap.ofEquiv e.symm).toLinearMap (CPTPMap.ofEquiv e.symm).pos
    (CPTPMap.ofEquiv e.symm).TP (hX.submatrix e.symm)
  change (relabelGate e X).traceNorm ≤ X.traceNorm at h1
  change (relabelGate e.symm (relabelGate e X)).traceNorm ≤ (relabelGate e X).traceNorm at h2
  rw [relabelGate_relabelGate] at h2
  exact le_antisymm h1 h2

private theorem controlled_remainder_hermitian
    {I : Type*} [Fintype I] [DecidableEq I]
    (U H X : Matrix I I ℂ) (θ : ℝ) (hH : H.IsHermitian) (hX : X.IsHermitian) :
    (U * X * Uᴴ - X + (Complex.I * (θ : ℂ)) • (H * X - X * H)).IsHermitian := by
  have hc : ((Complex.I * (θ : ℂ)) • (H * X - X * H)).IsHermitian := by
    show ((Complex.I * (θ : ℂ)) • (H * X - X * H))ᴴ = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hH.eq, hX.eq, RCLike.star_def, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    module
  exact ((Matrix.isHermitian_mul_mul_conjTranspose U hX).sub hX).add hc

private theorem traceRight_star {I J : Type*} [Fintype I] [Fintype J]
    (X : Matrix (I × J) (I × J) ℂ) : (Matrix.traceRight X)ᴴ = Matrix.traceRight Xᴴ := by
  ext i j
  simp [Matrix.traceRight, Matrix.conjTranspose_apply, map_sum]

private theorem copy_reference_generator_trace_right (D r : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.IsHermitian) :
    Matrix.traceRight (TensorGate X ρ * controlledCopyReferenceGenerator D r) =
      X * TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) := by
  have h := congrArg Matrix.conjTranspose (controlledCopy_reference_generator_trace_left D r ρ X)
  have hH : (controlledCopyReferenceGenerator D r).IsHermitian := by
    show (controlledCopyReferenceGenerator D r)ᴴ = _
    simp only [controlledCopyReferenceGenerator, relabelGate_apply']
    exact controlledReferenceGenerator_hermitian D r
  rw [traceRight_star, Matrix.conjTranspose_mul, tensorGate_conjTranspose,
    hX.eq, hρ.1.isHermitian.eq, hH.eq, Matrix.conjTranspose_mul,
    tensorGate_conjTranspose, Matrix.conjTranspose_one, (copyHamiltonian_hermitian D ρ hρ.1.isHermitian).eq,
    hX.eq] at h
  exact h

private theorem relabel_controlled_remainder
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (U H X : Matrix I I ℂ) (θ : ℝ) :
    relabelGate e (U * X * Uᴴ - X + (Complex.I * (θ : ℂ)) • (H * X - X * H)) =
      relabelGate e U * relabelGate e X * (relabelGate e U)ᴴ - relabelGate e X +
        (Complex.I * (θ : ℂ)) • (relabelGate e H * relabelGate e X -
          relabelGate e X * relabelGate e H) := by
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  change f (U * X * Uᴴ - X + (Complex.I * (θ : ℂ)) • (H * X - X * H)) =
    f U * f X * (f U)ᴴ - f X + (Complex.I * (θ : ℂ)) • (f H * f X - f X * f H)
  simp only [map_add, map_sub, map_mul, map_smul]
  rw [show f Uᴴ = (f U)ᴴ from (relabel_star e U).symm]

private theorem hamiltonian_left_reference_first_order
    (d r : ℕ) (H : Operator d) (hH : H.IsHermitian) (θ : ℝ)
    (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (hX : X.IsHermitian) :
    Matrix.traceNorm (TensorGate (1 : Operator r) (HamiltonianEvolution H θ) * X *
      (TensorGate (1 : Operator r) (HamiltonianEvolution H θ))ᴴ - X +
      (Complex.I * (θ : ℂ)) • (TensorGate (1 : Operator r) H * X -
        X * TensorGate (1 : Operator r) H)) ≤
      2 * θ ^ 2 * ‖H‖ ^ 2 * X.traceNorm := by
  let Y := X.submatrix Prod.swap Prod.swap
  let e := Equiv.prodComm (Fin d) (Fin r)
  let U := TensorGate (HamiltonianEvolution H θ) (1 : Operator r)
  let K := TensorGate H (1 : Operator r)
  let R := U * Y * Uᴴ - Y + (Complex.I * (θ : ℂ)) • (K * Y - Y * K)
  have hY : Y.IsHermitian := hX.submatrix Prod.swap
  have hK : K.IsHermitian := by
    show Kᴴ = K
    simp only [K, tensorGate_conjTranspose, hH.eq, Matrix.conjTranspose_one]
  have hR : R.IsHermitian := controlled_remainder_hermitian U K Y θ hK hY
  have hround : relabelGate e Y = X := by ext p q; rfl
  have hYn : Y.traceNorm = X.traceNorm := by
    have h := traceNorm_relabel_hermitian e Y hY
    rw [hround] at h
    exact h.symm
  have hshape := relabel_controlled_remainder e U K Y θ
  dsimp only [U, K] at hshape
  rw [relabelGate_prodComm, relabelGate_prodComm, hround] at hshape
  have h := hamiltonian_reference_first_order_remainder d r H θ Y hH
  have hn := traceNorm_relabel_hermitian e R hR
  change (relabelGate e (U * Y * Uᴴ - Y +
      (Complex.I * (θ : ℂ)) • (K * Y - Y * K))).traceNorm = R.traceNorm at hn
  have hn' := (congrArg Matrix.traceNorm hshape).symm.trans hn
  calc
    _ = R.traceNorm := hn'
    _ ≤ 2 * θ ^ 2 * ‖H‖ ^ 2 * Y.traceNorm := h
    _ = _ := by rw [hYn]

private theorem copy_ideal_reference_first_order (D r : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (θ : ℝ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.IsHermitian) :
    Matrix.traceNorm (TensorGate (1 : Operator r) (copyControlledEvolution ρ θ) * X *
        (TensorGate (1 : Operator r) (copyControlledEvolution ρ θ))ᴴ - X +
      (Complex.I * (θ : ℂ)) •
        (TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) * X -
          X * TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ))) ≤
      2 * θ ^ 2 * X.traceNorm := by
  rw [copyControlledEvolution_hamiltonian]
  have h := hamiltonian_left_reference_first_order (2 * D) r (controlledCopyHamiltonian D ρ)
    (copyHamiltonian_hermitian D ρ hρ.1.isHermitian) θ X hX
  have hh : ‖controlledCopyHamiltonian D ρ‖ ^ 2 ≤ 1 := by
    have hn := copyHamiltonian_norm_le_one D ρ hρ
    nlinarith [norm_nonneg (controlledCopyHamiltonian D ρ)]
  refine h.trans ?_
  calc
    _ = (2 * θ ^ 2 * X.traceNorm) * ‖controlledCopyHamiltonian D ρ‖ ^ 2 := by ring
    _ ≤ (2 * θ ^ 2 * X.traceNorm) * 1 :=
      mul_le_mul_of_nonneg_left hh
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg θ)) (Matrix.traceNorm_nonneg X))
    _ = _ := mul_one _

private theorem copy_actual_reference_first_order (D r : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (θ : ℝ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm (ChannelAmplification (controlledCopyChannel ρ hρ θ).map r X - X +
      (Complex.I * (θ : ℂ)) •
        (TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) * X -
          X * TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ))) ≤
      6 * θ ^ 2 * X.traceNorm := by
  let Y := TensorGate X ρ
  let U := controlledCopyReferenceGate D r θ
  let H := controlledCopyReferenceGenerator D r
  let R := U * Y * Uᴴ - Y + (Complex.I * (θ : ℂ)) • (H * Y - Y * H)
  have hY : Y.PosSemidef := hX.kronecker hρ.1
  have hH := controlledReferenceGenerator_hermitian D r
  have hR : R.IsHermitian := controlled_remainder_hermitian U H Y θ hH hY.isHermitian
  have hYn : Y.traceNorm = X.traceNorm := by
    rw [traceNorm_tensorGate X hX ρ hρ.1, density_traceNorm_eq_one ρ hρ, mul_one]
  have htrace : Matrix.traceRight Y = X := by
    ext p q
    have ht : ∑ k, ρ k k = 1 := hρ.2
    simp only [Y, Matrix.traceRight, Matrix.of_apply, tensorGate_apply]
    rw [← Finset.mul_sum, ht, mul_one]
  have hshape : Matrix.traceRight R =
      ChannelAmplification (controlledCopyChannel ρ hρ θ).map r X - X +
      (Complex.I * (θ : ℂ)) •
        (TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) * X -
          X * TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ)) := by
    dsimp only [R, U, H, Y]
    rw [Matrix.traceRight_add, Matrix.traceRight_sub, Matrix.traceRight_smul,
      Matrix.traceRight_sub, ← controlledCopy_reference_actual_bridge,
      htrace, controlledCopy_reference_generator_trace_left,
      copy_reference_generator_trace_right D r ρ hρ X hX.isHermitian]
    rfl
  rw [← hshape]
  calc
    _ ≤ R.traceNorm := traceRight_hermitian_trace_contraction R hR
    _ ≤ 6 * θ ^ 2 * Y.traceNorm := controlledCopyReferenceGate_sandwich_remainder D r θ Y
    _ = 6 * θ ^ 2 * X.traceNorm := by rw [hYn]

theorem controlled_copy_one_step_reference_error
    (D r : ℕ) (ρ : Operator D) (hρ : IsDensityOperator ρ) (θ : ℝ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm (ChannelAmplification (controlledCopyChannel ρ hρ θ).map r X -
      MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution ρ θ)) X) ≤
      8 * θ ^ 2 * (Matrix.trace X).re := by
  let C := (Complex.I * (θ : ℂ)) •
    (TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ) * X -
      X * TensorGate (1 : Operator r) (controlledCopyHamiltonian D ρ))
  have hsplit : ChannelAmplification (controlledCopyChannel ρ hρ θ).map r X -
      MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution ρ θ)) X =
      (ChannelAmplification (controlledCopyChannel ρ hρ θ).map r X - X + C) -
        (MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution ρ θ)) X - X + C) := by
    abel
  rw [hsplit]
  have h1 := copy_actual_reference_first_order D r ρ hρ θ X hX
  have h2 := copy_ideal_reference_first_order D r ρ hρ θ X hX.isHermitian
  have h := (traceNorm_sub_le _ _).trans (add_le_add h1 h2)
  exact h.trans_eq (by rw [psd_traceNorm_eq_trace X hX]; ring)

end ControlledFirstOrder

section ControlledFreshError

open scoped ComplexOrder Matrix.Norms.L2Operator

private theorem controlled_conj_trace {I : Type*} [Fintype I] [DecidableEq I]
    (U X : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.trace (MatrixMap.conj U X) = Matrix.trace X := by
  change Matrix.trace (U * X * Uᴴ) = Matrix.trace X
  rw [Matrix.trace_mul_cycle]
  have hu : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hU
  rw [hu, Matrix.one_mul]

private theorem controlled_tensor_pow {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix J J ℂ) (m : ℕ) :
    (TensorGate (1 : Matrix I I ℂ) A) ^ m = TensorGate (1 : Matrix I I ℂ) (A ^ m) := by
  induction m with
  | zero => simp [tensorGate_one]
  | succ m ih => rw [pow_succ, ih, tensorGate_mul, Matrix.one_mul, pow_succ]

private theorem controlledCopy_equal_step_error (D r : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (θ : ℝ) (m : ℕ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm
      (ChannelAmplification (copyChannelPower (controlledCopyChannel ρ hρ θ) m).map r X -
        MatrixMap.conj ((TensorGate (1 : Operator r) (copyControlledEvolution ρ θ)) ^ m) X) ≤
      8 * (m : ℝ) * θ ^ 2 * (Matrix.trace X).re := by
  let T := controlledCopyChannel ρ hρ θ
  let U := TensorGate (1 : Operator r) (copyControlledEvolution ρ θ)
  have hU : U ∈ Matrix.unitaryGroup (Fin r × Fin (2 * D)) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (copyControlledEvolution_unitarity ρ hρ.1.isHermitian θ)
  induction m with
  | zero =>
    have hid : ChannelAmplification (LinearMap.id : Operator (2 * D) →ₗ[ℂ] Operator (2 * D)) r X = X := by
      ext p q
      rfl
    simp only [copyChannelPower, QuantumChannel.id, pow_zero, Nat.cast_zero, mul_zero, zero_mul]
    rw [hid, conjMap_apply]
    simp
  | succ m ih =>
    let A := ChannelAmplification (copyChannelPower T m).map r X
    let B := MatrixMap.conj (U ^ m) X
    have hA : A.PosSemidef := (copyChannelPower T m).completelyPositive r X hX
    have hB : B.PosSemidef := hX.mul_mul_conjTranspose_same (U ^ m)
    have hBt : Matrix.trace B = Matrix.trace X := controlled_conj_trace _ X (pow_mem hU m)
    have hrecA : ChannelAmplification (copyChannelPower T (m + 1)).map r X =
        ChannelAmplification T.map r A := by
      ext ⟨a,i⟩ ⟨b,j⟩
      rfl
    have hrecB : MatrixMap.conj (U ^ (m + 1)) X = MatrixMap.conj U B := by
      simp only [B, conjMap_apply, pow_succ', Matrix.conjTranspose_mul]
      noncomm_ring
    have he : ChannelAmplification T.map r A - MatrixMap.conj U B =
        ChannelAmplification T.map r (A - B) +
          (ChannelAmplification T.map r B - MatrixMap.conj U B) := by
      rw [amplification_sub]
      abel
    have hc := channel_reference_hermitian_trace_contraction T (hA.isHermitian.sub hB.isHermitian)
    have hl := controlled_copy_one_step_reference_error D r ρ hρ θ B hB
    rw [hBt] at hl
    change Matrix.traceNorm (ChannelAmplification (copyChannelPower T (m + 1)).map r X -
      MatrixMap.conj (U ^ (m + 1)) X) ≤ _
    rw [hrecA, hrecB]
    rw [he]
    have ht := (Matrix.traceNorm_add_le _ _).trans (add_le_add hc hl)
    have hi : (A - B).traceNorm ≤ 8 * (m : ℝ) * θ ^ 2 * (Matrix.trace X).re := ih
    have hsum := ht.trans (add_le_add hi (le_refl _))
    exact hsum.trans_eq (by push_cast; ring)

theorem controlled_copy_fresh_global_error
    (D r n : ℕ) (hn : 0 < n) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ)
    (hX : X.PosSemidef) :
    Matrix.traceNorm (ChannelAmplification (controlledCopyRun ρ hρ t n).map r X -
      MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution ρ t)) X) ≤
      8 * t ^ 2 / (n : ℝ) * (Matrix.trace X).re := by
  have h := controlledCopy_equal_step_error D r ρ hρ (t / (n : ℝ)) n X hX
  rw [controlled_tensor_pow, copyControlledEvolution_pow, nat_mul_div_self hn t] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  convert! h using 1
  field_simp

end ControlledFreshError

noncomputable local instance (D : ℕ) : DecidableEq (Fin D) := Classical.decEq (Fin D)
noncomputable local instance (D : ℕ) : DecidableEq (Fin (2 * D)) := Classical.decEq (Fin (2 * D))

def trueSectorIdx (D : ℕ) (j : Fin D) : Fin (2 * D) := ⟨D + j.val, by omega⟩

theorem trueSectorIdx_apply (D : ℕ) (j : Fin D) :
    trueSectorIdx D j = controlDataEquiv D (true, j) := by
  apply Fin.ext
  simp [trueSectorIdx, controlDataEquiv, finProdFinEquiv, boolEquivFin2, Nat.add_comm]

theorem trueSectorIdx_inj (D : ℕ) {a b : Fin D} (h : trueSectorIdx D a = trueSectorIdx D b) :
    a = b := by
  have hh := congrArg Fin.val h
  have h' : (D : ℕ) + a.val = D + b.val := by
    simpa only [trueSectorIdx, Fin.val_mk] using! hh
  exact Fin.ext (by omega)

noncomputable def trueSectorι (D : ℕ) : Matrix (Fin (2 * D)) (Fin D) ℂ :=
  fun i j => if i = trueSectorIdx D j then 1 else 0

private theorem delta_star_mul_delta {n : Type} [Fintype n] [DecidableEq n]
    {a b : n} (h : a = b) :
    (∑ k, (starRingEnd ℂ) (if k = a then 1 else 0) * (if k = b then 1 else 0)) = 1 := by
  subst h
  have h1 : (∑ k, (starRingEnd ℂ) (if k = a then 1 else 0) * (if k = a then 1 else 0))
      = (starRingEnd ℂ) (if a = a then 1 else 0) * (if a = a then 1 else 0) :=
    Fintype.sum_eq_single a (fun k hk => by
      show (starRingEnd ℂ) (if k = a then 1 else 0) * (if k = a then 1 else 0) = 0
      simp [hk])
  simpa using! h1

private theorem delta_star_mul_delta_ne {n : Type} [Fintype n] [DecidableEq n]
    {a b : n} (h : a ≠ b) :
    (∑ k, (starRingEnd ℂ) (if k = a then 1 else 0) * (if k = b then 1 else 0)) = 0 := by
  refine Fintype.sum_eq_zero _ fun k => ?_
  by_cases hk : k = a
  · rw [if_pos hk, if_neg (fun hkb => h (hk.symm.trans hkb))]
    simp
  · rw [if_neg hk]
    simp

theorem trueSectorι_isometry (D : ℕ) : (trueSectorι D).Isometry := by
  classical
  ext i j
  have hmul : ((trueSectorι D)ᴴ * (trueSectorι D)) i j
      = ∑ k, (starRingEnd ℂ) (if k = trueSectorIdx D i then 1 else 0)
        * (if k = trueSectorIdx D j then 1 else 0) := by
    simp [trueSectorι, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hmul, Matrix.one_apply]
  by_cases hij : trueSectorIdx D i = trueSectorIdx D j
  · have h1 := delta_star_mul_delta hij
    have hij' : i = j := trueSectorIdx_inj D hij
    simp only [hij', if_true] at h1 ⊢
    exact h1
  · have h1 := delta_star_mul_delta_ne hij
    have hij' : i ≠ j := fun h => hij (by rw [h])
    simp only [hij'] at h1 ⊢
    exact h1

theorem trueSectorι_star_mul (D : ℕ) : (trueSectorι D)ᴴ * trueSectorι D = 1 := by
  show (trueSectorι D).Isometry
  exact trueSectorι_isometry D

theorem traceNorm_embed_mul (D : ℕ) (E : Operator D) (ι : Matrix (Fin (2 * D)) (Fin D) ℂ)
    (hι : (ιᴴ : Matrix (Fin D) (Fin (2 * D)) ℂ) * ι = 1) :
    Matrix.traceNorm ((ι * E) * ιᴴ) = E.traceNorm := by
  have key : ∀ u : Matrix (Fin (2 * D)) (Fin D) ℂ, uᴴ * u = 1 →
      Matrix.traceNorm ((u * E) * uᴴ) = E.traceNorm := by
    intro u hu
    have hu' : u.Isometry := hu
    exact (Matrix.traceNorm_isometry_right hu').trans (Matrix.traceNorm_isometry_left hu')
  exact key ι hι

theorem traceNorm_trueSector (D : ℕ) (E : Operator D) :
    Matrix.traceNorm ((trueSectorι D * E) * (trueSectorι D)ᴴ) = E.traceNorm := by
  refine traceNorm_embed_mul D E (trueSectorι D) ?_
  show (trueSectorι D)ᴴ * trueSectorι D = 1
  exact trueSectorι_isometry D

theorem controlled_copy_actual_cptp_and_false_block
    (D : ℕ) (ρ : Operator D) (hρ : IsDensityOperator ρ) (θ : ℝ) (X : Operator D) :
    let e := controlDataEquiv D
    let Y :=
        relabelGate e
        (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) X)
    (controlledCopyChannel ρ hρ θ).map Y = Y := by
  (try dsimp only)
  rw [controlledCopyChannel, controlledCopyChannelMap_relabel D ρ θ,
    controlledCopyRawMap_ketFalse D ρ θ X hρ.2]

end Qatlib.Concepts.CopyEvolution.Discriminate
