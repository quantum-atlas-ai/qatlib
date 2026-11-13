/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout

/-!
# Spectral Label Laws for Copy Phase Estimation

This module derives the spectral distribution of ideal copy driven phase estimation from a
unitary diagonalization of the density operator. `copyQPEIdealOutput_spectral_label` expresses
each label mass as an eigenvalue weighted sum of squared phase kernel amplitudes at phases `-eig
i / 2`.

Event projectors transfer trace norm bounds on output matrices to errors in label event masses.
`copy_qpe_actual_spectral_label_event` then connects the actual fresh copy execution with the
spectral law, in the density matrix exponentiation and phase estimation setting of
[LloydMohseniRebentrost2014] and [NielsenChuang2010].

## Main statements

* `copyQPE_evolution_spectral` computes the time pi evolution in a unitary eigenbasis.
* `copyQPEIdealOutput_spectral_label` gives the ideal eigenvalue weighted phase kernel formula.
* `copyQPELabelMass_event_error_of_trace_eq` improves the event error bound to half the trace
  norm when traces agree.
* `copy_qpe_actual_spectral_label_event` bounds actual spectral event error by `8 * (M - 1) *
  pi^2 / n`.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014], Quantum principal component analysis.
* [Nielsen and Chuang, 2010][NielsenChuang2010], Quantum Computation and Quantum Information.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
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
open scoped Classical ComplexOrder

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
section CopySpectralReadout

open scoped Classical ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

/-- Conjugating the outer product of a state by any matrix gives the outer product of the state
after applying that matrix. -/
private theorem copyQPE_outer_conj {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) :
    MatrixMap.conj U (outerProduct ψ) = outerProduct (ApplyGate U ψ) := by
  ext i j
  simp only [conjMap_apply, outerProduct_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ApplyGate, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [RCLike.star_def]
  ring

/-- Given a unitary diagonalization of `rho` with real eigenvalues, computes its time pi
Hamiltonian evolution by exponentiating each diagonal eigenvalue and conjugating back by the
unitary eigenbasis. -/
theorem copyQPE_evolution_spectral (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) :
    hamiltonianEvolution ρ Real.pi =
      V * Matrix.diagonal (fun i => Complex.exp (-Complex.I * (Real.pi : ℂ) * (eig i : ℂ))) * Vᴴ := by
  let U : unitary (Operator D) := ⟨V, hV⟩
  let f := Unitary.conjStarAlgAut ℂ (Operator D) U
  let A := Matrix.diagonal (fun i => -Complex.I * (Real.pi : ℂ) * (eig i : ℂ))
  letI : NormedAlgebra ℚ (Operator D) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hm := NormedSpace.map_exp f f.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional A
  have he : f A = (-Complex.I * (Real.pi : ℂ)) • ρ := by
    rw [hs]
    simp only [f, Unitary.conjStarAlgAut_apply, A]
    change V * Matrix.diagonal (fun i => -Complex.I * (Real.pi : ℂ) * (eig i : ℂ)) * Vᴴ = _
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  rw [he] at hm
  unfold hamiltonianEvolution
  refine hm.symm.trans ?_
  change V * NormedSpace.exp A * Vᴴ = _
  rw [Matrix.exp_diagonal]
  change V * Matrix.diagonal (NormedSpace.exp _) * Vᴴ = _
  apply congrArg (fun B : Operator D => V * B * Vᴴ)
  apply congrArg (Matrix.diagonal : (Fin D → ℂ) → Operator D)
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

/-- Applying a matrix to basis state `i` yields its `i`th column as a state vector. -/
private theorem copyQPE_column (D : ℕ) (V : Operator D) (i : Fin D) :
    ApplyGate V (Qatlib.Foundations.PureStateMath.Ket i) = fun j => V j i := by
  funext j
  simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- Every column of a unitary matrix is a normalized state vector. -/
private theorem copyQPE_column_normalized (D : ℕ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) :
    Normalized (fun j => V j i) := by
  rw [← copyQPE_column]
  exact normalized_applyGate hV (normalized_ket i)

/-- Expands a matrix of the form `V * diagonal eig * Vᴴ` as the sum of column outer products of
`V`, weighted by the real diagonal coefficients. -/
private theorem copyQPE_spectral_density_sum (D : ℕ) (V : Operator D) (eig : Fin D → ℝ) :
    V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ =
      ∑ i, (eig i : ℂ) • outerProduct (fun j => V j i) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.star_def]
  ring

/-- For a unitary diagonalization of `rho`, its `i`th eigenvector column acquires phase `exp (2
* pi * I * (-eig i / 2))` under time pi Hamiltonian evolution. -/
private theorem copyQPE_eigenphase (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) (i : Fin D) :
    ApplyGate (hamiltonianEvolution ρ Real.pi) (fun j => V j i) =
      Complex.exp (2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ)) • (fun j => V j i) := by
  have hVV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV
  have huv : hamiltonianEvolution ρ Real.pi * V =
      V * Matrix.diagonal (fun j => Complex.exp (-Complex.I * (Real.pi : ℂ) * (eig j : ℂ))) := by
    rw [copyQPE_evolution_spectral D ρ V eig hV hs, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hphase : -Complex.I * (Real.pi : ℂ) * (eig i : ℂ) =
      2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ) := by push_cast; ring
  funext j
  have h := congrArg (fun A : Operator D => A j i) huv

  rw [Matrix.mul_diagonal] at h
  simp only [Matrix.of_apply, Matrix.mul_apply] at h
  change (∑ k, hamiltonianEvolution ρ Real.pi j k * V k i) =
    Complex.exp (2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ)) * V j i
  rw [h, hphase, mul_comm]

/-- Ideal copy program execution on a pure state outer product equals the outer product of the
corresponding pure state circuit execution with the ideal controlled evolution oracle. -/
private theorem copyQPEIdealProgram_outer (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D))) (ψ : QState (Fin M × (Bool × Fin D))) :
    copyQPEIdealProgram D M ρ C (outerProduct ψ) =
      outerProduct (Run (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [copyQPEIdealProgram, Run, copyQPE_outer_conj, ih]

/-- Packages ideal copy program execution as a complex linear matrix map by composing gate
conjugations and ideal controlled evolution conjugations along the circuit. -/
private noncomputable def copyQPEIdealProgramMap (D M : ℕ) (ρ : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) →
      MatrixMap (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ
  | [] => LinearMap.id
  | Step.gate U :: C => (copyQPEIdealProgramMap D M ρ C).comp (MatrixMap.conj U)
  | Step.query :: C => (copyQPEIdealProgramMap D M ρ C).comp
      (MatrixMap.conj (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))))

/-- Applying the linear map `copyQPEIdealProgramMap` agrees with the recursive matrix execution
`copyQPEIdealProgram`. -/
private theorem copyQPEIdealProgramMap_apply (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D)))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    copyQPEIdealProgramMap D M ρ C X = copyQPEIdealProgram D M ρ C X := by
  induction C generalizing X with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [copyQPEIdealProgramMap, LinearMap.comp_apply,
      copyQPEIdealProgram, ih]

/-- For a positive phase register size, initialization sends a real weighted sum of data column
outer products to the same weighted sum of initialized joint state outer products. -/
private theorem copyQPEInput_spectral_sum (D M : ℕ) (hM : 0 < M)
    (V : Operator D) (eig : Fin D → ℝ) :
    copyQPEInput D M (∑ i, (eig i : ℂ) • outerProduct (fun j => V j i)) =
      ∑ i, (eig i : ℂ) • outerProduct
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (fun j => V j i))) := by
  rw [copyQPEInput, dif_pos hM]
  simp only [outerProduct_tensorState]
  ext ⟨a,b,i⟩ ⟨c,d,j⟩
  simp only [tensorGate_apply, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- On the outer product of an eigenstate with eigenphase `phi`, the ideal counted phase
estimation program outputs the outer product with amplitudes `qpeKernel M phi z` times the
data eigenstate and with false control. -/
private theorem copyQPEIdealProgram_eigen (D M : ℕ) (hM : 0 < M) (ρ : Operator D)
    (ψ : QState (Fin D)) (φ : ℝ)
    (hψ : ApplyGate (hamiltonianEvolution ρ Real.pi) ψ =
      Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    copyQPEIdealProgram D M ρ (countedPhaseCircuit M) (copyQPEInput D M (outerProduct ψ)) =
      outerProduct (fun p : Fin M × (Bool × Fin D) =>
        if p.2.1 then 0 else qpeKernel M φ p.1 * ψ p.2.2) := by
  rw [copyQPEInput, dif_pos hM, ← outerProduct_tensorState, ← outerProduct_tensorState,
    copyQPEIdealProgram_outer, (counted_offgrid_qpe_clean_flag M hM
      (hamiltonianEvolution ρ Real.pi) ψ).1, qpeOutput_eigen M _ ψ φ hψ]
  rfl

/-- For normalized data and false control, the phase label mass of the phase kernel output outer
product equals the squared norm of the kernel amplitude at that label. -/
private theorem copyQPELabelMass_pure_kernel (D M : ℕ) (ψ : QState (Fin D)) (hψ : Normalized ψ)
    (φ : ℝ) (z : Fin M) :
    copyQPELabelMass D M (outerProduct (fun p : Fin M × (Bool × Fin D) =>
      if p.2.1 then 0 else qpeKernel M φ p.1 * ψ p.2.2)) z = ‖qpeKernel M φ z‖ ^ 2 := by
  unfold copyQPELabelMass
  have he : (outerProduct (fun p : Fin M × (Bool × Fin D) =>
      if p.2.1 then 0 else qpeKernel M φ p.1 * ψ p.2.2)).submatrix
      (fun p => (z,p)) (fun p => (z,p)) =
      outerProduct (fun p : Bool × Fin D => if p.1 then 0 else qpeKernel M φ z * ψ p.2) := rfl
  rw [he, trace_outerProduct, Complex.ofReal_re]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_add, norm_mul, mul_pow]
  rw [← Finset.mul_sum, hψ, mul_one]

/-- Phase label mass distributes over a finite real weighted sum of matrices, yielding the same
weighted sum of label masses. -/
private theorem copyQPELabelMass_weighted_sum (D M : ℕ) (c : Fin D → ℝ)
    (X : Fin D → Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (z : Fin M) :
    copyQPELabelMass D M (∑ i, (c i : ℂ) • X i) z =
      ∑ i, c i * copyQPELabelMass D M (X i) z := by
  simp only [copyQPELabelMass, Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- For a positive phase register size and a unitary diagonalization of `rho` with real
eigenvalues, the ideal output mass at label `z` is the sum of `eig i * norm (qpeKernel M
(-eig i / 2) z)^2` over all eigenvalue indices. -/
theorem copyQPEIdealOutput_spectral_label (D M : ℕ) (hM : 0 < M)
    (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) (z : Fin M) :
    copyQPELabelMass D M (copyQPEIdealOutput D M ρ) z =
      ∑ i, eig i * ‖qpeKernel M (-eig i / 2) z‖ ^ 2 := by
  have hρsum : ρ = ∑ i, (eig i : ℂ) • outerProduct (fun j => V j i) :=
    hs.trans (copyQPE_spectral_density_sum D V eig)
  have hinput := copyQPEInput_spectral_sum D M hM V eig
  rw [← hρsum] at hinput
  have hpure (i : Fin D) := copyQPEIdealProgram_eigen D M hM ρ (fun j => V j i)
    (-eig i / 2) (copyQPE_eigenphase D ρ V eig hV hs i)
  have hpure' (i : Fin D) :
      copyQPEIdealProgram D M ρ (countedPhaseCircuit M)
        (outerProduct (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (fun j => V j i)))) =
        outerProduct (fun p : Fin M × (Bool × Fin D) =>
          if p.2.1 then 0 else qpeKernel M (-eig i / 2) p.1 * V p.2.2 i) := by
    have h := hpure i
    rw [copyQPEInput, dif_pos hM, ← outerProduct_tensorState, ← outerProduct_tensorState] at h
    exact h
  have hout : copyQPEIdealOutput D M ρ =
      ∑ i, (eig i : ℂ) • outerProduct (fun p : Fin M × (Bool × Fin D) =>
        if p.2.1 then 0 else qpeKernel M (-eig i / 2) p.1 * V p.2.2 i) := by
    unfold copyQPEIdealOutput
    rw [← copyQPEIdealProgramMap_apply, hinput, map_sum]
    simp only [map_smul, copyQPEIdealProgramMap_apply, hpure']
  rw [hout, copyQPELabelMass_weighted_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [copyQPELabelMass_pure_kernel D M _ (copyQPE_column_normalized D V hV i)]

/-- Defines the diagonal projector selecting all control and data coordinates whose phase label
belongs to the event `E`. -/
private noncomputable def copyQPEEventProjector (D M : ℕ) (E : Finset (Fin M)) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  Matrix.diagonal (fun p => if p.1 ∈ E then 1 else 0)

/-- The phase label event projector has Euclidean operator norm at most one. -/
private theorem copyQPEEventProjector_norm (D M : ℕ) (E : Finset (Fin M)) :
    ‖copyQPEEventProjector D M E‖ ≤ 1 := by
  rw [copyQPEEventProjector, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro p; split_ifs <;> simp)

/-- The real trace of the event projector times a matrix equals the sum of that matrix's phase
label masses over the event. -/
private theorem copyQPE_event_trace (D M : ℕ) (E : Finset (Fin M))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    (Matrix.trace (copyQPEEventProjector D M E * X)).re =
      ∑ z ∈ E, copyQPELabelMass D M X z := by
  have hc : Matrix.trace (copyQPEEventProjector D M E * X) =
      ∑ z ∈ E, Matrix.trace (X.submatrix (fun p => (z,p)) (fun p => (z,p))) := by
    unfold copyQPEEventProjector
    rw [Matrix.trace, Fintype.sum_prod_type]
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    have he (z : Fin M) :
        (∑ p : Bool × Fin D, (if z ∈ E then (1 : ℂ) else 0) * X (z,p) (z,p)) =
        if z ∈ E then Matrix.trace (X.submatrix (fun p => (z,p)) (fun p => (z,p))) else 0 := by
      by_cases hz : z ∈ E <;> simp [hz, Matrix.trace, Matrix.submatrix_apply]
    simp only [he]
    simp
  have h := congrArg Complex.re hc
  simpa only [Complex.re_sum, copyQPELabelMass] using! h

/-- For any two output matrices, the absolute difference of their total phase label masses on an
event is at most the trace norm of their difference. -/
theorem copyQPELabelMass_event_error (D M : ℕ) (E : Finset (Fin M))
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    |(∑ z ∈ E, copyQPELabelMass D M X z) - (∑ z ∈ E, copyQPELabelMass D M Y z)| ≤
      Matrix.traceNorm (X - Y) := by
  rw [← copyQPE_event_trace D M E X, ← copyQPE_event_trace D M E Y,
    ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub]
  calc
    _ ≤ ‖Matrix.trace (copyQPEEventProjector D M E * (X - Y))‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (copyQPEEventProjector D M E * (X - Y)) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖copyQPEEventProjector D M E‖ * Matrix.traceNorm (X - Y) :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * Matrix.traceNorm (X - Y) :=
      mul_le_mul_of_nonneg_right (copyQPEEventProjector_norm D M E) (Matrix.traceNorm_nonneg _)
    _ = _ := one_mul _

/-- For two matrices with equal traces, the absolute difference of their total phase label
masses on an event is at most half the trace norm of their difference. -/
theorem copyQPELabelMass_event_error_of_trace_eq (D M : ℕ) (E : Finset (Fin M))
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (htrace : Matrix.trace X = Matrix.trace Y) :
    |(∑ z ∈ E, copyQPELabelMass D M X z) - (∑ z ∈ E, copyQPELabelMass D M Y z)| ≤
      Matrix.traceNorm (X - Y) / 2 := by
  let B : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
    Matrix.diagonal (fun p => if p.1 ∈ E then (1 / 2 : ℂ) else -(1 / 2))
  have hB : B = copyQPEEventProjector D M E - (1 / 2 : ℂ) •
      (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) := by
    ext p q
    by_cases hpq : p = q
    · subst q
      by_cases hp : p.1 ∈ E <;>
        norm_num [B, copyQPEEventProjector, Matrix.diagonal_apply, Matrix.one_apply, hp]
    · simp [B, copyQPEEventProjector, Matrix.diagonal_apply, Matrix.one_apply, hpq]
  have hnorm : ‖B‖ ≤ (1 / 2 : ℝ) := by
    dsimp only [B]
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
      (by intro p; split_ifs <;> norm_num)
  have hzero : Matrix.trace (X - Y) = 0 := by
    rw [Matrix.trace_sub, htrace, sub_self]
  have hcenter : Matrix.trace (B * (X - Y)) =
      Matrix.trace (copyQPEEventProjector D M E * (X - Y)) := by
    rw [hB, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul, hzero, smul_zero, sub_zero]
  rw [← copyQPE_event_trace D M E X, ← copyQPE_event_trace D M E Y,
    ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub, ← hcenter]
  calc
    _ ≤ ‖Matrix.trace (B * (X - Y))‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (B * (X - Y)) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖B‖ * Matrix.traceNorm (X - Y) := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ (1 / 2) * Matrix.traceNorm (X - Y) :=
      mul_le_mul_of_nonneg_right hnorm (Matrix.traceNorm_nonneg _)
    _ = Matrix.traceNorm (X - Y) / 2 := by ring

/-- For a density operator with a unitary diagonalization and nonnegative eigenvalues, at least
two phase labels, and positive `n`, the actual mass of any label event differs from the
eigenvalue weighted phase kernel event mass by at most `8 * (M - 1) * pi^2 / n` in the
density matrix exponentiation setting of [LloydMohseniRebentrost2014]. -/
theorem copy_qpe_actual_spectral_label_event
    (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hρ : IsDensityOperator ρ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ)
    (_heig : ∀ i, 0 ≤ eig i) (E : Finset (Fin M)) :
    |(∑ z ∈ E, copyQPELabelMass D M (copyQPEOutput D M n ρ) z) -
      (∑ i, eig i * (∑ z ∈ E, ‖qpeKernel M (-eig i / 2) z‖ ^ 2))| ≤
      8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) := by
  have h := copyQPELabelMass_event_error D M E (copyQPEOutput D M n ρ) (copyQPEIdealOutput D M ρ)
  have he : (∑ z ∈ E, copyQPELabelMass D M (copyQPEIdealOutput D M ρ) z) =
      ∑ i, eig i * (∑ z ∈ E, ‖qpeKernel M (-eig i / 2) z‖ ^ 2) := by
    simp only [copyQPEIdealOutput_spectral_label D M (by omega) ρ V eig hV hs]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [he] at h
  exact h.trans (copy_qpe_actual_program_state_error D M n hM hn ρ hρ).2.2

end CopySpectralReadout
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
