/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.SelfTomographyOnGridOutputStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CopyEvolution.SelfTomography
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

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

private theorem copyQPE_column (D : ℕ) (V : Operator D) (i : Fin D) :
    ApplyGate V (Qatlib.Foundations.PureStateMath.Ket i) = fun j => V j i := by
  funext j
  simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

private theorem copyQPE_spectral_density_sum (D : ℕ) (V : Operator D) (eig : Fin D → ℝ) :
    V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ =
      ∑ i, (eig i : ℂ) • outerProduct (fun j => V j i) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,
    Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.star_def]
  ring

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
  (try dsimp only at h)
  rw [Matrix.mul_diagonal] at h
  simp only [Matrix.mul_apply] at h
  change (∑ k, hamiltonianEvolution ρ Real.pi j k * V k i) =
    Complex.exp (2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ)) * V j i
  rw [h, hphase, mul_comm]

private theorem copyQPEIdealProgram_outer (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D))) (ψ : QState (Fin M × (Bool × Fin D))) :
    copyQPEIdealProgram D M ρ C (outerProduct ψ) =
      outerProduct (Run (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [copyQPEIdealProgram, Run, copyQPE_outer_conj, ih]

private noncomputable def copyQPEIdealProgramMap (D M : ℕ) (ρ : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) →
      MatrixMap (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ
  | [] => LinearMap.id
  | Step.gate U :: C => (copyQPEIdealProgramMap D M ρ C).comp (MatrixMap.conj U)
  | Step.query :: C => (copyQPEIdealProgramMap D M ρ C).comp
      (MatrixMap.conj (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))))

private theorem copyQPEIdealProgramMap_apply (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D)))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    copyQPEIdealProgramMap D M ρ C X = copyQPEIdealProgram D M ρ C X := by
  induction C generalizing X with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [copyQPEIdealProgramMap, LinearMap.comp_apply,
      copyQPEIdealProgram, ih]

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

theorem selfTomography_spectral_output (D M : ℕ) (hM : 0 < M)
    (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) :
    copyQPEIdealOutput D M ρ =
      ∑ i, (eig i : ℂ) • outerProduct (fun p : Fin M × (Bool × Fin D) =>
        if p.2.1 then 0 else qpeKernel M (-eig i / 2) p.1 * V p.2.2 i) := by
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
  exact hout

theorem selfTomographyOnGridOutput : SelfTomographyOnGridOutput := by
  classical
  intro D M ρ V eig hM _hρ hV hs _he hg
  choose z hz using hg
  refine ⟨z, hz, ?_⟩
  rw [selfTomography_spectral_output D M hM ρ V eig hV hs]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext p
  have heq : -eig i / 2 = ((z i).val : ℝ)/M +
      ((⌊-eig i / 2 - ((z i).val : ℝ)/M + 1/2⌋ : ℤ) : ℝ) := by
    have h := abs_eq_zero.mp (hz i)
    linarith
  rw [heq, qpeKernel_int_add,
    (offgrid_phase_geometric_and_periodic M (((z i).val : ℝ)/M) p.1 hM).2.2 (z i)]
  by_cases hb : p.2.1 = true
  · simp [hb]
  · simp [hb, Qatlib.Foundations.PureStateMath.Ket]
end Qatlib.Concepts.CopyEvolution.SelfTomography
