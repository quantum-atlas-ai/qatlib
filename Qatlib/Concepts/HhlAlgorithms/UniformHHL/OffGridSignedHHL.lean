/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter
import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

/-!
# Uniform HHL for signed off-grid spectra

This module proves correctness of the uniform phase-estimation HHL circuit for real eigenphases
of either sign, separated from zero and bounded in absolute value by `1/4`. The spectral filter
realizes a scaled reciprocal, connecting the circuit to the pseudoinverse solution of
[HarrowHassidimLloyd2009].

The results include full-workspace error, positive Born success probability, normalized solution
accuracy, oracle perturbation bounds, and explicit finite-resolution parameters.

## Main statements

* `uniform_offgrid_signed_hhl_full_workspace_error`: error at most `η` with the stated grid
  budget.
* `uniform_offgrid_signed_hhl_born_and_solution`: success mass and normalized pseudoinverse
  direction.
* `uniform_offgrid_hhl_actual_unitary_access_noise`: stability under unitary oracle
  perturbations.
* `uniform_hhl_computed_finite_precision_parameters`: explicit accuracy, grid, and resource
  parameters.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The output of the counted uniform HHL word on a basis input with phase, scratch, and success
registers initialized to zero. -/
noncomputable def uniformHHLRun {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (O : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Bool × Fin D))) :=
  evaluate (countedHHLOracleLift O) (uniformHHLWord M d B) *ᵥ
    TensorState (Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j)))

/-- For a unitary oracle, the counted HHL run equals the embedded execution of forward phase
estimation, the flag gate, and inverse phase estimation. -/
theorem uniformHHLRun_eq {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (d : ℝ) (B : Operator D) (j : Fin D) :
    uniformHHLRun M hM U d B j = phaseFlagEmbed M
      (Run 1 (gridHHLQPEBlock (D := D) (M := M) U
        ++ [Step.gate (uniformHHLFlag (D := D) (M := M) d)]
        ++ gridHHLQPEBlockInv (D := D) (M := M) U)
        (TensorState (Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Ket false) (ApplyGate B (Ket j))))) := by
  have hMpos : 0 < M := by omega
  have hEval : evaluate (countedHHLOracleLift (D := D) (M := M) U) (uniformHHLWord M d B)
      = (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ *
        (countedHHLLiftGate (uniformHHLFlag (D := D) (M := M) d) *
          (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)
            * countedHHLLiftGate (countedHHLPrepMain (D := D) (M := M) B))) := by
    rw [uniformHHLWord, evaluate_append, evaluate_append, evaluate_append,
      evaluate_adjointCircuit]
    simp only [evaluate, instructionMatrix, mul_one]
    noncomm_ring
  unfold uniformHHLRun
  rw [countedHHLBranchInput_eq D M hMpos j]
  change ApplyGate _ _ = _
  rw [hEval, ← applyGate_comp, ← applyGate_comp, ← applyGate_comp]
  rw [countedHHLLiftGate_apply (countedHHLPrepMain (D := D) (M := M) B),
    countedHHLPrepMain_apply hMpos B j, countedQPEWord_apply D M hMpos U _,
    countedHHLLiftGate_apply (uniformHHLFlag (D := D) (M := M) d),
    countedQPEWord_apply_adjoint D M hMpos U hU _]
  rw [run_append, run_append, run_gate, run_nil]

/-- The uniform HHL output has Euclidean norm one for positive `d` and unitary oracle and
preparation matrices. -/
theorem uniformHHLRun_norm {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U B : Operator D) (j : Fin D) (d : ℝ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) :
    ‖toEuclidean_fromVec (uniformHHLRun M hM U d B j)‖ = 1 := by
  have hlegal := (uniform_hhl_actual_legal_forward_inverse_ledger D M d B hM hd hB).1
  have hunit := WellFormedAdjointCircuit.evaluate_unitary hlegal
    (countedHHLOracleLift_unitary hU)
  unfold uniformHHLRun
  rw [show evaluate _ _ *ᵥ _ = ApplyGate (evaluate _ _) _ from rfl,
    norm_applyGate_of_mem_unitaryGroup hunit]
  exact norm_countedHHLBranchInput D M (by omega) j

/-- Replacing unitary oracle `U` by unitary `W` changes the output by at most `2*(M-1)*‖W-U‖`
for positive `d` and unitary input preparation. -/
theorem uniformHHLRun_oracle_noise {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U W B : Operator D) (j : Fin D) (d : ℝ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) :
    ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j - uniformHHLRun M hM U d B j)‖
      ≤ 2 * (M - 1 : ℕ) * ‖W - U‖ := by
  have hledger := uniform_hhl_actual_legal_forward_inverse_ledger D M d B hM hd hB
  have h := norm_evaluate_sub_evaluate_le
    (countedHHLOracleLift (D := D) (M := M) W)
    (countedHHLOracleLift (D := D) (M := M) U)
    (countedHHLOracleLift_unitary hW) (countedHHLOracleLift_unitary hU)
    (uniformHHLWord M d B) hledger.1
    (TensorState (Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j))))
  rw [hledger.2.1, norm_countedHHLBranchInput D M (by omega) j,
    mul_one] at h
  have hdist := norm_oracleLift_sub D M (by omega) W U
  exact h.trans (by
    push_cast
    exact mul_le_mul_of_nonneg_left hdist (by positivity))

/-- Forward phase estimation on a clean phase register gives `qpeOutput`, with the supplied
Boolean flag state carried through the workspace. -/
theorem uniformHHLForwardReadout {D M : ℕ} (hM : 0 < M)
    (U : Operator D) (b : QState (Fin D)) (g : QState Bool) :
    Run 1 (gridHHLQPEBlock (M := M) U)
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState g b)) =
      gridHHLWorkspaceState (qpeOutput M U b) g := by
  have hin : TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState g b) =
      gridHHLWorkspaceState (TensorState (Ket (⟨0, hM⟩ : Fin M)) b) g := by
    funext p
    obtain ⟨a, f, i⟩ := p
    simp only [gridHHLWorkspaceState_apply, TensorState]
    ring
  simp only [gridHHLQPEBlock, Run]
  rw [hin, gridHHLFourier_apply, gridHHLPhaseOnly_qft_uniform hM,
    gridHHLPowers_apply, gridHHLFourier_apply]
  congr 1
  rw [qpeOutput, gridHHLPhaseOnly_eq_tensorGate]
  rfl

/-- The columns of a unitary spectral basis are eigenvectors of the continuous HHL oracle with
their specified exponential eigenvalues. -/
theorem continuousHHLOracle_mulVec_column {D : ℕ} (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) :
    continuousHHLOracle eig V *ᵥ (V *ᵥ Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • (V *ᵥ Ket i) := by
  have hUV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hV
  have hc : Vᴴ *ᵥ (V *ᵥ Ket i) = Ket i := by
    rw [Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
  unfold continuousHHLOracle
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  have hd : diagonal (fun k => Complex.exp (2 * Real.pi * Complex.I * (eig k : ℂ)))
      *ᵥ Ket i = Complex.exp (2 * Real.pi * Complex.I * eig i) • Ket i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    by_cases hk : k = i
    · subst k; simp [Ket]
    · simp [Ket, hk]
  rw [hd, Matrix.mulVec_smul]

/-- The phase-estimation output expands in the unitary eigenbasis with spectral input
coefficients and the corresponding phase kernels. -/
theorem uniformHHL_spectral_readout {D M : ℕ} (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (b : QState (Fin D)) :
    qpeOutput M (continuousHHLOracle eig V) b =
      ∑ i, (Vᴴ *ᵥ b) i • TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i) := by
  conv_lhs => rw [gridHHL_eigen_expansion (M := M) V hV b]
  rw [qpeOutput_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [qpeOutput_eigen M _ _ _ (continuousHHLOracle_mulVec_column eig V hV i)]

/-- The phase-flag embedding preserves Euclidean norm. -/
theorem uniformHHL_scratch_embed_norm {D M : ℕ}
    (v : QState (Fin M × (Bool × Fin D))) :
    ‖toEuclidean_fromVec (phaseFlagEmbed M v)‖ = ‖toEuclidean_fromVec v‖ := by
  rw [phaseFlagEmbed_eq_sector, norm_toEuclidean_relabelState,
    tensorState_l2_norm, norm_toEuclidean_fromVec_ket, one_mul]

/-- On a tensor-product input, the flag gate applies the decoded-label rotation to the Boolean
flag and leaves the data factor unchanged. -/
theorem uniformHHLFlag_product {D M : ℕ} (d : ℝ)
    (a : QState (Fin M)) (g : QState Bool) (v : QState (Fin D)) :
    ApplyGate (uniformHHLFlag (D := D) (M := M) d)
      (TensorState a (TensorState g v)) =
      fun p => a p.1 * (uniformHHLRotation d (uniformHHLDecode M p.1) *ᵥ g) p.2.1 * v p.2.2 := by
  have hin : TensorState a (TensorState g v) =
      relabelState (gridHHLFlagData (D := D) (M := M))
        (TensorState (TensorState a g) v) := by
    funext p
    simp [relabelState, gridHHLFlagData_symm_apply, TensorState, mul_assoc]
  rw [hin, uniformHHLFlag, applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  funext p
  obtain ⟨y, f, i⟩ := p
  change (ApplyGate (BlockDiag (fun y : Fin M =>
    uniformHHLRotation d (uniformHHLDecode M y))) (TensorState a g)) (y, f) * v i = _
  congr 1
  change (∑ q : Fin M × Bool, _ * _) = _
  simp only [Fintype.sum_prod_type, Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply,
      TensorState]
  rw [Finset.sum_eq_single y]
  · simp only [ite_true]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f' _
    ring
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

/-- A unitary spectral change of basis preserves the sum of squared amplitudes in every phase
and flag sector. -/
theorem uniformHHL_spectral_workspace_norm_sq {D M : ℕ}
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (a : Fin M → Bool → QState (Fin D)) :
    ‖toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
      (V *ᵥ a p.1 p.2.1) p.2.2)‖ ^ 2 =
      ∑ y, ∑ f, ∑ i, ‖a y f i‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro f _
  simpa only [Complex.normSq_eq_norm_sq] using!
    sum_normSq_mulVec_of_mem_unitaryGroup hV (a y f)

/-- For normalized spectral coefficients and the stated gap and grid budget, the workspace error
from decoded flag rotations is at most `η`. -/
theorem uniformHHL_spectral_error_bound {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (β : QState (Fin D)) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4)
    (hbudget : 4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ))
    (hβ : ∑ i, ‖β i‖ ^ 2 = 1) :
    ‖toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
      (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 *
        ((uniformHHLRotation d (uniformHHLDecode M p.1) *ᵥ Ket false) p.2.1 -
          (uniformHHLRotation d (eig i) *ᵥ Ket false) p.2.1))) p.2.2)‖ ≤ η := by
  let δ := fun (y : Fin M) (i : Fin D) =>
    uniformHHLRotation d (uniformHHLDecode M y) *ᵥ Ket false -
      uniformHHLRotation d (eig i) *ᵥ Ket false
  have hs : (∑ y : Fin M, ∑ f : Bool, ∑ i : Fin D,
      ‖β i * qpeKernel M (eig i) y * δ y i f‖ ^ 2) =
      ∑ i : Fin D, ‖β i‖ ^ 2 * (∑ y : Fin M, ‖qpeKernel M (eig i) y‖ ^ 2 *
        ‖toEuclidean_fromVec (δ y i)‖ ^ 2) := by
    simp only [norm_mul, mul_pow]
    calc
      _ = ∑ y : Fin M, ∑ i : Fin D, ∑ f : Bool,
          ‖β i‖ ^ 2 * ‖qpeKernel M (eig i) y‖ ^ 2 * ‖δ y i f‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro y _
        exact Finset.sum_comm
      _ = ∑ i : Fin D, ∑ y : Fin M, ∑ f : Bool,
          ‖β i‖ ^ 2 * ‖qpeKernel M (eig i) y‖ ^ 2 * ‖δ y i f‖ ^ 2 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [norm_toEuclidean_fromVec_sq]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        ring
  have hsq : ‖toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
      (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 * δ p.1 i p.2.1)) p.2.2)‖ ^ 2 ≤ η ^ 2 := by
    rw [uniformHHL_spectral_workspace_norm_sq V hV
      (fun y f i => β i * qpeKernel M (eig i) y * δ y i f), hs]
    calc (∑ i, ‖β i‖ ^ 2 * (∑ y, ‖qpeKernel M (eig i) y‖ ^ 2 *
        ‖toEuclidean_fromVec (δ y i)‖ ^ 2))
        ≤ ∑ i, ‖β i‖ ^ 2 * η ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (uniformHHL_spectral_window_error M (eig i) d η hM hd hη hη1
              (heig i).1 (heig i).2 hbudget) (sq_nonneg _)
      _ = η ^ 2 := by rw [← Finset.sum_mul, hβ, one_mul]
  change ‖toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
    (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 * δ p.1 i p.2.1)) p.2.2)‖ ≤ η
  nlinarith [norm_nonneg (toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
    (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 * δ p.1 i p.2.1)) p.2.2))]

/-- Embed a data state with phase zero, scratch flag false, and success flag true. -/
noncomputable def uniformHHLSuccessEmbed {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (v : QState (Fin D)) : QState (Fin M × (Bool × (Bool × Fin D))) :=
  TensorState (Ket (⟨0, by omega⟩ : Fin M))
    (TensorState (Ket false) (TensorState (Ket true) v))

/-- The ideal signed reciprocal-filter state with clean phase and scratch registers, using exact
spectral flag amplitudes. -/
noncomputable def uniformHHLIdeal {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Bool × Fin D))) :=
  TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Ket false)
    (fun p : Bool × Fin D =>
      ((V * diagonal (fun i => if p.1 then (uniformHHLGamma d (eig i) : ℂ)
        else (Real.sqrt (1 - uniformHHLGamma d (eig i) ^ 2) : ℂ)) * Vᴴ) *ᵥ
        (B *ᵥ Ket j)) p.2))

/-- The ideal output equals a spectral sum of exact-eigenphase flag rotations with the phase
register reset. -/
theorem uniformHHLIdeal_spectral {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (d : ℝ) (j : Fin D) :
    uniformHHLIdeal M hM eig V d B j = phaseFlagEmbed M
      (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        TensorState (Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (uniformHHLRotation d (eig i) *ᵥ Ket false) (V *ᵥ Ket i))) := by
  funext p
  obtain ⟨y, scratch, flag, k⟩ := p
  cases scratch
  · simp only [uniformHHLIdeal, phaseFlagEmbed, TensorState, Ket,
      Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_mulVec_apply]
    simp only [Matrix.mulVec_diagonal]
    cases flag <;>
      simp [uniformHHLRotation, Matrix.mulVec, dotProduct, Ket,
        Finset.mul_sum, Finset.sum_mul] <;>
      split_ifs <;> try rfl
    all_goals
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      ring
  · simp [uniformHHLIdeal, phaseFlagEmbed, TensorState, Ket]

/-- Forward phase estimation acts termwise on a spectral sum with eigenvalue-dependent Boolean
flag states. -/
theorem uniformHHL_forward_spectral_flags {D M : ℕ} (hM : 0 < M)
    (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (β : QState (Fin D)) (g : Fin D → QState Bool) :
    Run 1 (gridHHLQPEBlock (M := M) (continuousHHLOracle eig V))
      (∑ i, β i • TensorState (Ket (⟨0, hM⟩ : Fin M))
        (TensorState (g i) (V *ᵥ Ket i))) =
      ∑ i, β i • gridHHLWorkspaceState
        (TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i)) (g i) := by
  rw [run_qpeBlock_eq, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← run_qpeBlock_eq, uniformHHLForwardReadout hM,
    qpeOutput_eigen M _ _ _ (continuousHHLOracle_mulVec_column eig V hV i)]

/-- The success embedding of the normalized pseudoinverse applied to the prepared input. -/
noncomputable def uniformHHLSolutionTarget {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Bool × Fin D))) :=
  let v := matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j)
  uniformHHLSuccessEmbed M hM ((‖toEuclidean_fromVec v‖ : ℂ)⁻¹ • v)

/-- The accuracy parameter `min (d/2) (2^(-k))`. -/
noncomputable def uniformHHLAccuracy (d : ℝ) (k : ℕ) : ℝ :=
  min (d / 2) ((1 / 2 : ℝ) ^ k)

/-- The grid size obtained by rounding the required budget `4096/(d^2*η^4)` upward and taking
its maximum with two. -/
noncomputable def uniformHHLGrid (d : ℝ) (k : ℕ) : ℕ :=
  max 2 ⌈4096 / (d ^ 2 * uniformHHLAccuracy d k ^ 4)⌉₊

/-- The computed uniform HHL grid has at least two labels. -/
theorem uniformHHLGrid_ge_two (d : ℝ) (k : ℕ) : 2 ≤ uniformHHLGrid d k :=
  le_max_left _ _

/-- The computed grid meets the budget `4096/(d^2*η^4)`, where `η = uniformHHLAccuracy d k`. -/
theorem uniformHHLGrid_budget (d : ℝ) (k : ℕ) :
    4096 / (d ^ 2 * uniformHHLAccuracy d k ^ 4) ≤ (uniformHHLGrid d k : ℝ) := by
  have hn : ⌈4096 / (d ^ 2 * uniformHHLAccuracy d k ^ 4)⌉₊ ≤ uniformHHLGrid d k :=
    le_max_right _ _
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

/-- The uniform HHL success embedding preserves Euclidean norm. -/
theorem uniformHHLSuccessEmbed_norm {D M : ℕ} (hM : 2 ≤ M)
    (v : QState (Fin D)) :
    ‖toEuclidean_fromVec (uniformHHLSuccessEmbed M hM v)‖ = ‖toEuclidean_fromVec v‖ := by
  unfold uniformHHLSuccessEmbed
  rw [tensorState_l2_norm, tensorState_l2_norm, tensorState_l2_norm,
    norm_toEuclidean_fromVec_ket, norm_toEuclidean_fromVec_ket,
    norm_toEuclidean_fromVec_ket]
  simp

/-- Collapsing the ideal output to the success event gives the embedded pseudoinverse solution
scaled by `d/4` when eigenphases have magnitude at least `d`. -/
theorem uniformHHLIdeal_collapse {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, d ≤ |eig i|) :
    Collapse (uniformHHLIdeal M hM eig V d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)) =
      uniformHHLSuccessEmbed M hM ((d / 4 : ℂ) •
        (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j))) := by
  have hne : ∀ i, (eig i : ℂ) ≠ 0 := by
    intro i
    apply Complex.ofReal_ne_zero.mpr
    intro h
    have hi := heig i
    rw [h, abs_zero] at hi
    linarith
  have hpinv := pseudoinverse_conj_diagonal (fun i => (eig i : ℂ)) hne V hV
  have hgamma : ∀ i, (uniformHHLGamma d (eig i) : ℂ) = (d / 4 : ℂ) * (eig i : ℂ)⁻¹ := by
    intro i
    rw [uniformHHLGamma_eq_reciprocal d (eig i) hd (by linarith [heig i])]
    push_cast
    ring
  have hg : V * diagonal (fun i => (uniformHHLGamma d (eig i) : ℂ)) * Vᴴ =
      (d / 4 : ℂ) • matrixPseudoinverse (continuousHHLMatrix eig V) := by
    rw [continuousHHLMatrix, hpinv]
    simp_rw [hgamma]
    change V * diagonal ((d / 4 : ℂ) • (fun i => (eig i : ℂ)⁻¹)) * Vᴴ = _
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  funext p
  obtain ⟨y, scratch, flag, k⟩ := p
  cases flag
  · simp [collapse_apply, uniformHHLSuccessEmbed, TensorState, Ket]
  · simp only [collapse_apply, Finset.mem_filter, Finset.mem_univ, and_true,
      ite_true, uniformHHLIdeal, uniformHHLSuccessEmbed, TensorState,
      Pi.smul_apply, smul_eq_mul]
    rw [hg, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Ket, ite_true]
    ring

/-- For a normalized prepared input and eigenphase magnitudes in `[d, 1/4]`, the ideal success
branch has Euclidean norm at least `d`. -/
theorem uniformHHLIdeal_success_norm_lower {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) :
    d ≤ ‖toEuclidean_fromVec (Collapse (uniformHHLIdeal M hM eig V d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)))‖ := by
  have hne : ∀ i, (eig i : ℂ) ≠ 0 := by
    intro i
    apply Complex.ofReal_ne_zero.mpr
    intro h
    have hi := (heig i).1
    rw [h, abs_zero] at hi
    linarith
  have hinv : continuousHHLMatrix eig V * matrixPseudoinverse (continuousHHLMatrix eig V) = 1 := by
    rw [continuousHHLMatrix, pseudoinverse_conj_diagonal _ hne V hV]
    exact (conj_diagonal_mul_inv _ hne V hV).1
  have hA : ‖continuousHHLMatrix eig V‖ ≤ 1 / 4 := by
    refine (norm_conj_diagonal_le V hV (fun i => (eig i : ℂ))).trans ?_
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).2
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! (heig i).2
  have hb : ‖toEuclidean_fromVec (B *ᵥ Ket j)‖ = 1 := by
    rw [show B *ᵥ Ket j = ApplyGate B (Ket j) from rfl,
      norm_applyGate_of_mem_unitaryGroup hB, norm_toEuclidean_fromVec_ket]
  have hkey : continuousHHLMatrix eig V *ᵥ
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j)) = B *ᵥ Ket j := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hn := l2_norm_mulVec_fromVec_le (continuousHHLMatrix eig V)
    (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j))
  rw [hkey, hb] at hn
  have hinvnorm : 4 ≤ ‖toEuclidean_fromVec
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j))‖ := by
    have hnn := norm_nonneg (toEuclidean_fromVec
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j)))
    nlinarith [mul_le_mul_of_nonneg_right hA hnn]
  rw [uniformHHLIdeal_collapse hM eig V B j d hV hd (fun i => (heig i).1),
    uniformHHLSuccessEmbed_norm]
  change d ≤ ‖(d / 4 : ℂ) • toEuclidean_fromVec
    (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j))‖
  have hc : (d / 4 : ℂ) = ((d / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_smul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < d / 4)]
  nlinarith

/-- Postselecting the ideal success event gives `uniformHHLSolutionTarget` under the stated
spectral-gap and positivity hypotheses. -/
theorem uniformHHLIdeal_postMeasure {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, d ≤ |eig i|) :
    PostMeasure (uniformHHLIdeal M hM eig V d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)) =
      uniformHHLSolutionTarget M hM eig V B j := by
  let v := matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j)
  have hlinear : uniformHHLSuccessEmbed M hM ((d / 4 : ℂ) • v) =
      (d / 4 : ℂ) • uniformHHLSuccessEmbed M hM v := by
    funext p
    simp only [uniformHHLSuccessEmbed, TensorState, Pi.smul_apply, smul_eq_mul]
    ring
  have he := toEuclidean_postMeasure_eq_normalize (uniformHHLIdeal M hM eig V d B j)
    (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true))
  rw [uniformHHLIdeal_collapse hM eig V B j d hV hd heig, hlinear] at he
  have hc : (d / 4 : ℂ) = ((d / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc] at he
  change toEuclidean_fromVec (PostMeasure _ _) =
    NormedSpace.normalize (((d / 4 : ℝ) : ℂ) • toEuclidean_fromVec (uniformHHLSuccessEmbed M hM v)) at he
  have hreal : (((d / 4 : ℝ) : ℂ) • toEuclidean_fromVec (uniformHHLSuccessEmbed M hM v)) =
      (d / 4 : ℝ) • toEuclidean_fromVec (uniformHHLSuccessEmbed M hM v) := by
    ext p
    change ((d / 4 : ℝ) : ℂ) * _ = (d / 4 : ℝ) • _
    rw [RCLike.real_smul_eq_coe_mul]
    rfl
  rw [hreal] at he
  rw [NormedSpace.normalize_smul_of_pos (by positivity : 0 < d / 4)] at he
  have htarget : toEuclidean_fromVec (uniformHHLSolutionTarget M hM eig V B j) =
      NormedSpace.normalize (toEuclidean_fromVec (uniformHHLSuccessEmbed M hM v)) := by
    rw [NormedSpace.normalize, uniformHHLSuccessEmbed_norm]
    ext p
    change uniformHHLSuccessEmbed M hM ((‖toEuclidean_fromVec v‖ : ℂ)⁻¹ • v) p =
      (‖toEuclidean_fromVec v‖)⁻¹ • uniformHHLSuccessEmbed M hM v p
    simp only [uniformHHLSuccessEmbed, TensorState, Pi.smul_apply, smul_eq_mul,
      RCLike.real_smul_eq_coe_mul]
    push_cast
    simp only [RCLike.ofReal_eq_complex_ofReal]
    ring
  have heq := he.trans htarget.symm
  exact (WithLp.equiv 2 _).symm.injective heq

/-- For eigenphase magnitudes in `[d, 1/4]` and grid size at least `4096/(d^2*η^4)`, the actual
full workspace output is within distance `η` of the ideal output. -/
theorem uniform_offgrid_signed_hhl_full_workspace_error :
    ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
      (j : Fin D) (d η : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < η → η ≤ 1 →
      (∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) →
      4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) →
      ‖toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j -
        uniformHHLIdeal M hM eig V d B j)‖ ≤ η := by
  intro D M hM eig V B j d η hV hB hd hη hη1 heig hbudget
  have hMp : 0 < M := by omega
  let U := continuousHHLOracle eig V
  let b := B *ᵥ Ket j
  let β := Vᴴ *ᵥ b
  let g := fun i => uniformHHLRotation d (eig i) *ᵥ Ket false
  let a := TensorState (Ket (⟨0, hMp⟩ : Fin M)) (TensorState (Ket false) b)
  let v := ∑ i, β i • TensorState (Ket (⟨0, hMp⟩ : Fin M))
    (TensorState (g i) (V *ᵥ Ket i))
  let F := gridHHLBlockOp (D := D) (M := M) U
  have hU := continuous_hhl_oracle_unitary eig V hV
  have hF := gridHHLBlockOp_unitary hMp U hU
  have hstar : Fᴴ * F = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hF
  have hideal : uniformHHLIdeal M hM eig V d B j = phaseFlagEmbed M v :=
    uniformHHLIdeal_spectral hM eig V B d j
  have ha : a = ∑ i, β i • TensorState (Ket (⟨0, hMp⟩ : Fin M))
      (TensorState (Ket false) (V *ᵥ Ket i)) := by
    have hb := gridHHL_eigen_expansion (M := M) V hV b
    funext p
    have hb' := congrFun hb p.2.2
    dsimp [a, β]
    simp only [TensorState, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul] at hb' ⊢
    rw [hb']
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hforward : F *ᵥ a = ∑ i, β i • gridHHLWorkspaceState
      (TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i)) (Ket false) := by
    rw [ha]
    simpa only [run_qpeBlock_eq] using!
      uniformHHL_forward_spectral_flags hMp eig V hV β (fun _ => Ket false)
  have hvforward : F *ᵥ v = ∑ i, β i • gridHHLWorkspaceState
      (TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i)) (g i) := by
    simpa only [run_qpeBlock_eq] using! uniformHHL_forward_spectral_flags hMp eig V hV β g
  have hrotate (i : Fin D) :
      uniformHHLFlag (D := D) (M := M) d *ᵥ
        (gridHHLWorkspaceState (TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i))
          (Ket false)) =
      fun p => qpeKernel M (eig i) p.1 *
        (uniformHHLRotation d (uniformHHLDecode M p.1) *ᵥ Ket false) p.2.1 *
          (V *ᵥ Ket i) p.2.2 := by
    have hp : gridHHLWorkspaceState (TensorState (qpeKernel M (eig i)) (V *ᵥ Ket i))
        (Ket false) = TensorState (qpeKernel M (eig i))
          (TensorState (Ket false) (V *ᵥ Ket i)) := by
      funext p
      obtain ⟨y, f, k⟩ := p
      simp only [gridHHLWorkspaceState_apply, TensorState]
      ring
    change ApplyGate _ _ = _
    rw [hp, uniformHHLFlag_product]
  have hdiff : uniformHHLFlag d *ᵥ (F *ᵥ a) - F *ᵥ v =
      fun p : Fin M × (Bool × Fin D) =>
        (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 *
          ((uniformHHLRotation d (uniformHHLDecode M p.1) *ᵥ Ket false) p.2.1 -
            g i p.2.1))) p.2.2 := by
    rw [hforward, hvforward, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    funext p
    obtain ⟨y, flag, k⟩ := p
    simp only [Pi.sub_apply, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [hrotate]
    simp only [gridHHLWorkspaceState_apply, TensorState]
    rw [← Finset.sum_sub_distrib, matrix_mulVec_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, Ket, gridHHL_selector_sum]
    ring
  have hβ : ∑ i, ‖β i‖ ^ 2 = 1 := by
    have hv := sum_normSq_mulVec_of_mem_unitaryGroup (mem_unitaryGroup_adjoint hV) b
    have hb := sum_normSq_mulVec_of_mem_unitaryGroup hB (Ket j)
    have hk : (∑ i : Fin D, Complex.normSq (Ket j i)) = 1 := by simp [Ket]
    simpa only [Complex.normSq_eq_norm_sq] using! hv.trans (hb.trans hk)
  have hnorm := uniformHHL_spectral_error_bound hM eig V β d η hV hd hη hη1 heig hbudget hβ
  rw [uniformHHLRun_eq M hM U hU d B j, hideal]
  have hembed : ∀ x z : QState (Fin M × (Bool × Fin D)),
      phaseFlagEmbed M x - phaseFlagEmbed M z = phaseFlagEmbed M (x - z) := by
    intro x z
    funext p
    simp [phaseFlagEmbed, Pi.sub_apply]
    split_ifs <;> simp
  rw [hembed, uniformHHL_scratch_embed_norm,
    run_append, run_append, run_gate, run_nil, run_qpeBlock_eq, run_qpeBlockInv_eq]
  change ‖toEuclidean_fromVec (Fᴴ *ᵥ (uniformHHLFlag d *ᵥ (F *ᵥ a)) - v)‖ ≤ η
  have hvback : Fᴴ *ᵥ (F *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  rw [← hvback, ← Matrix.mulVec_sub]
  rw [show Fᴴ *ᵥ _ = ApplyGate Fᴴ _ from rfl,
    norm_applyGate_of_mem_unitaryGroup (mem_unitaryGroup_adjoint hF), hdiff]
  exact hnorm

/-- Under the stated gap and grid hypotheses with `η ≤ d/2`, success probability is positive and
at least `d^2/4`, and the normalized output is within `2*η/d` of the pseudoinverse solution
target. -/
theorem uniform_offgrid_signed_hhl_born_and_solution :
    ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
      (j : Fin D) (d η : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < η → η ≤ d / 2 →
      (∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) →
      4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) →
      let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
      let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
      d ^ 2 / 4 ≤ MeasureProb out S ∧ 0 < MeasureProb out S ∧
        ‖toEuclidean_fromVec (PostMeasure out S - uniformHHLSolutionTarget M hM eig V B j)‖
          ≤ 2 * η / d := by
  intro D M hM eig V B j d η hV hB hd hη hηd heig hbudget
  (try dsimp only)
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  let ideal := uniformHHLIdeal M hM eig V d B j
  let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
  have hη1 : η ≤ 1 := by linarith [(heig j).1, (heig j).2]
  have herr : ‖toEuclidean_fromVec (out - ideal)‖ ≤ η :=
    uniform_offgrid_signed_hhl_full_workspace_error D M hM eig V B j d η
      hV hB hd hη hη1 heig hbudget
  have hlower : d ≤ ‖toEuclidean_fromVec (Collapse ideal S)‖ :=
    uniformHHLIdeal_success_norm_lower hM eig V B j d hV hB hd heig
  have hgap : η < Real.sqrt (MeasureProb ideal S) := by
    rw [← norm_toEuclidean_collapse_eq_sqrt_measureProb]
    linarith
  have hpost := postMeasure_error_of_gap ideal out S herr hgap
  have hselected := (norm_toEuclidean_collapse_sub_le ideal out S).trans herr
  have htri := norm_sub_norm_le (toEuclidean_fromVec (Collapse ideal S))
    (toEuclidean_fromVec (Collapse out S))
  have htri' : ‖toEuclidean_fromVec (Collapse ideal S)‖ -
      ‖toEuclidean_fromVec (Collapse out S)‖ ≤
      ‖toEuclidean_fromVec (Collapse out S - Collapse ideal S)‖ := by
    change _ ≤ ‖toEuclidean_fromVec (Collapse ideal S - Collapse out S)‖ at htri
    rwa [show toEuclidean_fromVec (Collapse ideal S - Collapse out S) =
      toEuclidean_fromVec (Collapse ideal S) - toEuclidean_fromVec (Collapse out S) from rfl,
      norm_sub_rev] at htri
  have hout : d / 2 ≤ ‖toEuclidean_fromVec (Collapse out S)‖ := by linarith
  have hsq : d ^ 2 / 4 ≤ ‖toEuclidean_fromVec (Collapse out S)‖ ^ 2 := by
    nlinarith [norm_nonneg (toEuclidean_fromVec (Collapse out S))]
  have hmass : ‖toEuclidean_fromVec (Collapse out S)‖ ^ 2 = MeasureProb out S := by
    rw [norm_toEuclidean_fromVec_sq, sum_normSq_collapse]
  refine ⟨hmass ▸ hsq, hpost.1, ?_⟩
  rw [← uniformHHLIdeal_postMeasure hM eig V B j d hV hd (fun i => (heig i).1)]
  exact hpost.2.trans (div_le_div_of_nonneg_left (by positivity) hd
    (by rwa [← norm_toEuclidean_collapse_eq_sqrt_measureProb]))

/-- Under the spectral and grid hypotheses, a unitary approximate oracle `W` gives total
workspace error at most `η + 2*(M-1)*‖W-continuousHHLOracle eig V‖`. -/
theorem uniform_offgrid_hhl_actual_unitary_access_noise :
    ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B W : Operator D)
      (j : Fin D) (d η : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → W ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 < d → 0 < η → η ≤ 1 → (∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) →
      4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) →
      ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j -
        uniformHHLIdeal M hM eig V d B j)‖ ≤
          η + 2 * (M - 1 : ℕ) * ‖W - continuousHHLOracle eig V‖ := by
  intro D M hM eig V B W j d η hV hB hW hd hη hη1 heig hbudget
  have hnoise := uniformHHLRun_oracle_noise M hM (continuousHHLOracle eig V) W B j d
    (continuous_hhl_oracle_unitary eig V hV) hW hB hd
  have happrox := uniform_offgrid_signed_hhl_full_workspace_error D M hM eig V B j d η
    hV hB hd hη hη1 heig hbudget
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (toEuclidean_fromVec (uniformHHLRun M hM W d B j))
    (toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j))
    (toEuclidean_fromVec (uniformHHLIdeal M hM eig V d B j))
  change ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j -
    uniformHHLIdeal M hM eig V d B j)‖ ≤
    ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j -
      uniformHHLRun M hM (continuousHHLOracle eig V) d B j)‖ +
    ‖toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j -
      uniformHHLIdeal M hM eig V d B j)‖ at ht
  exact ht.trans (by linarith)

/-- For positive `d`, the computed accuracy and grid meet the positivity and resolution
requirements, and the one-dimensional word has `2*(M-1)` queries and `4*(M-1)+6` gates. -/
theorem uniform_hhl_computed_finite_precision_parameters :
    ∀ (d : ℝ) (k : ℕ), 0 < d →
      let η := min (d / 2) ((1 / 2 : ℝ) ^ k)
      let M := uniformHHLGrid d k
      0 < η ∧ η ≤ d / 2 ∧ 2 ≤ M ∧
        4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) ∧
        adjointQueryCount (uniformHHLWord (D := 1) M d (1 : Operator 1)) = 2 * (M - 1) ∧
        adjointGateCount (uniformHHLWord (D := 1) M d (1 : Operator 1)) = 4 * (M - 1) + 6 := by
  intro d k hd
  (try dsimp only)
  have hM := uniformHHLGrid_ge_two d k
  have hledger := uniform_hhl_actual_legal_forward_inverse_ledger 1 (uniformHHLGrid d k)
    d 1 hM hd (Submonoid.one_mem _)
  exact ⟨lt_min (by linarith) (pow_pos (by norm_num) k), min_le_left _ _,
    hM, uniformHHLGrid_budget d k, hledger.2⟩

end Qatlib.Concepts.HhlAlgorithms.UniformHHL
