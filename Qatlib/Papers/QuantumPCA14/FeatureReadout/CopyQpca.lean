/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionDefs
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics
import Qatlib.Concepts.HspRecovery.SieveLaw.NormalizedBranchDistance
import Qatlib.Concepts.HspRecovery.SieveLaw.SharpSelectiveStability
import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleMeasurement
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus

/-!
# Copy based quantum PCA and spectral readout

This module develops spectral mixtures and finite copy phase estimation outputs, including
posterior states for individual labels, observable statistics from independent fresh
measurements, and sine envelope phase accuracy bounds. The definitions `spectralState`,
`posterior`, and `sineSchedule` connect these matrix and probability statements.

Threshold selection approximates normalized principal spectral parts under a spectral gap and
retained mass condition. The normalized Choi state construction also connects process phase
estimation to complete Kraus representations, and `frontier1` assembles the six resulting
specifications. See [LloydMohseniRebentrost2014].

## Main statements

* `offgrid_full_output`: The ideal copy phase estimation output has the stated spectral kernel
  expansion, while the actual output is a density operator within trace norm `8 * (M - 1) * π² /
  n` and has resource tuple `((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)`.
* `conditional_eigenvector_error`: If the ideal branch has sufficient mass and posterior weight
  outside `i` at most `δ`, the actual conditional state's trace norm error from eigenvector `i`
  is at most the global copy error divided by branch mass plus `2 * δ`.
* `threshold_principal_correctness`: For a gapped density spectrum with retained mass greater
  than `δ`, the sine schedule produces a positive selected branch whose normalized state is
  within `2 * δ` divided by retained mass of the normalized principal part, with the stated rank
  bound and resource tuple.
* `frontier1`: The six specifications `FullEq2`, `ConditionalEigenvectors`,
  `IndependentLearning`, `ImprovedPhase`, `PrincipalComponents`, and `ProcessLearning` all hold.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.HspRecovery.SieveLaw
open Qatlib.Concepts.CopyEvolution.SelfTomography

namespace Qatlib.Papers.QuantumPCA14.FeatureReadout

open Matrix Qatlib
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-- The matrix `V * diagonal w * Vᴴ` formed from real spectral weights. -/
def spectralState {D : ℕ} (V : Operator D) (w : Fin D → ℝ) : Operator D :=
  V * diagonal (fun i => (w i : ℂ)) * Vᴴ

/-- The conjugate transpose of a unitary matrix multiplied by that matrix equals the identity. -/
theorem unitary_adjoint_mul {D : ℕ} {V : Operator D}
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) : Vᴴ * V = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV

/-- Nonnegative spectral weights make `spectralState V w` positive semidefinite. -/
theorem spectralState_pos {D : ℕ} (V : Operator D) (w : Fin D → ℝ)
    (hw : ∀ i, 0 ≤ w i) : (spectralState V w).PosSemidef :=
  (Matrix.posSemidef_diagonal_iff.mpr (fun i => RCLike.ofReal_nonneg.mpr (hw i))).mul_mul_conjTranspose_same V

/-- For unitary `V`, the trace of `spectralState V w` equals the sum of the weights cast to `ℂ`. -/
theorem spectralState_trace {D : ℕ} (V : Operator D) (w : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    trace (spectralState V w) = ((∑ i, w i : ℝ) : ℂ) := by
  rw [spectralState, trace_mul_cycle, unitary_adjoint_mul hV, one_mul, trace_diagonal]
  simp

/-- For unitary `V` and nonnegative weights summing to one, `spectralState V w` is a density
operator. -/
theorem spectralState_density {D : ℕ} (V : Operator D) (w : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : IsDensityOperator (spectralState V w) := by
  exact ⟨spectralState_pos V w hw, by rw [spectralState_trace V w hV, hs]; simp⟩

/-- The spectral state is the sum of the column outer products of `V`, weighted by `w`. -/
theorem spectralState_sum {D : ℕ} (V : Operator D) (w : Fin D → ℝ) :
    spectralState V w = ∑ i, (w i : ℂ) • outerProduct (fun j => V j i) := by
  ext a b
  rw [spectralState, mul_apply]
  simp only [mul_diagonal, Matrix.sum_apply,
    Matrix.smul_apply, outerProduct_apply, conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.star_def]
  ring

/-- Conjugating a spectral state by the adjoint of its unitary basis gives the diagonal matrix
of its weights. -/
theorem spectralState_coordinates {D : ℕ} (V : Operator D) (w : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Vᴴ * spectralState V w * V = diagonal (fun i => (w i : ℂ)) := by
  simp only [spectralState, Matrix.mul_assoc, unitary_adjoint_mul hV, Matrix.mul_one]
  rw [← Matrix.mul_assoc, unitary_adjoint_mul hV, one_mul]

/-- The weight of eigenvector `i` in label branch `z`, equal to its eigenvalue times the squared
phase estimation kernel amplitude. -/
def branchWeight {D M : ℕ} (eig : Fin D → ℝ) (z : Fin M) (i : Fin D) : ℝ :=
  eig i * ‖qpeKernel M (-eig i / 2) z‖ ^ 2

/-- The sum of the eigenvector weights in label branch `z`. -/
def branchTotal {D M : ℕ} (eig : Fin D → ℝ) (z : Fin M) : ℝ :=
  ∑ i, branchWeight eig z i

/-- The off grid label branch is the spectral state with weights `branchWeight eig z`. -/
theorem offgridBranch_spectral {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (z : Fin M) : offgridBranch D M eig V z = spectralState V (branchWeight eig z) := by
  rw [spectralState_sum]
  ext a b
  simp only [offgridBranch, Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply,
    branchWeight, Complex.ofReal_mul, Complex.ofReal_pow, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (‖qpeKernel M (-eig i / 2) z‖ : ℂ) ^ 2 =
      qpeKernel M (-eig i / 2) z * starRingEnd ℂ (qpeKernel M (-eig i / 2) z) by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring]
  ring

/-- For a unitary spectral basis, the total branch weight equals the off grid branch mass. -/
theorem branchTotal_eq_mass {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (z : Fin M) :
    branchTotal eig z = offgridBranchMass D M eig V z := by
  rw [offgridBranchMass, offgridBranch_spectral, spectralState_trace V _ hV]
  rfl

/-- The finite distribution on eigenvector indices obtained by dividing nonnegative branch
weights by their positive total. -/
def posterior {D M : ℕ} (eig : Fin D → ℝ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hz : 0 < branchTotal eig z) : FinDist (Fin D) where
  prob i := branchWeight eig z i / branchTotal eig z
  nonneg i := div_nonneg (mul_nonneg (he i) (sq_nonneg _)) hz.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hz)

/-- Conditioning the off grid output on a label of positive mass gives the spectral state with
the corresponding posterior weights. -/
theorem conditional_posterior {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hz : 0 < branchTotal eig z) :
    offgridConditionalState D M eig V z (by rw [← branchTotal_eq_mass eig V hV]; exact hz) =
      spectralState V (posterior eig he z hz).prob := by
  rw [offgridConditionalState, ← branchTotal_eq_mass eig V hV, offgridBranch_spectral]
  have hd : diagonal (fun i => ((posterior eig he z hz).prob i : ℂ)) =
      (branchTotal eig z : ℂ)⁻¹ • diagonal (fun i => (branchWeight eig z i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [posterior, div_eq_mul_inv, mul_comm]
    · simp [Matrix.smul_apply, h]
  simp only [spectralState]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

/-- For nonnegative eigenvalues and a unitary basis, an off grid conditional state with positive
branch mass is a density operator. -/
theorem conditional_density {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hz : 0 < branchTotal eig z) :
    IsDensityOperator (offgridConditionalState D M eig V z
      (by rw [← branchTotal_eq_mass eig V hV]; exact hz)) := by
  rw [conditional_posterior eig V hV he z hz]
  exact spectralState_density V _ hV (posterior eig he z hz).nonneg
    (posterior eig he z hz).sum_one

/-- The diagonal coordinate of the off grid conditional state in its unitary spectral basis
equals the posterior probability of that eigenvector. -/
theorem conditional_coordinate {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hz : 0 < branchTotal eig z) (i : Fin D) :
    (Vᴴ * offgridConditionalState D M eig V z
      (by rw [← branchTotal_eq_mass eig V hV]; exact hz) * V) i i =
        ((posterior eig he z hz).prob i : ℂ) := by
  rw [conditional_posterior eig V hV he z hz, spectralState_coordinates V _ hV]
  simp

/-- If all branch weight outside index `i` is at most a fraction `δ` of the positive total, its
posterior probability is at least `1 - δ`. -/
theorem posterior_accuracy {D M : ℕ} (eig : Fin D → ℝ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hz : 0 < branchTotal eig z) (i : Fin D) (δ : ℝ)
    (hbad : branchTotal eig z - branchWeight eig z i ≤ δ * branchTotal eig z) :
    1 - δ ≤ (posterior eig he z hz).prob i := by
  change 1 - δ ≤ branchWeight eig z i / branchTotal eig z
  apply (le_div_iff₀ hz).mpr
  nlinarith

/-- The ideal copy phase estimation output has the stated spectral kernel expansion, while the
actual output is a density operator within trace norm `8 * (M - 1) * π² / n` and has
resource tuple `((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)`. See
[LloydMohseniRebentrost2014]. -/
theorem offgrid_full_output {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = spectralState V eig) :
    copyQPEIdealOutput D M ρ =
      ∑ i, (eig i : ℂ) • outerProduct (fun p : Fin M × (Bool × Fin D) =>
        if p.2.1 then 0 else qpeKernel M (-eig i / 2) p.1 * V p.2.2 i) ∧
    ((copyQPEOutput D M n ρ).PosSemidef ∧ trace (copyQPEOutput D M n ρ) = 1) ∧
    (copyQPEOutput D M n ρ - copyQPEIdealOutput D M ρ).traceNorm ≤
      8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ∧
    copyQPEResources D M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0) := by
  have h := copy_qpe_actual_program_state_error D M n hM hn ρ hρ
  exact ⟨selfTomography_spectral_output D M (by omega) ρ V eig hV hs,
    ⟨h.1, h.2.1⟩, h.2.2, copy_qpe_same_path_fresh_resource_counts D M n hM hn⟩

/-- The linear map interpreting a phase estimation circuit with exact controlled Hamiltonian
evolution in place of each query. -/
def idealMap (D M : ℕ) (ρ : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) →
      MatrixMap (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ
  | [] => LinearMap.id
  | Step.gate U :: C => (idealMap D M ρ C).comp (MatrixMap.conj U)
  | Step.query :: C => (idealMap D M ρ C).comp (MatrixMap.conj
      (TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))))

/-- Applying `idealMap` agrees with the ideal copy phase estimation program. -/
theorem idealMap_apply (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D)))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    idealMap D M ρ C X = copyQPEIdealProgram D M ρ C X := by
  induction C generalizing X with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [idealMap, LinearMap.comp_apply, copyQPEIdealProgram, ih]

/-- Conjugating a pure state outer product by `U` gives the outer product of the state after
applying `U`. -/
theorem outer_conj {I : Type} [Fintype I] [DecidableEq I]
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

/-- The ideal copy phase estimation program sends a pure state outer product to the outer
product of the corresponding circuit output. -/
theorem idealProgram_outer (D M : ℕ) (ρ : Operator D)
    (C : Circuit (Fin M × (Bool × Fin D))) (ψ : QState (Fin M × (Bool × Fin D))) :
    copyQPEIdealProgram D M ρ C (outerProduct ψ) = outerProduct
      (Run (TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [copyQPEIdealProgram, Run, outer_conj, ih]

/-- For positive clock size, the phase estimation input of a spectral state is the weighted sum
of eigenvector outer products with clock zero and flag false. -/
theorem input_spectral {D M : ℕ} (hM : 0 < M) (V : Operator D) (eig : Fin D → ℝ) :
    copyQPEInput D M (spectralState V eig) = ∑ i, (eig i : ℂ) • outerProduct
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (fun j => V j i))) := by
  rw [spectralState_sum, copyQPEInput, dif_pos hM]
  simp only [outerProduct_tensorState]
  ext ⟨a,b,i⟩ ⟨c,d,j⟩
  simp only [tensorGate_apply, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A spectral basis column is an eigenvector of Hamiltonian evolution at time `π`, with phase
`exp (2 * π * I * (-eig i / 2))`. -/
theorem eigenphase {D : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) (i : Fin D) :
    hamiltonianEvolution ρ Real.pi *ᵥ (fun j => V j i) =
      Complex.exp (2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ)) • (fun j => V j i) := by
  have huv : hamiltonianEvolution ρ Real.pi * V = V * diagonal
      (fun j => Complex.exp (-Complex.I * (Real.pi : ℂ) * (eig j : ℂ))) := by
    rw [copyQPE_evolution_spectral D ρ V eig hV hs, Matrix.mul_assoc,
      unitary_adjoint_mul hV, Matrix.mul_one]
  have hphase : -Complex.I * (Real.pi : ℂ) * (eig i : ℂ) =
      2 * Real.pi * Complex.I * ((-eig i / 2 : ℝ) : ℂ) := by push_cast; ring
  funext j
  have h := congrArg (fun A : Operator D => A j i) huv
  (try dsimp only at h)
  rw [Matrix.mul_diagonal] at h
  change (∑ k, hamiltonianEvolution ρ Real.pi j k * V k i) = _
  rw [← Matrix.mul_apply, h, hphase]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The ideal copy phase estimation output obtained using the sine envelope phase circuit. -/
def sineIdeal (D M : ℕ) (hM : 2 ≤ M) (ρ : Operator D) :=
  copyQPEIdealProgram D M ρ (sinEnvelopePhaseCircuit M hM) (copyQPEInput D M ρ)

/-- The finite copy phase estimation output obtained using the sine envelope phase circuit. -/
def sineActual (D M n : ℕ) (hM : 2 ≤ M) (ρ : Operator D) :=
  copyQPEProgram D M n ρ (sinEnvelopePhaseCircuit M hM) (copyQPEInput D M ρ)

/-- The ideal sine envelope output is a spectral mixture of eigenvectors paired with their sine
envelope phase kernels. -/
theorem sine_spectral_output {D M : ℕ} (hM : 2 ≤ M)
    (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) :
    sineIdeal D M hM ρ = ∑ i, (eig i : ℂ) • outerProduct
      (phaseFlagEmbed M (TensorState (sinEnvelopeKernel M (-eig i / 2)) (fun j => V j i))) := by
  unfold sineIdeal
  rw [← idealMap_apply, hs, input_spectral (by omega), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, idealMap_apply, idealProgram_outer, sin_envelope_forward_eigenstate]
  exact eigenphase _ V eig hV rfl i

/-- The sine envelope circuit has `M - 1` queries and `2 * (M - 1) + 2` gates, with copy
resource tuple `((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)`. -/
theorem sine_counts {D M : ℕ} (hM : 2 ≤ M) (n : ℕ) :
    copyQPEProgramResources n (sinEnvelopePhaseCircuit (I := Fin D) M hM) =
      ((M-1)*n, (M-1)*n, (M-1)*n, 0) ∧
    QueryCount (sinEnvelopePhaseCircuit (I := Fin D) M hM) = M-1 ∧
    GateCount (sinEnvelopePhaseCircuit (I := Fin D) M hM) = 2*(M-1)+2 := by
  have h := sin_envelope_forward_word_counts (I := Fin D) M hM
  simp only [sinEnvelopeForwardWord, adjointQueryCount_reverse,
    adjointQueryCount_map_stepToAdjoint, adjointGateCount_reverse,
    adjointGateCount_map_stepToAdjoint] at h
  exact ⟨by rw [copyQPEProgramResources_eq, h.1], h⟩

/-- For `M ≥ 2` and positive `n`, the actual sine envelope output is a density operator and
differs from the ideal output by trace norm at most `8 * (M - 1) * π² / n`. -/
theorem sine_actual_error {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (sineActual D M n hM ρ).PosSemidef ∧ trace (sineActual D M n hM ρ) = 1 ∧
    (sineActual D M n hM ρ - sineIdeal D M hM ρ).traceNorm ≤
      8 * (M-1 : ℕ) * Real.pi^2 / (n : ℝ) := by
  have hX := copyQPEInput_density D M (by omega) ρ hρ
  have hC := sin_envelope_phase_circuit_unitary (I := Fin D) M hM
  have hd := copyQPEProgram_positive_trace D M n ρ hρ _ hC _ hX.1
  have he := copyQPEProgram_input_and_access_error D M n hn ρ hρ _ hC _ _ hX.1 hX.1
  rw [(sine_counts (D := D) hM n).2.1, hX.2, sub_self, traceNorm_zero,
    Complex.one_re, mul_one, zero_add] at he
  exact ⟨hd.1, hd.2.trans hX.2, he.trans_eq (by ring)⟩

/-- For positive `ε`, the sine envelope phase kernel mass at circular distance at least `ε` is
bounded by `(4 * π² + 40 * π⁴ / 3) / (2 * π * M * ε)²`. -/
theorem sine_phase_tail (M : ℕ) (hM : 2 ≤ M) (φ ε : ℝ) (hε : 0 < ε) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      ε ≤ phaseDistance φ ((z.val : ℝ) / M)), ‖sinEnvelopeKernel M φ z‖^2) ≤
        (4*Real.pi^2+40*Real.pi^4/3) / (2*Real.pi*(M : ℝ)*ε)^2 := by
  let s := Finset.univ.filter (fun z : Fin M => ε ≤ phaseDistance φ ((z.val : ℝ)/M))
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hden : 0 < (2*Real.pi*(M : ℝ)*ε)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  calc
    _ = ∑ z ∈ s, ‖sinEnvelopeKernel M φ z‖^2 * (2*Real.pi*(M : ℝ)*ε)^2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ s, ‖sinEnvelopeKernel M φ z‖^2 *
        (2*Real.pi*(M : ℝ)*phaseDistance φ ((z.val : ℝ)/M))^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' : ε ≤ phaseDistance φ ((z.val : ℝ)/M) := (Finset.mem_filter.mp hz).2
      gcongr
    _ ≤ ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (2*Real.pi*(M : ℝ)*phaseDistance φ ((z.val : ℝ)/M))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => by positivity)
    _ ≤ _ := sin_envelope_kernel_second_moment M φ hM

/-- The linear map extracting the data block for clock label `z` and summing over both flag
values. -/
def dataBlock {D M : ℕ} (z : Fin M) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ →ₗ[ℂ] Operator D where
  toFun X i j := ∑ b : Bool, X (z,b,i) (z,b,j)
  map_add' X Y := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [mul_add]

/-- Extracting a clock label data block preserves positive semidefiniteness. -/
theorem dataBlock_pos {D M : ℕ} (z : Fin M)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) : (dataBlock z X).PosSemidef := by
  change (∑ b : Bool, X.submatrix (fun i => (z,b,i)) (fun i => (z,b,i))).PosSemidef
  exact Matrix.posSemidef_sum _ (fun b _ => hX.submatrix _)

/-- The real trace of a clock label data block equals its copy phase estimation label mass. -/
theorem dataBlock_mass {D M : ℕ} (z : Fin M)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    (trace (dataBlock z X)).re = copyQPELabelMass D M X z := by
  simp only [dataBlock, LinearMap.coe_mk, AddHom.coe_mk, trace, diag_apply,
    Complex.re_sum, copyQPELabelMass, Fintype.sum_prod_type, Matrix.submatrix_apply]
  rw [Finset.sum_comm]

/-- For a positive semidefinite input, the real trace of a clock label data block is at most the
real trace of the input. -/
theorem dataBlock_tni {D M : ℕ} (z : Fin M)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) : (trace (dataBlock z X)).re ≤ (trace X).re := by
  rw [dataBlock_mass]
  have h := Finset.single_le_sum (fun w _ => copyQPELabelMass_nonneg D M X hX w)
    (Finset.mem_univ z)
  simpa only [copyQPELabelMass_sum] using! h

/-- The label data block of the ideal phase estimation output equals the corresponding off grid
spectral branch. -/
theorem ideal_dataBlock {D M : ℕ} (hM : 0 < M) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) (z : Fin M) :
    dataBlock z (copyQPEIdealOutput D M ρ) = offgridBranch D M eig V z := by
  rw [selfTomography_spectral_output D M hM ρ V eig hV hs]
  ext i j
  simp only [dataBlock, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_bool,
    offgridBranch, Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply,
    if_true, Bool.false_eq_true, if_false, mul_zero, map_zero, smul_zero,
    Finset.sum_const_zero, zero_add]

/-- A positive semidefinite matrix with positive real trace becomes a density operator under
`normalizedPositiveBranch`. -/
theorem normalize_density {D : ℕ} (X : Operator D) (hX : X.PosSemidef)
    (hp : 0 < (trace X).re) : IsDensityOperator (normalizedPositiveBranch X) := by
  have hi := (RCLike.nonneg_iff.mp hX.trace_nonneg).2
  change (trace X).im = 0 at hi
  have ht : trace X = ((trace X).re : ℂ) := by apply Complex.ext <;> simp [hi]
  rw [normalizedPositiveBranch, if_pos hp]
  have hn : (0 : ℂ) ≤ ((trace X).re : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hp.le)
  refine ⟨hX.smul hn, ?_⟩
  rw [trace_smul, ht]
  simp [ne_of_gt hp]

/-- For positive inputs of equal trace within trace norm `η`, an ideal label block of mass
greater than `η / 2` gives a positive actual block whose normalized state is within `η`
divided by the ideal block mass. -/
theorem block_stability {D M : ℕ} (z : Fin M)
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (ht : trace X = trace Y)
    (η : ℝ) (hη : 0 ≤ η) (he : (X-Y).traceNorm ≤ η)
    (hp : η / 2 < (trace (dataBlock z Y)).re) :
    0 < (trace (dataBlock z X)).re ∧
    IsDensityOperator (normalizedPositiveBranch (dataBlock z X)) ∧
    (normalizedPositiveBranch (dataBlock z X) -
      normalizedPositiveBranch (dataBlock z Y)).traceNorm ≤ η / (trace (dataBlock z Y)).re := by
  have hb := positive_tni_trace_zero_budget (dataBlock z)
    (dataBlock_pos z) (dataBlock_tni z) (X-Y) (hX.isHermitian.sub hY.isHermitian)
    (by rw [trace_sub, Complex.sub_re, ht, sub_self])
  rw [map_sub, trace_sub, Complex.sub_re] at hb
  have hmass : |(trace (dataBlock z X)).re - (trace (dataBlock z Y)).re| ≤ η / 2 := by
    have htrace : |(trace (dataBlock z X - dataBlock z Y)).re| ≤
        (dataBlock z X - dataBlock z Y).traceNorm :=
      (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
    rw [trace_sub, Complex.sub_re] at htrace
    linarith
  have hx : 0 < (trace (dataBlock z X)).re := by have h := (abs_le.mp hmass).1; linarith
  have hy : 0 < (trace (dataBlock z Y)).re := by linarith
  have hd := normalized_positive_branch_distance (Fin D) (dataBlock z X) (dataBlock z Y)
    (dataBlock_pos z X hX) (dataBlock_pos z Y hY) hx hy
  refine ⟨hx, normalize_density _ (dataBlock_pos z X hX) hx, hd.trans ?_⟩
  exact (div_le_div_of_nonneg_right (hb.trans he) (by positivity)).trans
    (div_le_div_of_nonneg_left hη hy (le_max_right _ _))

/-- The linear map discarding clock and flag registers by summing all clock label data blocks. -/
def discardClock (D M : ℕ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ →ₗ[ℂ] Operator D :=
  ∑ z : Fin M, dataBlock z

/-- Discarding clock and flag registers preserves positive semidefiniteness. -/
theorem discardClock_pos {D M : ℕ}
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) : (discardClock D M X).PosSemidef := by
  simp only [discardClock, LinearMap.sum_apply]
  exact Matrix.posSemidef_sum _ (fun z _ => dataBlock_pos z X hX)

/-- Discarding clock and flag registers preserves the trace. -/
theorem discardClock_trace {D M : ℕ}
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    trace (discardClock D M X) = trace X := by
  simp only [discardClock, LinearMap.sum_apply, dataBlock,
    LinearMap.coe_mk, AddHom.coe_mk, trace, diag_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]

/-- Discarding clock and flag registers from the ideal copy phase estimation output recovers the
input spectral state. -/
theorem discardClock_ideal {D M : ℕ} (hM : 0 < M) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) :
    discardClock D M (copyQPEIdealOutput D M ρ) = ρ := by
  simp only [discardClock, LinearMap.sum_apply, ideal_dataBlock hM ρ V eig hV hs,
    offgridBranch_spectral, spectralState_sum]
  rw [Finset.sum_comm, hs, spectralState_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  have hw : (∑ z : Fin M, (branchWeight eig z i : ℂ)) = (eig i : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    simp only [branchWeight, ← Finset.mul_sum, uniform_qpeKernel_normalized M (-eig i/2) hM,
        mul_one]
  rw [hw]

/-- The data register state obtained by discarding clock and flag registers from the actual copy
phase estimation output. -/
def learnedData {D M n : ℕ} (ρ : Operator D) : Operator D :=
  discardClock D M (copyQPEOutput D M n ρ)

/-- For clock size at least two and density input, `learnedData` is a density operator. -/
theorem learnedData_density {D M n : ℕ} (hM : 2 ≤ M) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : IsDensityOperator (learnedData (M := M) (n := n) ρ) := by
  have h := copyQPEOutput_density D M n (by omega) ρ hρ
  exact ⟨discardClock_pos _ h.1, (discardClock_trace _).trans h.2⟩

/-- For `M ≥ 2` and positive `n`, the learned data state is within trace norm `8 * (M - 1) * π²
/ n` of the input density matrix. -/
theorem learnedData_error {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) :
    (learnedData (M := M) (n := n) ρ - ρ).traceNorm ≤
      8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) := by
  let X := copyQPEOutput D M n ρ
  let Y := copyQPEIdealOutput D M ρ
  have hx := copyQPEOutput_density D M n (by omega) ρ hρ
  have he : ∀ i, 0 ≤ eig i := by
    have hd := hρ.1.mul_mul_conjTranspose_same Vᴴ
    rw [conjTranspose_conjTranspose, hs, spectralState_coordinates V eig hV] at hd
    intro i
    exact (RCLike.nonneg_iff.mp ((Matrix.posSemidef_diagonal_iff.mp hd) i)).1
  have hy : Y.PosSemidef := by
    change (copyQPEIdealOutput D M ρ).PosSemidef
    rw [selfTomography_spectral_output D M (by omega) ρ V eig hV hs]
    exact Matrix.posSemidef_sum _ (fun i _ =>
      (outerProduct_posSemidef _).smul (RCLike.ofReal_nonneg.mpr (he i)))
  have ht : trace Y = 1 := by
    rw [← discardClock_trace Y, discardClock_ideal (by omega) ρ V eig hV hs]
    exact hρ.2
  have hb := positive_tni_trace_zero_budget (discardClock D M)
    (fun A hA => discardClock_pos A hA) (fun A _ => by rw [discardClock_trace])
    (X-Y) (hx.1.isHermitian.sub hy.isHermitian)
    (by rw [trace_sub, hx.2, ht]; simp)
  rw [map_sub, discardClock_ideal (by omega) ρ V eig hV hs] at hb
  exact (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb).trans
    (copy_qpe_actual_program_state_error D M n hM hn ρ hρ).2.2

/-- The projective POVM associated with the columns of a unitary matrix `V`. -/
def basisPOVM {D : ℕ} (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    POVM (Fin D) (Fin D) where
  mats i := ⟨ensembleProjector (fun _ : Unit => Vᴴ) ((),i),
    (ensembleProjector_posSemidef (fun _ : Unit => Vᴴ) ((),i)).isHermitian⟩
  nonneg i := by
    apply HermitianMat.zero_le_iff.mpr
    exact ensembleProjector_posSemidef (fun _ : Unit => Vᴴ) ((),i)
  normalized := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum]
    exact ensembleProjector_sum_axis (fun _ : Unit => Vᴴ)
      (fun _ => Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hV) ()

/-- The effect for outcome `i` of `basisPOVM V hV` is the outer product of column `i` of `V`. -/
theorem basisPOVM_effect {D : ℕ} (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (i : Fin D) : ((basisPOVM V hV).mats i).mat = outerProduct (fun j => V j i) := by
  change Vᴴᴴ * Projector {i} * Vᴴ = _
  rw [conjTranspose_conjTranspose]
  have h : Projector ({i} : Finset (Fin D)) = outerProduct (Ket i) := by
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i <;>
      simp [Projector, diagonal_apply, outerProduct_apply,
          Qatlib.Foundations.PureStateMath.Ket, ha, hb, eq_comm] <;> aesop
  rw [h, ← conjMap_apply, outer_conj]
  congr 1
  funext j
  simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- If an operator is resolved as a weighted sum of POVM effects, the corresponding measurement
expectation equals the real trace of that operator times the state. -/
theorem povm_expect_resolution {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (f : O → ℝ) (A : Operator D) (hres : A = ∑ o, (f o : ℂ) • (Λ.mats o).mat) :
    (povmLaw Λ ρ hρ).expect f = (trace (A*ρ)).re := by
  rw [hres]
  simp only [FinDist.expect, povmLaw_prob, Finset.sum_mul, Matrix.smul_mul,
    trace_sum, trace_smul, Complex.re_sum, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro o _
  ring

/-- The projective POVM in an orthonormal eigenbasis of a Hermitian observable. -/
def observablePOVM {D : ℕ} (A : Operator D) (hA : A.IsHermitian) : POVM (Fin D) (Fin D) :=
  basisPOVM (hA.eigenvectorUnitary : Operator D) hA.eigenvectorUnitary.property

/-- A Hermitian observable is the sum of its spectral POVM effects weighted by its eigenvalues. -/
theorem observable_resolution {D : ℕ} (A : Operator D) (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i : ℂ) • ((observablePOVM A hA).mats i).mat := by
  simp only [observablePOVM, basisPOVM_effect]
  rw [← spectralState_sum]
  exact hA.spectral_theorem

/-- Measuring the spectral POVM of a Hermitian observable has eigenvalue expectation equal to
the real trace of the observable times the density matrix. -/
theorem observable_mean {D : ℕ} (A ρ : Operator D) (hA : A.IsHermitian)
    (hρ : IsDensityOperator ρ) :
    (povmLaw (observablePOVM A hA) ρ hρ).expect hA.eigenvalues = (trace (A*ρ)).re :=
  povm_expect_resolution _ _ _ _ _ (observable_resolution A hA)

/-- For `m > 0` independent fresh POVM measurements, the sample mean is unbiased, its mean
squared deviation is the single measurement variance divided by `m`, and its deviation
probability satisfies the stated variance bound. See [LloydMohseniRebentrost2014]. -/
theorem fresh_mean_variance_tail {D m : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (σ : Operator D) (hσ : IsDensityOperator σ)
    (f : O → ℝ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    (freshPovmLaw (fun _ : Fin m => D) (fun _ => Λ) (fun _ => σ) (fun _ => hσ)).expect
        (FinDist.avg f) = (povmLaw Λ σ hσ).expect f ∧
    (freshPovmLaw (fun _ : Fin m => D) (fun _ => Λ) (fun _ => σ) (fun _ => hσ)).expect
        (fun ω => (FinDist.avg f ω - (povmLaw Λ σ hσ).expect f)^2) =
          (povmLaw Λ σ hσ).variance f / m ∧
    eventMass (freshPovmLaw (fun _ : Fin m => D) (fun _ => Λ) (fun _ => σ) (fun _ => hσ))
        (fun ω => ε < |FinDist.avg f ω - (povmLaw Λ σ hσ).expect f|) ≤
          (povmLaw Λ σ hσ).variance f / (m*ε^2) := by
  constructor
  · simpa only [FinDist.expect, freshPovmLaw_prob, FinDist.probOf] using!
      (povmLaw Λ σ hσ).expect_avg f hm
  constructor
  · simpa only [FinDist.expect, freshPovmLaw_prob, FinDist.probOf] using!
      (povmLaw Λ σ hσ).expect_avg_sub_sq f hm
  · simpa only [eventMass, FinDist.probEvent, freshPovmLaw_prob, FinDist.probOf] using!
      (povmLaw Λ σ hσ).chebyshev_avg f hm ε hε

/-- The finite distribution of clock labels in the actual copy phase estimation output of a
density matrix. -/
def actualLabelLaw {D M n : ℕ} (hM : 2 ≤ M) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : FinDist (Fin M) where
  prob := copyQPELabelMass D M (copyQPEOutput D M n ρ)
  nonneg z := copyQPELabelMass_nonneg D M _ (copyQPEOutput_density D M n (by omega) ρ hρ).1 z
  sum_one := by
    rw [copyQPELabelMass_sum, (copyQPEOutput_density D M n (by omega) ρ hρ).2]
    rfl

/-- Across positive numbers of independent runs, the frequency of label `z` has mean equal to
its actual label probability, mean squared error equal to the indicator variance divided by
the run count, and the stated deviation bound. -/
theorem label_frequency_statistics {D M n m : ℕ} (hM : 2 ≤ M) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (z : Fin M) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    let p := actualLabelLaw (n := n) hM ρ hρ
    let f : Fin M → ℝ := fun x => if x = z then 1 else 0
    let r := independent (fun _ : Fin m => p)
    r.expect (FinDist.avg f) = p.prob z ∧
    r.expect (fun ω => (FinDist.avg f ω-p.prob z)^2) = p.variance f / m ∧
    eventMass r (fun ω => ε < |FinDist.avg f ω-p.prob z|) ≤ p.variance f/(m*ε^2) := by
  (try dsimp only)
  let p := actualLabelLaw (n := n) hM ρ hρ
  let f : Fin M → ℝ := fun x => if x = z then 1 else 0
  have hmean : p.expect f = p.prob z := by simp [FinDist.expect, f]
  have he := p.expect_avg f hm
  have hv := p.expect_avg_sub_sq f hm
  have ht := p.chebyshev_avg f hm ε hε
  rw [hmean] at he hv ht
  exact ⟨he, hv, ht⟩

/-- The bias in a Hermitian observable's measurement mean between state `σ` and matrix `ρ` is at
most `‖A‖ * traceNorm (σ - ρ)`. -/
theorem observable_bias {D : ℕ} (A σ ρ : Operator D) (hA : A.IsHermitian)
    (hσ : IsDensityOperator σ) :
    |(povmLaw (observablePOVM A hA) σ hσ).expect hA.eigenvalues - (trace (A*ρ)).re| ≤
      ‖A‖ * (σ-ρ).traceNorm := by
  rw [observable_mean, ← Complex.sub_re, ← trace_sub, ← Matrix.mul_sub]
  exact ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans
    (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _)

/-- Measuring a Hermitian observable on the learned data state has bias from its input
expectation at most `‖A‖ * 8 * (M - 1) * π² / n`. -/
theorem learned_observable_bias {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V A : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (hA : A.IsHermitian) :
    |(povmLaw (observablePOVM A hA) (learnedData (M := M) (n := n) ρ)
        (learnedData_density hM ρ hρ)).expect hA.eigenvalues - (trace (A*ρ)).re| ≤
      ‖A‖ * (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ)) :=
  (observable_bias A _ ρ hA _).trans
    (mul_le_mul_of_nonneg_left (learnedData_error hM hn ρ V eig hρ hV hs) (norm_nonneg _))

/-- The tensor extension of `V` acting on the data register and as the identity on clock and
flag registers. -/
def eigenBasis {D : ℕ} (M : ℕ) (V : Operator D) :=
  TensorGate (1 : Operator M) (TensorGate (1 : Matrix Bool Bool ℂ) V)

/-- Extending a unitary data basis by identity operators on clock and flag registers gives a
unitary matrix. -/
theorem eigenBasis_unitary {D : ℕ} (M : ℕ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    eigenBasis M V ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary (Submonoid.one_mem _) hV)

/-- The diagonal indicator of a clock and eigenvector event restricted to the false flag sector. -/
def eventDiagonal {D M : ℕ} (E : Fin M → Fin D → Prop) [∀ z i, Decidable (E z i)] :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  diagonal (fun p => if p.2.1 then 0 else if E p.1 p.2.2 then 1 else 0)

/-- The event indicator effect obtained by conjugating `eventDiagonal E` by the extended data
basis. -/
def eventEffect {D M : ℕ} (V : Operator D)
    (E : Fin M → Fin D → Prop) [∀ z i, Decidable (E z i)] :=
  eigenBasis M V * eventDiagonal E * (eigenBasis M V)ᴴ

/-- For a unitary data basis, every event effect has norm at most one. -/
theorem eventEffect_norm {D M : ℕ} (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (E : Fin M → Fin D → Prop) [∀ z i, Decidable (E z i)] : ‖eventEffect V E‖ ≤ 1 := by
  have hw := l2_norm_unitary_le_one (eigenBasis_unitary M V hV)
  have hh : ‖(eigenBasis M V)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hw
  have hd : ‖eventDiagonal E‖ ≤ 1 := by
    rw [eventDiagonal, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro p
    split <;> (try split) <;> norm_num
  exact ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))).trans
      (by calc (‖eigenBasis M V‖ * ‖eventDiagonal E‖) * ‖(eigenBasis M V)ᴴ‖ ≤ (1*1)*1 := by gcongr
               _ = 1 := by norm_num)

/-- For an effect matrix of norm at most one, the difference of its real trace pairings with `X`
and `Y` is at most `traceNorm (X - Y)`. -/
theorem effect_error {I : Type} [Fintype I] [DecidableEq I]
    (P X Y : Matrix I I ℂ) (hP : ‖P‖ ≤ 1) :
    |(trace (P*X)).re - (trace (P*Y)).re| ≤ (X-Y).traceNorm := by
  rw [← Complex.sub_re, ← trace_sub, ← Matrix.mul_sub]
  exact (((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans
    (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _)).trans
      (by simpa using! mul_le_mul_of_nonneg_right hP (Matrix.traceNorm_nonneg (X-Y)))

/-- The joint state with data basis index `i`, false flag, and clock amplitudes `K i`. -/
def kernelBasis {D M : ℕ} (K : Fin D → Fin M → ℂ) (i : Fin D) :
    QState (Fin M × (Bool × Fin D)) :=
  fun p => if p.2.1 then 0 else K i p.1 * Qatlib.Foundations.PureStateMath.Ket i p.2.2

/-- Applying the extended data basis to `kernelBasis K i` replaces its data basis vector by
column `i` of `V`. -/
theorem eigenBasis_kernel {D M : ℕ} (V : Operator D) (K : Fin D → Fin M → ℂ) (i : Fin D) :
    ApplyGate (eigenBasis M V) (kernelBasis K i) =
      fun p => if p.2.1 then 0 else K i p.1 * V p.2.2 i := by
  funext ⟨z,b,k⟩
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    eigenBasis, tensorGate_apply, Matrix.one_apply, kernelBasis, Fintype.sum_bool]
  cases b <;> simp [Qatlib.Foundations.PureStateMath.Ket, ite_mul, apply_ite]
  ring

/-- Simultaneous conjugation of two matrices by a unitary matrix preserves the trace of their
product. -/
theorem trace_conj_pair {I : Type} [Fintype I] [DecidableEq I]
    (W A B : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ) :
    trace ((W*A*Wᴴ)*(W*B*Wᴴ)) = trace (A*B) := by
  have hh : Wᴴ*W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hW
  calc
    _ = trace (W*(A*B)*Wᴴ) := by
      congr 1
      calc _ = W*A*(Wᴴ*W)*B*Wᴴ := by noncomm_ring
           _ = _ := by rw [hh]; noncomm_ring
    _ = _ := by rw [trace_mul_cycle, hh, one_mul]

/-- The event effect mass of a kernel state in a unitary eigenbasis equals the sum of squared
kernel amplitudes over the event's labels. -/
theorem kernel_event_mass {D M : ℕ} (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (K : Fin D → Fin M → ℂ)
    (E : Fin M → Fin D → Prop) [∀ z i, Decidable (E z i)] (i : Fin D) :
    (trace (eventEffect V E * outerProduct (fun p : Fin M × (Bool × Fin D) =>
      if p.2.1 then 0 else K i p.1 * V p.2.2 i))).re =
        ∑ z ∈ Finset.univ.filter (fun z => E z i), ‖K i z‖^2 := by
  rw [eventEffect, ← eigenBasis_kernel V K i, ← outer_conj,
    conjMap_apply, trace_conj_pair _ _ _ (eigenBasis_unitary M V hV)]
  simp only [trace, diag_apply, eventDiagonal, Matrix.diagonal_mul, outerProduct_apply,
    kernelBasis, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, mul_zero, map_zero, Finset.sum_const_zero, zero_add, Complex.re_sum,
    Qatlib.Foundations.PureStateMath.Ket]
  simp [ite_mul, apply_ite, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Finset.sum_filter]

/-- The ideal sine envelope event mass equals the eigenvalue weighted sum of the corresponding
sine kernel label masses. -/
theorem sine_event_mass {D M : ℕ} (hM : 2 ≤ M) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (E : Fin M → Fin D → Prop) [∀ z i, Decidable (E z i)] :
    (trace (eventEffect V E * sineIdeal D M hM ρ)).re =
      ∑ i, eig i * ∑ z ∈ Finset.univ.filter (fun z => E z i),
        ‖sinEnvelopeKernel M (-eig i/2) z‖^2 := by
  rw [sine_spectral_output hM ρ V eig hV hs]
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, Complex.re_sum,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (trace (eventEffect V E * outerProduct
    (fun p : Fin M × (Bool × Fin D) => if p.2.1 then 0 else
      sinEnvelopeKernel M (-eig i/2) p.1 * V p.2.2 i))).re = _
  exact kernel_event_mass V hV (fun j => sinEnvelopeKernel M (-eig j/2)) E i

/-- If the phase resolution and finite copy error budgets are each at most `δ / 2`, the actual
sine envelope event mass at phase distance at least `ε` is at most `δ`. -/
theorem sine_high_confidence {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (he : ∀ i, 0 ≤ eig i) (ε δ : ℝ) (hε : 0 < ε)
    (hresolution : 4*Real.pi^2+40*Real.pi^4/3 ≤ (δ/2)*(2*Real.pi*(M : ℝ)*ε)^2)
    (haccess : 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ≤ δ/2) :
    (trace (eventEffect V (fun z i => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M)) *
      sineActual D M n hM ρ)).re ≤ δ := by
  have hsum : ∑ i, eig i = 1 := by
    have h := hρ.2
    rw [hs, spectralState_trace V eig hV] at h
    exact_mod_cast h
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hden : 0 < (2*Real.pi*(M : ℝ)*ε)^2 := by positivity
  have ht (i : Fin D) : (∑ z ∈ Finset.univ.filter
      (fun z : Fin M => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M)),
      ‖sinEnvelopeKernel M (-eig i/2) z‖^2) ≤ δ/2 :=
    (sine_phase_tail M hM (-eig i/2) ε hε).trans ((div_le_iff₀ hden).mpr hresolution)
  have hi : (trace (eventEffect V (fun z i => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M)) *
      sineIdeal D M hM ρ)).re ≤ δ/2 := by
    rw [sine_event_mass hM ρ V eig hV hs]
    calc _ ≤ ∑ i, eig i*(δ/2) := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ht i) (he i))
         _ = δ/2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hd := effect_error (eventEffect V (fun z i => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M)))
    (sineActual D M n hM ρ) (sineIdeal D M hM ρ) (eventEffect_norm V hV _)
  have ha := (sine_actual_error hM hn ρ hρ).2.2
  have hb := (abs_le.mp (hd.trans ha)).2
  linarith

/-- The spectral state retaining only the eigenvalue weights indexed by `S`. -/
def principalState {D : ℕ} (V : Operator D) (eig : Fin D → ℝ) (S : Finset (Fin D)) :=
  spectralState V (fun i => if i ∈ S then eig i else 0)

/-- Retaining a subset of nonnegative spectral weights gives a positive semidefinite principal
state. -/
theorem principal_pos {D : ℕ} (V : Operator D) (eig : Fin D → ℝ)
    (he : ∀ i, 0 ≤ eig i) (S : Finset (Fin D)) : (principalState V eig S).PosSemidef :=
  spectralState_pos V _ (fun i => by split <;> simp_all)

/-- In a unitary basis, the trace of a principal state equals the sum of the retained
eigenvalues. -/
theorem principal_trace {D : ℕ} (V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (S : Finset (Fin D)) :
    trace (principalState V eig S) = ((∑ i ∈ S, eig i : ℝ) : ℂ) := by
  rw [principalState, spectralState_trace V _ hV]
  simp

/-- The rank of a principal state is at most the number of retained indices. -/
theorem principal_rank {D : ℕ} (V : Operator D) (eig : Fin D → ℝ) (S : Finset (Fin D)) :
    (principalState V eig S).rank ≤ S.card := by
  let w : Fin D → ℝ := fun i => if i ∈ S then eig i else 0
  have hr : (principalState V eig S).rank ≤ (diagonal (fun i => (w i : ℂ))).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right V (diagonal (fun i => (w i : ℂ))))
  apply hr.trans
  rw [Matrix.rank_diagonal]
  let g : {i // (w i : ℂ) ≠ 0} → S :=
    fun i => ⟨i.1, by
      by_contra hi
      exact i.2 (by simp [w, hi])⟩
  have hg : Function.Injective g := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  simpa only [Fintype.card_coe] using! Fintype.card_le_of_injective g hg

/-- The spectral state construction sends pointwise subtraction of weights to subtraction of
matrices. -/
theorem spectralState_sub {D : ℕ} (V : Operator D) (w u : Fin D → ℝ) :
    spectralState V (fun i => w i-u i) = spectralState V w - spectralState V u := by
  simp only [spectralState, Complex.ofReal_sub]
  rw [show diagonal (fun i => (w i : ℂ)-(u i : ℂ)) =
    diagonal (fun i => (w i : ℂ)) - diagonal (fun i => (u i : ℂ)) from (Matrix.diagonal_sub _ _).symm]
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- For nonnegative weights in a unitary basis, the trace norm of the discarded spectral part
equals the sum of the discarded weights. -/
theorem principal_tail {D : ℕ} (V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (S : Finset (Fin D)) :
    (spectralState V eig - principalState V eig S).traceNorm = ∑ i ∈ Sᶜ, eig i := by
  have hid : spectralState V eig - principalState V eig S =
      spectralState V (fun i => if i ∈ Sᶜ then eig i else 0) := by
    rw [principalState, ← spectralState_sub]
    congr 1
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  rw [hid, posSemidef_traceNorm_eq_re
    (spectralState_pos V _ (fun i => by split <;> simp_all)), spectralState_trace V _ hV]
  simp only [Complex.ofReal_re, ← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- Normalizing a positive mass principal part of a density spectrum gives a density operator
within trace norm twice the discarded eigenvalue mass of the original state. -/
theorem principal_normalized {D : ℕ} (V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (hs : ∑ i, eig i = 1) (S : Finset (Fin D)) (hp : 0 < ∑ i ∈ S, eig i) :
    IsDensityOperator (normalizedPositiveBranch (principalState V eig S)) ∧
    (normalizedPositiveBranch (principalState V eig S) - spectralState V eig).traceNorm ≤
      2 * ∑ i ∈ Sᶜ, eig i := by
  have ht : ∑ i ∈ Sᶜ, eig i = 1 - ∑ i ∈ S, eig i := by
    have h := Finset.sum_add_sum_compl S eig
    rw [hs] at h
    linarith
  have hpc : (trace (principalState V eig S)).re = ∑ i ∈ S, eig i := by
    rw [principal_trace V eig hV]; rfl
  have hρ := spectralState_density V eig hV he hs
  have hn : normalizedPositiveBranch (spectralState V eig) = spectralState V eig := by
    simp [normalizedPositiveBranch, hρ.2]
  have hraw : (principalState V eig S - spectralState V eig).traceNorm = ∑ i ∈ Sᶜ, eig i := by
    rw [show principalState V eig S - spectralState V eig =
      -(spectralState V eig - principalState V eig S) by abel, traceNorm_neg, principal_tail V eig hV he]
  have hp1 : (∑ i ∈ S, eig i) ≤ 1 := by
    have h := Finset.sum_nonneg (fun i (_ : i ∈ Sᶜ) => he i)
    linarith
  have hd := normalized_positive_branch_distance (Fin D) (principalState V eig S) (spectralState V eig)
    (principal_pos V eig he S) hρ.1 (by rw [hpc]; exact hp) (by rw [hρ.2]; norm_num)
  rw [hn, hraw, hpc, hρ.2, Complex.one_re, max_eq_right hp1,
    abs_of_nonpos (sub_nonpos.mpr hp1), div_one] at hd
  exact ⟨normalize_density _ (principal_pos V eig he S) (by rw [hpc]; exact hp), by linarith⟩

/-- The Choi matrix of a trace preserving map on `D` dimensional input has trace `D`. -/
theorem process_trace {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (hT : TracePreserving T) :
    trace (ChoiMatrix T) = (D : ℂ) := by
  have hi (i : Fin D) : ∑ a : Fin E, T (matrixUnit i i) a a = 1 := by
    change trace (T (matrixUnit i i)) = 1
    rw [hT]
    simp [matrixUnit, Matrix.trace_single_eq_same]
  simp only [trace, diag_apply, Fintype.sum_prod_type, ChoiMatrix, hi]
  simp

/-- The Choi matrix relabeled to `Fin (D * E)` and scaled by the reciprocal input dimension. -/
def processState {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Operator (D*E) :=
  (D : ℂ)⁻¹ • relabelGate (finProdFinEquiv (m := D) (n := E)) (ChoiMatrix T)

/-- For positive input dimension, the normalized Choi matrix of a completely positive trace
preserving map is a density operator. -/
theorem process_density {D E : ℕ} (hD : 0 < D) (T : Operator D →ₗ[ℂ] Operator E)
    (hCP : CompletelyPositive T) (hTP : TracePreserving T) : IsDensityOperator (processState T) := by
  have hp := (choi_posSemidef_of_completelyPositive hCP).submatrix
    (finProdFinEquiv (m := D) (n := E)).symm
  have hn : (0 : ℂ) ≤ (D : ℂ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg D : (0 : ℝ) ≤ D))
  refine ⟨hp.smul hn, ?_⟩
  rw [processState, trace_smul]
  change (D : ℂ)⁻¹ * trace ((ChoiMatrix T).submatrix
    (finProdFinEquiv (m := D) (n := E)).symm (finProdFinEquiv (m := D) (n := E)).symm) = 1
  rw [Matrix.trace_submatrix, process_trace T hTP]
  exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hD))

/-- Applying the amplified map to the maximally entangled matrix scaled by `1 / D` gives the
Choi matrix scaled by `1 / D`. -/
theorem process_one_use {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    ChannelAmplification T D ((D : ℂ)⁻¹ • omegaMatrix D) =
      (D : ℂ)⁻¹ • ChoiMatrix T := by
  ext x y
  change T (fun i j => (D : ℂ)⁻¹ * omegaMatrix D (x.1,i) (y.1,j)) x.2 y.2 = _
  have h : (fun i j => (D : ℂ)⁻¹ * omegaMatrix D (x.1,i) (y.1,j)) =
      (D : ℂ)⁻¹ • matrixUnit x.1 y.1 := by
    ext i j
    simp [omegaMatrix, matrixUnit, Matrix.single, eq_comm]
  rw [h, map_smul]
  rfl

/-- The matrix `V` multiplied by the diagonal square roots of the scaled spectral weights `c *
eig i`. -/
def spectralFactor {D : ℕ} (c : ℝ) (V : Operator D) (eig : Fin D → ℝ) : Operator D :=
  V * diagonal (fun i => (Real.sqrt (c*eig i) : ℂ))

/-- For nonnegative `c` and eigenvalue weights, the spectral factor times its adjoint equals `c`
times the spectral state. -/
theorem spectralFactor_product {D : ℕ} (c : ℝ) (hc : 0 ≤ c) (V : Operator D)
    (eig : Fin D → ℝ) (he : ∀ i, 0 ≤ eig i) :
    spectralFactor c V eig * (spectralFactor c V eig)ᴴ = (c : ℂ) • spectralState V eig := by
  have hd : (diagonal (fun i => (Real.sqrt (c*eig i) : ℂ))).conjTranspose =
      diagonal (fun i => (Real.sqrt (c*eig i) : ℂ)) := by simp [diagonal_conjTranspose]
  have hs : diagonal (fun i => (Real.sqrt (c*eig i) : ℂ)) *
      diagonal (fun i => (Real.sqrt (c*eig i) : ℂ)) =
      (c : ℂ) • diagonal (fun i => (eig i : ℂ)) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (mul_nonneg hc (he i)), Complex.ofReal_mul]
    · simp [Matrix.smul_apply, h]
  simp only [spectralFactor, conjTranspose_mul, hd]
  calc
    _ = V * (diagonal (fun i => (Real.sqrt (c*eig i) : ℂ)) *
        diagonal (fun i => (Real.sqrt (c*eig i) : ℂ))) * Vᴴ := by noncomm_ring
    _ = _ := by rw [hs, Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- A nonnegative spectral decomposition of the process state of a trace preserving map with
positive input dimension yields a Kraus representation satisfying the completeness relation. -/
theorem process_spectral_kraus {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) (hTP : TracePreserving T)
    (V : Operator (D*E)) (eig : Fin (D*E) → ℝ) (he : ∀ i, 0 ≤ eig i)
    (hs : processState T = spectralState V eig) :
    let F := relabelGate (finProdFinEquiv (m := D) (n := E)).symm
      (spectralFactor D V eig)
    KrausForm T (krausOfFactor F) ∧ KrausComplete (krausOfFactor F) := by
  (try dsimp only)
  let e := finProdFinEquiv (m := D) (n := E)
  let A := spectralFactor (D : ℝ) V eig
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have heq : f (ChoiMatrix T) = (D : ℂ) • processState T := by
    change relabelGate e (ChoiMatrix T) = (D : ℂ) • ((D : ℂ)⁻¹ • relabelGate e (ChoiMatrix T))
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt hD)), one_smul]
  have hf : A*Aᴴ = f (ChoiMatrix T) := by
    rw [heq, hs]
    exact spectralFactor_product D (by positivity) V eig he
  have hc : ChoiMatrix T = relabelGate e.symm A * (relabelGate e.symm A)ᴴ := by
    apply f.injective
    have hstar (X : Operator (D*E)) : relabelGate e.symm Xᴴ = (relabelGate e.symm X)ᴴ := rfl
    rw [← hstar]
    change f (ChoiMatrix T) = f (f.symm A * f.symm Aᴴ)
    rw [← map_mul]
    change f (ChoiMatrix T) = f (f.symm (A*Aᴴ))
    rw [f.apply_symm_apply, hf]
  have hk := krausForm_of_choi_eq T hc
  exact ⟨hk, krausComplete_of_tracePreserving hk hTP⟩

/-- The constant `4 * π² + 40 * π⁴ / 3` in the sine envelope phase tail bound. -/
def sineMomentConstant : ℝ := 4*Real.pi^2+40*Real.pi^4/3

/-- The pair of clock size and copies per query chosen from phase tolerance `ε` and error budget
`δ` using ceiling bounds. -/
def sineSchedule (ε δ : ℝ) : ℕ × ℕ :=
  let M := max 2 (Nat.ceil (Real.sqrt (2*sineMomentConstant/δ)/(2*Real.pi*ε)))
  (M, max 1 (Nat.ceil ((16 : ℝ)*(M-1 : ℕ)*Real.pi^2/δ)))

/-- For positive `ε` and `δ`, `sineSchedule` chooses clock size at least two and positive copy
count, with phase resolution and finite copy errors each meeting their `δ / 2` budgets. -/
theorem sineSchedule_valid (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    let M := (sineSchedule ε δ).1
    let n := (sineSchedule ε δ).2
    2 ≤ M ∧ 0 < n ∧
    sineMomentConstant ≤ (δ/2)*(2*Real.pi*(M : ℝ)*ε)^2 ∧
    8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ≤ δ/2 := by
  dsimp only [sineSchedule]
  let M := max 2 (Nat.ceil (Real.sqrt (2*sineMomentConstant/δ)/(2*Real.pi*ε)))
  let n := max 1 (Nat.ceil ((16 : ℝ)*(M-1 : ℕ)*Real.pi^2/δ))
  have hM : 2 ≤ M := le_max_left _ _
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  have hC : 0 ≤ sineMomentConstant := by unfold sineMomentConstant; positivity
  have hm : Real.sqrt (2*sineMomentConstant/δ)/(2*Real.pi*ε) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2
      (Nat.ceil (Real.sqrt (2*sineMomentConstant/δ)/(2*Real.pi*ε)))))
  have hrad : 0 ≤ 2*sineMomentConstant/δ := by positivity
  have hroot : Real.sqrt (2*sineMomentConstant/δ) ≤ 2*Real.pi*(M : ℝ)*ε := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*Real.pi*ε)).mp hm
    nlinarith
  have hs : 2*sineMomentConstant/δ ≤ (2*Real.pi*(M : ℝ)*ε)^2 := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (2*sineMomentConstant/δ)]
  have hres := (div_le_iff₀ hδ).mp hs
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnceil : Nat.ceil ((16 : ℝ)*(M-1 : ℕ)*Real.pi^2/δ) ≤ n := le_max_right _ _
  have hceil : (16 : ℝ)*(M-1 : ℕ)*Real.pi^2/δ ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
  have hc := (div_le_iff₀ hδ).mp hceil
  refine ⟨hM, hn, by nlinarith, (div_le_iff₀ hnreal).mpr ?_⟩
  nlinarith

/-- Under the resolution and finite copy error budgets, the actual sine envelope event mass at
phase distance less than `ε` is at least `1 - δ`. See [LloydMohseniRebentrost2014]. -/
theorem sine_success_probability {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (he : ∀ i, 0 ≤ eig i) (ε δ : ℝ) (hε : 0 < ε)
    (hresolution : sineMomentConstant ≤ (δ/2)*(2*Real.pi*(M : ℝ)*ε)^2)
    (haccess : 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ≤ δ/2) :
    1-δ ≤ (trace (eventEffect V (fun z i => phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε) *
      sineActual D M n hM ρ)).re := by
  have hsum : ∑ i, eig i = 1 := by
    have h := hρ.2
    rw [hs, spectralState_trace V eig hV] at h
    exact_mod_cast h
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hden : 0 < (2*Real.pi*(M : ℝ)*ε)^2 := by positivity
  have hgood (i : Fin D) : 1-δ/2 ≤ ∑ z ∈ Finset.univ.filter
      (fun z : Fin M => phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε),
      ‖sinEnvelopeKernel M (-eig i/2) z‖^2 := by
    have hb := (sine_phase_tail M hM (-eig i/2) ε hε).trans
      ((div_le_iff₀ hden).mpr hresolution)
    have hp : (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M)), ‖sinEnvelopeKernel M (-eig i/2) z‖^2) +
      (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε), ‖sinEnvelopeKernel M (-eig i/2) z‖^2) = 1 := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      convert! sin_envelope_kernel_normalized M (-eig i/2) hM using 1
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M) <;> simp [h, not_lt.mpr] at *
    linarith
  have hi : 1-δ/2 ≤ (trace (eventEffect V
      (fun z i => phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε) * sineIdeal D M hM ρ)).re := by
    rw [sine_event_mass hM ρ V eig hV hs]
    calc _ = ∑ i, eig i*(1-δ/2) := by rw [← Finset.sum_mul, hsum, one_mul]
         _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hgood i) (he i))
  have hd := effect_error (eventEffect V (fun z i => phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε))
    (sineActual D M n hM ρ) (sineIdeal D M hM ρ) (eventEffect_norm V hV _)
  have ha := (sine_actual_error hM hn ρ hρ).2.2
  have hb := (abs_le.mp (hd.trans ha)).1
  linarith

/-- The real weights in a unitary spectral representation of a density operator are nonnegative. -/
theorem spectrum_nonneg {D : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hρ : IsDensityOperator ρ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = spectralState V eig) : ∀ i, 0 ≤ eig i := by
  have hd := hρ.1.mul_mul_conjTranspose_same Vᴴ
  rw [conjTranspose_conjTranspose, hs, spectralState_coordinates V eig hV] at hd
  intro i
  exact (RCLike.nonneg_iff.mp ((Matrix.posSemidef_diagonal_iff.mp hd) i)).1

/-- For a density operator with a unitary spectral representation and `M ≥ 2`, the standard
ideal copy phase estimation output is positive semidefinite with trace one. -/
theorem standard_ideal_density {D M : ℕ} (hM : 2 ≤ M) (ρ V : Operator D)
    (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) :
    (copyQPEIdealOutput D M ρ).PosSemidef ∧ trace (copyQPEIdealOutput D M ρ) = 1 := by
  constructor
  · rw [selfTomography_spectral_output D M (by omega) ρ V eig hV hs]
    exact Matrix.posSemidef_sum _ (fun i _ =>
      (outerProduct_posSemidef _).smul (RCLike.ofReal_nonneg.mpr (spectrum_nonneg ρ V eig hρ hV hs i)))
  · rw [← discardClock_trace, discardClock_ideal (by omega) ρ V eig hV hs]
    exact hρ.2

/-- If the ideal label mass exceeds half the global copy error bound, the actual label has
positive mass and its normalized data block is a density operator within the global bound
divided by the ideal mass of the normalized ideal branch. -/
theorem actual_conditional_state {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (z : Fin M) (hp : (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/2 < branchTotal eig z) :
    0 < copyQPELabelMass D M (copyQPEOutput D M n ρ) z ∧
    IsDensityOperator (normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ))) ∧
    (normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ)) -
      normalizedPositiveBranch (offgridBranch D M eig V z)).traceNorm ≤
        (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/branchTotal eig z := by
  have hx := copyQPEOutput_density D M n (by omega) ρ hρ
  have hy := standard_ideal_density hM ρ V eig hρ hV hs
  have hm : (trace (dataBlock z (copyQPEIdealOutput D M ρ))).re = branchTotal eig z := by
    rw [ideal_dataBlock (by omega) ρ V eig hV hs, offgridBranch_spectral,
      spectralState_trace V _ hV]
    rfl
  have hb := block_stability z (copyQPEOutput D M n ρ) (copyQPEIdealOutput D M ρ)
    hx.1 hy.1 (hx.2.trans hy.2.symm) _ (by positivity)
    (copy_qpe_actual_program_state_error D M n hM hn ρ hρ).2.2 (by rw [hm]; exact hp)
  rw [hm, dataBlock_mass, ideal_dataBlock (by omega) ρ V eig hV hs] at hb
  exact hb

/-- Normalizing an off grid branch of positive mass gives the spectral state whose weights are
its posterior probabilities. -/
theorem normalized_offgrid_posterior {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (z : Fin M) (hp : 0 < branchTotal eig z) :
    normalizedPositiveBranch (offgridBranch D M eig V z) = spectralState V (posterior eig he z hp).prob := by
  rw [← conditional_posterior eig V hV he z hp]
  have hm : (trace (offgridBranch D M eig V z)).re = branchTotal eig z := by
    rw [offgridBranch_spectral, spectralState_trace V _ hV]; rfl
  simp only [normalizedPositiveBranch, hm, if_pos hp, offgridConditionalState,
    ← branchTotal_eq_mass eig V hV]

/-- Two equal positive weights normalized in the identity basis give half the identity on
dimension two, which differs from the outer product of the zero basis vector. -/
theorem repeated_weight_posterior (a : ℝ) (ha : 0 < a) :
    spectralState (1 : Operator 2) (fun _ => a/(a+a)) =
      (1/2 : ℂ) • (1 : Operator 2) ∧
    spectralState (1 : Operator 2) (fun _ => a/(a+a)) ≠ outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
  have hv : a/(a+a) = (1/2 : ℝ) := by field_simp; ring
  constructor
  · ext i j
    by_cases hij : i = j <;> simp [spectralState, hv, hij]
  · intro h
    have hh := congrArg (fun X : Operator 2 => X 1 1) h
    norm_num [spectralState, hv, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket] at hh

/-- In a unitary basis, the trace norm of a spectral state with real weights is at most the sum
of their absolute values. -/
theorem spectralState_norm_bound {D : ℕ} (V : Operator D) (w : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (spectralState V w).traceNorm ≤ ∑ i, |w i| := by
  let p := fun i => max (w i) 0
  let q := fun i => max (-w i) 0
  have hw : w = fun i => p i-q i := by
    funext i
    dsimp [p,q]
    rcases le_total 0 (w i) with hi | hi <;> simp [hi, neg_nonpos.mpr, neg_nonneg.mpr]
  have heq : spectralState V w = spectralState V p + -(spectralState V q) := by
    conv_lhs => rw [hw, spectralState_sub]
    rfl
  rw [heq]
  have hb := Matrix.traceNorm_add_le (spectralState V p) (-(spectralState V q))
  rw [traceNorm_neg, posSemidef_traceNorm_eq_re (spectralState_pos V p (fun i => le_max_right _ _)),
    posSemidef_traceNorm_eq_re (spectralState_pos V q (fun i => le_max_right _ _)),
    spectralState_trace V p hV, spectralState_trace V q hV, Complex.ofReal_re,
    Complex.ofReal_re, ← Finset.sum_add_distrib] at hb
  refine hb.trans_eq (Finset.sum_congr rfl (fun i _ => ?_))
  dsimp [p,q]
  rcases le_total 0 (w i) with hi | hi
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi, add_zero]
  · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), abs_of_nonpos hi, zero_add]

/-- The linear map summing the data blocks at the selected clock labels `E`. -/
def selectClock {D M : ℕ} (E : Finset (Fin M)) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ →ₗ[ℂ] Operator D :=
  ∑ z ∈ E, dataBlock z

/-- Selecting a finite collection of clock label blocks preserves positive semidefiniteness. -/
theorem selectClock_pos {D M : ℕ} (E : Finset (Fin M))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) : (selectClock E X).PosSemidef := by
  simp only [selectClock, LinearMap.sum_apply]
  exact Matrix.posSemidef_sum _ (fun z _ => dataBlock_pos z X hX)

/-- For a positive semidefinite input, selecting clock labels cannot increase its real trace. -/
theorem selectClock_tni {D M : ℕ} (E : Finset (Fin M))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) : (trace (selectClock E X)).re ≤ (trace X).re := by
  simp only [selectClock, LinearMap.sum_apply, trace_sum, Complex.re_sum, dataBlock_mass]
  rw [← copyQPELabelMass_sum D M X]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    (fun z _ _ => copyQPELabelMass_nonneg D M X hX z)

/-- The eigenvalue weighted sum of outer products of spectral basis columns scaled by their
label kernel amplitudes. -/
def kernelBranch {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (K : Fin D → Fin M → ℂ) (z : Fin M) : Operator D :=
  ∑ i, (eig i : ℂ) • outerProduct (fun j => K i z * V j i)

/-- A kernel branch is the spectral state with weights `eig i * ‖K i z‖²`. -/
theorem kernelBranch_spectral {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (K : Fin D → Fin M → ℂ) (z : Fin M) :
    kernelBranch eig V K z = spectralState V (fun i => eig i * ‖K i z‖^2) := by
  rw [spectralState_sum]
  ext a b
  simp only [kernelBranch, Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply,
    Complex.ofReal_mul, Complex.ofReal_pow, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (‖K i z‖ : ℂ)^2 = K i z * starRingEnd ℂ (K i z) by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; ring]
  ring

/-- Extracting label `z` from the joint kernel mixture gives `kernelBranch eig V K z`. -/
theorem kernel_dataBlock {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (K : Fin D → Fin M → ℂ) (z : Fin M) :
    dataBlock z (∑ i, (eig i : ℂ) • outerProduct (fun p : Fin M × (Bool × Fin D) =>
      if p.2.1 then 0 else K i p.1 * V p.2.2 i)) = kernelBranch eig V K z := by
  ext i j
  simp only [dataBlock, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_bool,
    kernelBranch, Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply,
    if_true, Bool.false_eq_true, if_false, mul_zero, map_zero, smul_zero,
    Finset.sum_const_zero, zero_add]

/-- The sum of squared kernel amplitudes over the retained label set `E` for eigenvector index
`i`. -/
def keepProbability {D M : ℕ} (K : Fin D → Fin M → ℂ) (E : Finset (Fin M)) (i : Fin D) : ℝ :=
  ∑ z ∈ E, ‖K i z‖^2

/-- Selecting clock labels from the joint kernel mixture gives a spectral state with weights
equal to the eigenvalues times their retention probabilities. -/
theorem select_kernel_spectral {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (K : Fin D → Fin M → ℂ) (E : Finset (Fin M)) :
    selectClock E (∑ i, (eig i : ℂ) • outerProduct (fun p : Fin M × (Bool × Fin D) =>
      if p.2.1 then 0 else K i p.1 * V p.2.2 i)) =
      spectralState V (fun i => eig i*keepProbability K E i) := by
  simp only [selectClock, LinearMap.sum_apply, kernel_dataBlock, kernelBranch_spectral,
    spectralState_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  exact (Finset.mul_sum E (fun z => ‖K i z‖^2) (eig i)).symm

/-- The eigenvalue weighted absolute discrepancy between label retention probabilities and
membership in the target spectral index set. -/
def classificationRisk {D M : ℕ} (eig : Fin D → ℝ) (K : Fin D → Fin M → ℂ)
    (E : Finset (Fin M)) (S : Finset (Fin D)) : ℝ :=
  ∑ i, eig i * |keepProbability K E i - if i ∈ S then 1 else 0|

/-- For nonnegative spectral weights and a unitary basis, the selected spectral state's trace
norm error from the target principal part is at most its classification risk. -/
theorem selected_principal_error {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (he : ∀ i, 0 ≤ eig i)
    (K : Fin D → Fin M → ℂ) (E : Finset (Fin M)) (S : Finset (Fin D)) :
    (spectralState V (fun i => eig i*keepProbability K E i) - principalState V eig S).traceNorm ≤
      classificationRisk eig K E S := by
  rw [principalState, ← spectralState_sub]
  refine (spectralState_norm_bound V _ hV).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, if_true, if_false, sub_zero]
  · rw [show eig i*keepProbability K E i - eig i = eig i*(keepProbability K E i-1) by ring,
      abs_mul, abs_of_nonneg (he i)]
  · rw [abs_mul, abs_of_nonneg (he i)]

/-- For density matrix Hamiltonian input and a unitary circuit, the ideal copy phase estimation
program preserves positive semidefiniteness and trace on positive inputs. -/
theorem idealProgram_positive_trace {D M : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (C : Circuit (Fin M × (Bool × Fin D))) (hC : IsUnitaryCircuit C)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.PosSemidef) :
    (copyQPEIdealProgram D M ρ C X).PosSemidef ∧ trace (copyQPEIdealProgram D M ρ C X) = trace X := by
  let U := TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))
  have hU : U ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (hamiltonianEvolution_unitary hρ.1.isHermitian Real.pi))
  have hc (W : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
      (hW : W ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ) (Y) :
      trace (MatrixMap.conj W Y) = trace Y := by
    rw [conjMap_apply, trace_mul_cycle]
    have hw : Wᴴ*W = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hW
    rw [hw, one_mul]
  induction C generalizing X with
  | nil => exact ⟨hX,rfl⟩
  | cons s C ih =>
    cases s with
    | query =>
      have hh := ih ((isUnitaryCircuit_query C).mp hC) (MatrixMap.conj U X)
        (hX.mul_mul_conjTranspose_same U)
      exact ⟨hh.1, hh.2.trans (hc U hU X)⟩
    | gate W =>
      obtain ⟨hW,hC'⟩ := (isUnitaryCircuit_gate W C).mp hC
      have hh := ih hC' (MatrixMap.conj W X) (hX.mul_mul_conjTranspose_same W)
      exact ⟨hh.1, hh.2.trans (hc W hW X)⟩

/-- For density input and `M ≥ 2`, the ideal sine envelope output is positive semidefinite with
trace one. -/
theorem sine_ideal_density {D M : ℕ} (hM : 2 ≤ M) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (sineIdeal D M hM ρ).PosSemidef ∧ trace (sineIdeal D M hM ρ) = 1 := by
  have hx := copyQPEInput_density D M (by omega) ρ hρ
  have ht := idealProgram_positive_trace ρ hρ (sinEnvelopePhaseCircuit M hM)
    (sin_envelope_phase_circuit_unitary M hM) _ hx.1
  exact ⟨ht.1, ht.2.trans hx.2⟩

/-- On positive inputs with equal trace, selecting clock labels contracts their trace norm
difference. -/
theorem selectClock_error {D M : ℕ} (E : Finset (Fin M))
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (ht : trace X = trace Y) :
    (selectClock E X - selectClock E Y).traceNorm ≤ (X-Y).traceNorm := by
  have hb := positive_tni_trace_zero_budget (selectClock E) (selectClock_pos E) (selectClock_tni E)
    (X-Y) (hX.isHermitian.sub hY.isHermitian) (by rw [trace_sub, ht]; simp)
  rw [map_sub] at hb
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans hb

/-- The data matrix obtained by retaining the specified clock labels from the actual sine
envelope output. -/
def sineSelected {D M n : ℕ} (hM : 2 ≤ M) (ρ : Operator D) (E : Finset (Fin M)) : Operator D :=
  selectClock E (sineActual D M n hM ρ)

/-- Selecting labels from the ideal sine envelope output multiplies each spectral weight by its
sine kernel retention probability. -/
theorem sine_selected_spectral {D M : ℕ} (hM : 2 ≤ M) (ρ V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig) (E : Finset (Fin M)) :
    selectClock E (sineIdeal D M hM ρ) =
      spectralState V (fun i => eig i*keepProbability (fun j => sinEnvelopeKernel M (-eig j/2)) E i) := by
  rw [sine_spectral_output hM ρ V eig hV hs]
  exact select_kernel_spectral eig V (fun j => sinEnvelopeKernel M (-eig j/2)) E

/-- If copy error plus classification risk is less than the retained spectral mass, the actual
selected branch has positive mass and its normalized density matrix is within twice that
total error divided by the retained mass of the normalized principal state. -/
theorem sine_selected_principal {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (E : Finset (Fin M)) (S : Finset (Fin D))
    (hp : 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) +
      classificationRisk eig (fun j => sinEnvelopeKernel M (-eig j/2)) E S < ∑ i ∈ S, eig i) :
    0 < (trace (sineSelected (n := n) hM ρ E)).re ∧
    IsDensityOperator (normalizedPositiveBranch (sineSelected (n := n) hM ρ E)) ∧
    (normalizedPositiveBranch (sineSelected (n := n) hM ρ E) -
      normalizedPositiveBranch (principalState V eig S)).traceNorm ≤
      2*(8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) +
        classificationRisk eig (fun j => sinEnvelopeKernel M (-eig j/2)) E S) / (∑ i ∈ S, eig i) := by
  let X := sineActual D M n hM ρ
  let Y := sineIdeal D M hM ρ
  let A := selectClock E X
  let P := principalState V eig S
  let e := 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) +
    classificationRisk eig (fun j => sinEnvelopeKernel M (-eig j/2)) E S
  have he := spectrum_nonneg ρ V eig hρ hV hs
  have hx := sine_actual_error hM hn ρ hρ
  have hy := sine_ideal_density hM ρ hρ
  have ha : A.PosSemidef := selectClock_pos E X hx.1
  have hP : P.PosSemidef := principal_pos V eig he S
  have hnE : 0 ≤ e := by
    apply add_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (he i) (abs_nonneg _))
  have hab : (A-selectClock E Y).traceNorm ≤ 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) :=
    (selectClock_error E X Y hx.1 hy.1 (hx.2.1.trans hy.2.symm)).trans hx.2.2
  have hbp : (selectClock E Y-P).traceNorm ≤ classificationRisk eig
      (fun j => sinEnvelopeKernel M (-eig j/2)) E S := by
    change (selectClock E (sineIdeal D M hM ρ)-principalState V eig S).traceNorm ≤ _
    rw [sine_selected_spectral hM ρ V eig hV hs]
    exact selected_principal_error eig V hV he _ E S
  have hap : (A-P).traceNorm ≤ e := by
    have hid : A-P = (A-selectClock E Y)+(selectClock E Y-P) := by abel
    rw [hid]
    exact (Matrix.traceNorm_add_le _ _).trans (add_le_add hab hbp)
  have hm : |(trace A).re - (trace P).re| ≤ e := by
    rw [← Complex.sub_re, ← trace_sub]
    exact ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans hap
  have htP : (trace P).re = ∑ i ∈ S, eig i := by rw [principal_trace V eig hV]; rfl
  have hAp : 0 < (trace A).re := by have h := (abs_le.mp hm).1; rw [htP] at h; linarith
  have hPp : 0 < (trace P).re := by rw [htP]; exact hnE.trans_lt hp
  have hd := normalized_positive_branch_distance (Fin D) A P ha hP hAp hPp
  refine ⟨hAp, normalize_density A ha hAp, hd.trans ?_⟩
  calc _ ≤ (2*e) / max (trace A).re (trace P).re :=
         div_le_div_of_nonneg_right (by linarith) (le_trans hPp.le (le_max_right _ _))
       _ ≤ (2*e)/(trace P).re := div_le_div_of_nonneg_left (by positivity) hPp (le_max_right _ _)
       _ = _ := by rw [htP]

/-- For `r` in `[0, 1]`, the decoded eigenvalue error is at most twice the circular phase
distance from `-r / 2` to the clock label. -/
theorem eigenvalue_decode_lipschitz (M : ℕ) (hM : 2 ≤ M) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : Fin M) :
    |qpeLabelDecode M z-r| ≤ 2*phaseDistance (-r/2) ((z.val : ℝ)/M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let x := (z.val : ℝ)/M
  let d := phaseDistance (-r/2) x
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := (div_lt_one hMr).mpr (by exact_mod_cast z.isLt)
  let c : ℤ := ⌊-r/2-x+1/2⌋
  have hc0 : c ≤ 0 := by
    have h : c < 1 := Int.floor_lt.mpr (by norm_num; linarith)
    omega
  have hc1 : -1 ≤ c := Int.le_floor.mpr (by norm_num; linarith)
  have hw : |-r/2-x-(c : ℝ)| ≤ d := le_rfl
  have hm0 : 0 ≤ min x (1-x) := le_min hx0 (by linarith)
  have hmx : min x (1-x) ≤ x := min_le_left _ _
  change |2*min x (1-x)-r| ≤ 2*d
  obtain hc | hc : c = 0 ∨ c = -1 := by omega
  · rw [hc] at hw
    norm_num only [Int.cast_zero, sub_zero] at hw
    obtain ⟨hl,hu⟩ := abs_le.mp hw
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hc] at hw
    norm_num only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] at hw
    obtain ⟨hl,hu⟩ := abs_le.mp hw
    rcases le_total x (1-x) with hx | hx
    · rw [min_eq_left hx]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [min_eq_right hx]
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The clock labels whose decoded eigenvalues are at least the threshold `τ`. -/
def principalLabels (M : ℕ) (τ : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun z => τ ≤ qpeLabelDecode M z)

/-- The spectral indices whose eigenvalues are at least the threshold `τ`. -/
def principalIndices {D : ℕ} (eig : Fin D → ℝ) (τ : ℝ) : Finset (Fin D) :=
  Finset.univ.filter (fun i => τ ≤ eig i)

/-- If eigenvalues lie in `[0, 1]` and avoid the threshold by `2 * ε`, a label within phase
distance `ε` is retained exactly when its eigenvalue is above threshold. -/
theorem threshold_agreement {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (he0 : ∀ i, 0 ≤ eig i) (he1 : ∀ i, eig i ≤ 1) (τ ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ i, eig i ≤ τ-2*ε ∨ τ+2*ε ≤ eig i) (i : Fin D) (z : Fin M)
    (hz : phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε) :
    z ∈ principalLabels M τ ↔ i ∈ principalIndices eig τ := by
  have hd := eigenvalue_decode_lipschitz M hM (eig i) (he0 i) (he1 i) z
  have hprec : |qpeLabelDecode M z-eig i| < 2*ε := by linarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hprec
  simp only [principalLabels, principalIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hgap i with hi | hi
  · have hx : ¬τ ≤ eig i := by linarith
    have hy : ¬τ ≤ qpeLabelDecode M z := by linarith
    simp [hx,hy]
  · have hx : τ ≤ eig i := by linarith
    have hy : τ ≤ qpeLabelDecode M z := by linarith
    simp [hx,hy]

/-- For a normalized nonnegative spectrum, label classification that agrees within phase
distance `ε` has risk at most `sineMomentConstant / (2 * π * M * ε)²`. -/
theorem sine_classification_risk {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (he : ∀ i, 0 ≤ eig i) (hsum : ∑ i, eig i = 1)
    (E : Finset (Fin M)) (S : Finset (Fin D)) (ε : ℝ) (hε : 0 < ε)
    (hagree : ∀ i z, phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε → (z ∈ E ↔ i ∈ S)) :
    classificationRisk eig (fun j => sinEnvelopeKernel M (-eig j/2)) E S ≤
      sineMomentConstant/(2*Real.pi*(M : ℝ)*ε)^2 := by
  let K := fun j => sinEnvelopeKernel M (-eig j/2)
  have hi (i : Fin D) : |keepProbability K E i - if i ∈ S then 1 else 0| ≤
      sineMomentConstant/(2*Real.pi*(M : ℝ)*ε)^2 := by
    have hp : 0 ≤ keepProbability K E i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hnorm : ∑ z, ‖K i z‖^2 = 1 := sin_envelope_kernel_normalized M (-eig i/2) hM
    have hc : (∑ z ∈ Eᶜ, ‖K i z‖^2) = 1-keepProbability K E i := by
      have h := Finset.sum_add_sum_compl E (fun z => ‖K i z‖^2)
      rw [hnorm] at h
      change keepProbability K E i + _ = 1 at h
      linarith
    have hp1 : keepProbability K E i ≤ 1 := by
      have h := Finset.sum_nonneg (fun z (_ : z ∈ Eᶜ) => sq_nonneg ‖K i z‖)
      linarith
    by_cases hS : i ∈ S
    · rw [if_pos hS, abs_of_nonpos (by linarith), neg_sub, ← hc]
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
        (fun z : Fin M => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M))) ?_
        (fun _ _ _ => sq_nonneg _)).trans (sine_phase_tail M hM (-eig i/2) ε hε)
      intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z, not_lt.mp ?_⟩
      intro hgood
      exact (Finset.mem_compl.mp hz) ((hagree i z hgood).mpr hS)
    · rw [if_neg hS, sub_zero, abs_of_nonneg hp]
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
        (fun z : Fin M => ε ≤ phaseDistance (-eig i/2) ((z.val : ℝ)/M))) ?_
        (fun _ _ _ => sq_nonneg _)).trans (sine_phase_tail M hM (-eig i/2) ε hε)
      intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z, not_lt.mp ?_⟩
      intro hgood
      exact hS ((hagree i z hgood).mp hz)
  calc
    _ ≤ ∑ i, eig i*(sineMomentConstant/(2*Real.pi*(M : ℝ)*ε)^2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (he i))
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- For a gapped density spectrum with retained mass greater than `δ`, the sine schedule
produces a positive selected branch whose normalized state is within `2 * δ` divided by
retained mass of the normalized principal part, with the stated rank bound and resource
tuple. -/
theorem threshold_principal_correctness {D : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hρ : IsDensityOperator ρ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = spectralState V eig) (he1 : ∀ i, eig i ≤ 1)
    (τ ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hgap : ∀ i, eig i ≤ τ-2*ε ∨ τ+2*ε ≤ eig i)
    (hmass : δ < ∑ i ∈ principalIndices eig τ, eig i) :
    let M := (sineSchedule ε δ).1
    let n := (sineSchedule ε δ).2
    let hM := (sineSchedule_valid ε δ hε hδ).1
    let E := principalLabels M τ
    let S := principalIndices eig τ
    0 < (trace (sineSelected (n := n) hM ρ E)).re ∧
    IsDensityOperator (normalizedPositiveBranch (sineSelected (n := n) hM ρ E)) ∧
    (normalizedPositiveBranch (sineSelected (n := n) hM ρ E) -
      normalizedPositiveBranch (principalState V eig S)).traceNorm ≤ 2*δ/(∑ i ∈ S, eig i) ∧
    (principalState V eig S).rank ≤ S.card ∧
    copyQPEProgramResources n (sinEnvelopePhaseCircuit (I := Fin D) M hM) =
      ((M-1)*n, (M-1)*n, (M-1)*n, 0) := by
  (try dsimp only)
  let M := (sineSchedule ε δ).1
  let n := (sineSchedule ε δ).2
  have hbud := sineSchedule_valid ε δ hε hδ
  have he := spectrum_nonneg ρ V eig hρ hV hs
  have hsum : ∑ i, eig i = 1 := by
    have ht := hρ.2
    rw [hs, spectralState_trace V eig hV] at ht
    exact_mod_cast ht
  have hrisk := sine_classification_risk hbud.1 eig he hsum (principalLabels M τ)
    (principalIndices eig τ) ε hε (threshold_agreement hbud.1 eig he he1 τ ε hε hgap)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hden : 0 < (2*Real.pi*(M : ℝ)*ε)^2 := by positivity
  have hsmall : classificationRisk eig (fun j => sinEnvelopeKernel M (-eig j/2))
      (principalLabels M τ) (principalIndices eig τ) ≤ δ/2 :=
    hrisk.trans ((div_le_iff₀ hden).mpr hbud.2.2.1)
  have hb := sine_selected_principal hbud.1 hbud.2.1 ρ V eig hρ hV hs
    (principalLabels M τ) (principalIndices eig τ) (by have ha := hbud.2.2.2; linarith)
  refine ⟨hb.1, hb.2.1, hb.2.2.trans ?_, principal_rank V eig _, (sine_counts hbud.1 n).1⟩
  apply div_le_div_of_nonneg_right
  · have ha := hbud.2.2.2; linarith
  · exact (hδ.trans hmass).le

/-- Retaining one spectral index gives its eigenvalue times the outer product of the
corresponding basis column. -/
theorem principal_singleton {D : ℕ} (V : Operator D) (eig : Fin D → ℝ) (i : Fin D) :
    principalState V eig {i} = (eig i : ℂ) • outerProduct (fun j => V j i) := by
  rw [principalState, spectralState_sum]
  simp

/-- For a unitary basis and positive eigenvalue, normalizing a singleton principal state gives
the outer product of that basis column. -/
theorem principal_singleton_normalized {D : ℕ} (V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) (hi : 0 < eig i) :
    normalizedPositiveBranch (principalState V eig {i}) = outerProduct (fun j => V j i) := by
  have ht : (trace (principalState V eig {i})).re = eig i := by rw [principal_trace V eig hV]; simp
  rw [normalizedPositiveBranch, ht, if_pos hi, principal_singleton, smul_smul]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hi)]
  simp

/-- A spectral mixture with probability weights is within trace norm `2 * (1 - p.prob i)` of the
outer product of basis column `i`. -/
theorem posterior_eigenvector_error {D : ℕ} (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : FinDist (Fin D)) (i : Fin D) :
    (spectralState V p.prob - outerProduct (fun j => V j i)).traceNorm ≤ 2*(1-p.prob i) := by
  have hpi : p.prob i ≤ 1 := by
    rw [← p.sum_one]
    exact Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)
  have hcol : spectralState V (fun j => if j=i then 1 else 0) = outerProduct (fun j => V j i) := by
    rw [spectralState_sum]
    simp
  rw [← hcol, ← spectralState_sub]
  refine (spectralState_norm_bound V _ hV).trans_eq ?_
  calc
    _ = ∑ j, (p.prob j + if j=i then 1-2*p.prob i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : j=i
      · subst j
        rw [if_pos rfl, abs_of_nonpos (sub_nonpos.mpr hpi), if_pos rfl]
        ring
      · simp [hij, p.nonneg j, abs_of_nonneg]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [p.sum_one]; ring

/-- If the ideal branch has sufficient mass and posterior weight outside `i` at most `δ`, the
actual conditional state's trace norm error from eigenvector `i` is at most the global copy
error divided by branch mass plus `2 * δ`. See [LloydMohseniRebentrost2014]. -/
theorem conditional_eigenvector_error {D M n : ℕ} (hM : 2 ≤ M) (hn : 0 < n)
    (ρ V : Operator D) (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hs : ρ = spectralState V eig)
    (z : Fin M) (i : Fin D) (δ : ℝ)
    (hp : (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/2 < branchTotal eig z)
    (hbad : branchTotal eig z - branchWeight eig z i ≤ δ*branchTotal eig z) :
    (normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ)) -
      outerProduct (fun j => V j i)).traceNorm ≤
        (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/branchTotal eig z + 2*δ := by
  have he := spectrum_nonneg ρ V eig hρ hV hs
  have hp0 : 0 < branchTotal eig z := lt_of_le_of_lt (by positivity) hp
  have ha := (actual_conditional_state hM hn ρ V eig hρ hV hs z hp).2.2
  rw [normalized_offgrid_posterior eig V hV he z hp0] at ha
  have hb := posterior_eigenvector_error V hV (posterior eig he z hp0) i
  have hc := posterior_accuracy eig he z hp0 i δ hbad
  have hid : normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ)) -
      outerProduct (fun j => V j i) =
      (normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ)) - spectralState V (posterior eig he z hp0).prob) +
        (spectralState V (posterior eig he z hp0).prob - outerProduct (fun j => V j i)) := by abel
  rw [hid]
  refine (Matrix.traceNorm_add_le _ _).trans ((add_le_add ha hb).trans ?_)
  linarith

/-- The real weights in a unitary spectral representation of a density operator sum to one. -/
theorem spectrum_sum {D : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hρ : IsDensityOperator ρ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = spectralState V eig) : ∑ i, eig i = 1 := by
  have ht := hρ.2
  rw [hs, spectralState_trace V eig hV] at ht
  exact_mod_cast ht

/-- Each real weight in a unitary spectral representation of a density operator is at most one. -/
theorem spectrum_le_one {D : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hρ : IsDensityOperator ρ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = spectralState V eig) (i : Fin D) : eig i ≤ 1 := by
  rw [← spectrum_sum ρ V eig hρ hV hs]
  exact Finset.single_le_sum (fun j _ => spectrum_nonneg ρ V eig hρ hV hs j) (Finset.mem_univ i)

/-- The recursive source use count for repeated circuit runs, charging one input copy and the
circuit's copy query resource count per run. -/
def batchSourceUses {D M : ℕ} (n : ℕ) (C : Circuit (Fin M × (Bool × Fin D))) : ℕ → ℕ
  | 0 => 0
  | m+1 => 1 + (copyQPEProgramResources n C).1 + batchSourceUses n C m

/-- The source use count for `m` runs is `m * (1 + QueryCount C * n)`. -/
theorem batchSourceUses_eq {D M : ℕ} (n : ℕ) (C : Circuit (Fin M × (Bool × Fin D))) (m : ℕ) :
    batchSourceUses n C m = m*(1+QueryCount C*n) := by
  induction m with
  | zero => simp [batchSourceUses]
  | succ m ih => rw [batchSourceUses, ih, copyQPEProgramResources_eq]; ring

/-- The source use count for `m` sine envelope runs is `m * (1 + (M - 1) * n)`. -/
theorem sine_batch_source_uses {D M : ℕ} (hM : 2 ≤ M) (n m : ℕ) :
    batchSourceUses n (sinEnvelopePhaseCircuit (I := Fin D) M hM) m = m*(1+(M-1)*n) := by
  rw [batchSourceUses_eq, (sine_counts (D := D) hM n).2.1]

/-- For a completely positive trace preserving map, copy phase estimation on its process state
has the stated finite copy error bound and its spectral factor yields a complete Kraus
representation. See [LloydMohseniRebentrost2014]. -/
theorem process_qpca_consumer {D E M n : ℕ} (hD : 0 < D) (hM : 2 ≤ M) (hn : 0 < n)
    (T : Operator D →ₗ[ℂ] Operator E) (hCP : CompletelyPositive T) (hTP : TracePreserving T)
    (V : Operator (D*E)) (eig : Fin (D*E) → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin (D*E)) ℂ) (hs : processState T = spectralState V eig) :
    (copyQPEOutput (D*E) M n (processState T) - copyQPEIdealOutput (D*E) M (processState T)).traceNorm ≤
      8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ∧
    let F := relabelGate (finProdFinEquiv (m := D) (n := E)).symm (spectralFactor D V eig)
    KrausForm T (krausOfFactor F) ∧ KrausComplete (krausOfFactor F) := by
  have hρ := process_density hD T hCP hTP
  exact ⟨(copy_qpe_actual_program_state_error (D*E) M n hM hn (processState T) hρ).2.2,
    process_spectral_kraus hD T hTP V eig (spectrum_nonneg _ V eig hρ hV hs) hs⟩

/-- The proposition asserting the ideal spectral output formula, actual density property, finite
copy trace norm error, and resource tuple for standard copy phase estimation. -/
def FullEq2 : Prop :=
  ∀ (D M n : ℕ), 2 ≤ M → 0 < n → ∀ (ρ V : Operator D) (eig : Fin D → ℝ),
  IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ → ρ = spectralState V eig →
  copyQPEIdealOutput D M ρ = ∑ i, (eig i : ℂ) • outerProduct
    (fun p : Fin M × (Bool × Fin D) => if p.2.1 then 0 else qpeKernel M (-eig i/2) p.1 * V p.2.2 i) ∧
  ((copyQPEOutput D M n ρ).PosSemidef ∧ trace (copyQPEOutput D M n ρ) = 1) ∧
  (copyQPEOutput D M n ρ-copyQPEIdealOutput D M ρ).traceNorm ≤ 8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ∧
  copyQPEResources D M n = ((M-1)*n,(M-1)*n,(M-1)*n,0)

/-- The proposition bounding conditional eigenvector error by the copy error divided by ideal
branch mass plus twice the posterior error. -/
def ConditionalEigenvectors : Prop :=
  ∀ (D M n : ℕ) (_hM : 2 ≤ M) (_hn : 0 < n) (ρ V : Operator D) (eig : Fin D → ℝ)
    (_hρ : IsDensityOperator ρ) (_hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (_hs : ρ = spectralState V eig) (z : Fin M) (i : Fin D) (δ : ℝ),
  (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/2 < branchTotal eig z →
  branchTotal eig z-branchWeight eig z i ≤ δ*branchTotal eig z →
  (normalizedPositiveBranch (dataBlock z (copyQPEOutput D M n ρ))-outerProduct (fun j => V j i)).traceNorm ≤
    (8*(M-1 : ℕ)*Real.pi^2/(n : ℝ))/branchTotal eig z+2*δ

/-- The proposition asserting unbiased observable sample means, variance divided by sample
count, and the corresponding variance tail bound for independent fresh measurements. -/
def IndependentLearning : Prop :=
  ∀ (D m : ℕ) (A σ : Operator D) (hA : A.IsHermitian) (hσ : IsDensityOperator σ), 0 < m →
  ∀ (ε : ℝ), 0 < ε →
    let Λ := observablePOVM A hA
    let r := freshPovmLaw (fun _ : Fin m => D) (fun _ => Λ) (fun _ => σ) (fun _ => hσ)
    r.expect (FinDist.avg hA.eigenvalues) = (trace (A*σ)).re ∧
    r.expect (fun ω => (FinDist.avg hA.eigenvalues ω-(trace (A*σ)).re)^2) =
      (povmLaw Λ σ hσ).variance hA.eigenvalues/m ∧
    eventMass r (fun ω => ε < |FinDist.avg hA.eigenvalues ω-(trace (A*σ)).re|) ≤
      (povmLaw Λ σ hσ).variance hA.eigenvalues/(m*ε^2)

/-- The proposition that the sine schedule gives phase accuracy less than `ε` with event mass at
least `1 - δ` for every density spectrum. -/
def ImprovedPhase : Prop :=
  ∀ (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ), IsDensityOperator ρ →
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → ρ = spectralState V eig →
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ),
    let M := (sineSchedule ε δ).1
    let n := (sineSchedule ε δ).2
    let hM := (sineSchedule_valid ε δ hε hδ).1
    1-δ ≤ (trace (eventEffect V (fun z i => phaseDistance (-eig i/2) ((z.val : ℝ)/M) < ε) *
      sineActual D M n hM ρ)).re

/-- The proposition asserting normalized principal component selection bounds, positivity, rank
control, and resource counts for spectra separated from the threshold. -/
def PrincipalComponents : Prop :=
  ∀ (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ) (_hρ : IsDensityOperator ρ)
    (_hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (_hs : ρ = spectralState V eig)
    (τ ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ),
  (∀ i, eig i ≤ τ-2*ε ∨ τ+2*ε ≤ eig i) → δ < ∑ i ∈ principalIndices eig τ, eig i →
    let M := (sineSchedule ε δ).1
    let n := (sineSchedule ε δ).2
    let hM := (sineSchedule_valid ε δ hε hδ).1
    let E := principalLabels M τ
    let S := principalIndices eig τ
    0 < (trace (sineSelected (n := n) hM ρ E)).re ∧
    IsDensityOperator (normalizedPositiveBranch (sineSelected (n := n) hM ρ E)) ∧
    (normalizedPositiveBranch (sineSelected (n := n) hM ρ E)-
      normalizedPositiveBranch (principalState V eig S)).traceNorm ≤ 2*δ/(∑ i ∈ S, eig i) ∧
    (principalState V eig S).rank ≤ S.card ∧
    copyQPEProgramResources n (sinEnvelopePhaseCircuit (I := Fin D) M hM) =
      ((M-1)*n,(M-1)*n,(M-1)*n,0)

/-- The proposition combining finite copy phase estimation error on a channel's normalized Choi
state with complete Kraus reconstruction from its spectral factor. -/
def ProcessLearning : Prop :=
  ∀ (D E M n : ℕ), 0 < D → 2 ≤ M → 0 < n → ∀ (T : Operator D →ₗ[ℂ] Operator E),
  CompletelyPositive T → TracePreserving T → ∀ (V : Operator (D*E)) (eig : Fin (D*E) → ℝ),
  V ∈ Matrix.unitaryGroup (Fin (D*E)) ℂ → processState T = spectralState V eig →
    (copyQPEOutput (D*E) M n (processState T)-copyQPEIdealOutput (D*E) M (processState T)).traceNorm ≤
      8*(M-1 : ℕ)*Real.pi^2/(n : ℝ) ∧
    let F := relabelGate (finProdFinEquiv (m := D) (n := E)).symm (spectralFactor D V eig)
    KrausForm T (krausOfFactor F) ∧ KrausComplete (krausOfFactor F)

/-- The six specifications `FullEq2`, `ConditionalEigenvectors`, `IndependentLearning`,
`ImprovedPhase`, `PrincipalComponents`, and `ProcessLearning` all hold. -/
theorem frontier1 : FullEq2 ∧ ConditionalEigenvectors ∧ IndependentLearning ∧
    ImprovedPhase ∧ PrincipalComponents ∧ ProcessLearning := by
  refine ⟨fun _ _ _ hM hn ρ V eig hρ hV hs => offgrid_full_output hM hn ρ V eig hρ hV hs,
    fun _ _ _ hM hn ρ V eig hρ hV hs z i δ hp hb =>
      conditional_eigenvector_error hM hn ρ V eig hρ hV hs z i δ hp hb,
    ?_, ?_, ?_, fun _ _ _ _ hD hM hn T hCP hTP V eig hV hs =>
      process_qpca_consumer hD hM hn T hCP hTP V eig hV hs⟩
  · intro D m A σ hA hσ hm ε hε
    have ht := fresh_mean_variance_tail (observablePOVM A hA) σ hσ hA.eigenvalues hm ε hε
    rw [observable_mean A σ hA hσ] at ht
    exact ht
  · intro D ρ V eig hρ hV hs ε δ hε hδ
    have hb := sineSchedule_valid ε δ hε hδ
    exact sine_success_probability hb.1 hb.2.1 ρ V eig hρ hV hs
      (spectrum_nonneg ρ V eig hρ hV hs) ε δ hε hb.2.2.1 hb.2.2.2
  · intro D ρ V eig hρ hV hs τ ε δ hε hδ hgap hmass
    exact threshold_principal_correctness ρ V eig hρ hV hs (spectrum_le_one ρ V eig hρ hV hs)
      τ ε δ hε hδ hgap hmass

/-- For positive dimension `D`, the matrix `omegaMatrix D` scaled by `1 / D` is positive
semidefinite with trace one. -/
theorem process_source_input (D : ℕ) (hD : 0 < D) :
    ((D : ℂ)⁻¹ • omegaMatrix D).PosSemidef ∧ trace ((D : ℂ)⁻¹ • omegaMatrix D) = 1 := by
  have hn : (0 : ℂ) ≤ (D : ℂ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg D : (0 : ℝ) ≤ D))
  refine ⟨(omegaMatrix_posSemidef D).smul hn, ?_⟩
  have ht : trace (omegaMatrix D) = (D : ℂ) := by
    simp only [trace, diag_apply, Fintype.sum_prod_type, omegaMatrix]
    simp
  rw [trace_smul, ht]
  exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hD)

end
end Qatlib.Papers.QuantumPCA14.FeatureReadout
