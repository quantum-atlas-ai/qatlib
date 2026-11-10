/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyQpcaDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix
open Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem clause8_gram_entry_convention {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (i j : Fin d) :
    gramEntry A i j = (gramOperator A) i j := by
  simp only [gramEntry, gramOperator, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rfl

theorem clause8_gram_trace {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) :
    Matrix.trace (gramOperator A) = ∑ k, gramColumnNormSq A k := by
  simp only [gramOperator, gramColumnNormSq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem clause8_gram_register {r d : ℕ} (ψ : Fin r → QState (Fin d)) (hψ : ∀ i, Normalized (ψ i))
    (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, (w i) ^ 2 = 1) :
    gramOperator (gramColumn ψ w) = gramMatrix ψ w ∧
    IsDensityOperator (gramMatrix ψ w) := by
  refine ⟨rfl, (gramFirstRegisterDensity r d ψ hψ w hw hsumw).2.2⟩

theorem clause8_pi_dyadic_range (w : ℕ) (k : Fin (2 ^ w)) :
    0 ≤ piDyadicWord w k ∧ piDyadicWord w k < 1 := by
  have hk : (k.val : ℝ) < 2 ^ w := by exact_mod_cast k.isLt
  have h2w : (0 : ℝ) < 2 ^ w := by positivity
  constructor
  · simp only [piDyadicWord]
    positivity
  · simp only [piDyadicWord, div_lt_iff₀ h2w]
    simpa using! hk

theorem clause8_pi_dyadic_step (w : ℕ) (k : Fin (2 ^ w)) (hk : k.val + 1 < 2 ^ w) :
    piDyadicWord w ⟨k.val + 1, by omega⟩ - piDyadicWord w k = (1 : ℝ) / 2 ^ w := by
  simp only [piDyadicWord]
  push_cast
  ring

theorem clause8_qpe_grid_is_pi_dyadic (w : ℕ) :
    Fintype.card (Fin (2 ^ w)) = (2 : ℝ) ^ w := by
  rw [Fintype.card_fin]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem clause8_fresh_step_ledger (D : ℕ) (angles : List ℝ) :
    freshStepLedger D angles = ⟨angles.length, angles.length, angles.length, 0⟩ := by
  simp only [freshStepLedger]
  rw [freshCopyResourceCounts_eq]

theorem clause8_qpe_path_ledger (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) :
    qpePathLedger D M n = ⟨(M - 1) * n, (M - 1) * n, (M - 1) * n, 0⟩ := by
  simp only [qpePathLedger]
  rw [copy_qpe_same_path_fresh_resource_counts D M n hM hn]

theorem clause8_ledger_price (L : QpcaRunLedger) :
    L.price = L.freshCopies + L.gates := rfl

theorem clause9_gram_spectral_events {r d M n : ℕ} (ψ : Fin r → QState (Fin d))
    (hψ : ∀ i, Normalized (ψ i)) (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsumw : ∑ i, (w i) ^ 2 = 1) (hM : 2 ≤ M) (hn : 0 < n)
    (V : Operator r) (hV : V ∈ Matrix.unitaryGroup (Fin r) ℂ) (eig : Fin r → ℝ)
    (hs : gramMatrix ψ w = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ)
    (E : Finset (Fin M)) :
    |(∑ z ∈ E, copyQPELabelMass r M (copyQPEOutput r M n (gramMatrix ψ w)) z) -
        (∑ i, eig i * (∑ z ∈ E, ‖qpeKernel M (-eig i / 2) z‖ ^ 2))| ≤
      8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ∧
    qpePathLedger r M n = ⟨(M - 1) * n, (M - 1) * n, (M - 1) * n, 0⟩ := by
  refine ⟨?_, clause8_qpe_path_ledger r M n hM hn⟩
  exact (gramSpectralReadoutSubgoal r d M n ψ hψ w hw hsumw hM hn V hV eig hs E).1

theorem clause9_offgrid_accuracy :
    Qatlib.Concepts.CopyEvolution.SelfTomography.clause16EndpointSpec :=
  Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.clause16_endpoint

theorem clause9_mcopy_law (M m : ℕ) (p : LabelLaw M) :
    (∑ t : Fin m → Fin M, mCopyLaw M m p t = 1) ∧
    (∀ (j : Fin m) (z : Fin M),
      (∑ t : Fin m → Fin M, mCopyLaw M m p t * (if t j = z then 1 else 0)) = p.mass z) :=
  ⟨mCopyLaw_total M m p, fun j z => mCopyLaw_marginal M m p j z⟩

theorem thresholdGoal_two_species_fresh (D r M n : ℕ) (hM : 0 < M) (hn : 0 < n) (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (t : ℝ)
    (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm (ChannelAmplification (twoSpeciesRun D ρ hρ σ hσ t n).map r X -
        MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution (ρ - σ) t)) X)
      ≤ 32 * t ^ 2 / (n : ℝ) * (Matrix.trace X).re ∧
    twoSpeciesPathLedger M n = ⟨2 * (M - 1) * n, 2 * (M - 1) * n, 2 * (M - 1) * n, 0⟩ := by
  refine ⟨two_species_controlled_fresh_global_error D r n hn ρ σ hρ hσ t X hX, ?_⟩
  simp only [twoSpeciesPathLedger, twoSpeciesQPEResources]

theorem thresholdGoal_sign_error_budget (M n : ℕ) (γ : ℝ) :
    twoSpeciesSignErrorBudget M n γ =
      128 / ((M : ℝ) * γ) + 8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) :=
  (stageB_copy_qpca_clause19).2.2.2.1 M n γ

theorem thresholdGoal_training_set :
    TrainingSetFiniteDiscrimination ∧
    (∀ (d m : ℕ) (φ : Fin m → QState (Fin d)) (hφ : ∀ i, Normalized (φ i)) (hm : 0 < m),
      IsDensityOperator (pureStateMixture d m φ)) := by
  refine ⟨trainingSetFiniteDiscrimination, ?_⟩
  intro d m φ hφ hm
  exact (stageB_copy_qpca_clause19).2.1 d m φ hφ hm

theorem clause16_endpoint :
    StageBCopyQpcaClause16 ∧
    (∀ {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (i j : Fin d),
      gramEntry A i j = (gramOperator A) i j) ∧
    (∀ {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ),
      Matrix.trace (gramOperator A) = ∑ k, gramColumnNormSq A k) ∧
    (∀ (w : ℕ) (k : Fin (2 ^ w)),
      0 ≤ piDyadicWord w k ∧ piDyadicWord w k < 1) ∧
    (∀ (D : ℕ) (angles : List ℝ),
      freshStepLedger D angles = ⟨angles.length, angles.length, angles.length, 0⟩) ∧
    (∀ (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n),
      qpePathLedger D M n = ⟨(M - 1) * n, (M - 1) * n, (M - 1) * n, 0⟩) := by
  refine ⟨stageB_copy_qpca_clause16, ?_, ?_, ?_, ?_, ?_⟩
  · intro m d A i j
    exact clause8_gram_entry_convention A i j
  · intro m d A
    exact clause8_gram_trace A
  · intro w k
    exact clause8_pi_dyadic_range w k
  · intro D angles
    exact clause8_fresh_step_ledger D angles
  · intro D M n hM hn
    exact clause8_qpe_path_ledger D M n hM hn

theorem clause17_endpoint :
    StageBCopyQpcaClause17 ∧
    (∀ {r d M n : ℕ} (ψ : Fin r → QState (Fin d)) (hψ : ∀ i, Normalized (ψ i))
      (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, (w i) ^ 2 = 1) (hM : 2 ≤ M)
      (hn : 0 < n) (V : Operator r) (hV : V ∈ Matrix.unitaryGroup (Fin r) ℂ)
      (eig : Fin r → ℝ)
      (hs : gramMatrix ψ w = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ)
      (E : Finset (Fin M)),
      |(∑ z ∈ E, copyQPELabelMass r M (copyQPEOutput r M n (gramMatrix ψ w)) z) -
          (∑ i, eig i * (∑ z ∈ E, ‖qpeKernel M (-eig i / 2) z‖ ^ 2))| ≤
        8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ)) := by
  refine ⟨stageB_copy_qpca_clause17, ?_⟩
  intro r d M n ψ hψ w hw hsumw hM hn V hV eig hs E
  exact (clause9_gram_spectral_events ψ hψ w hw hsumw hM hn V hV eig hs E).1

theorem clause19_endpoint :
    StageBCopyQpcaClause19 ∧
    (∀ (D r M n : ℕ) (hM : 0 < M) (hn : 0 < n) (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
      (hσ : IsDensityOperator σ) (t : ℝ)
      (X : Matrix (Fin r × Fin (2 * D)) (Fin r × Fin (2 * D)) ℂ) (hX : X.PosSemidef),
      Matrix.traceNorm (ChannelAmplification (twoSpeciesRun D ρ hρ σ hσ t n).map r X -
          MatrixMap.conj (TensorGate (1 : Operator r) (copyControlledEvolution (ρ - σ) t)) X)
        ≤ 32 * t ^ 2 / (n : ℝ) * (Matrix.trace X).re) ∧
    (∀ (M n : ℕ) (γ : ℝ),
      twoSpeciesSignErrorBudget M n γ =
        128 / ((M : ℝ) * γ) + 8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ)) := by
  refine ⟨stageB_copy_qpca_clause19, ?_, ?_⟩
  · intro D r M n hM hn ρ σ hρ hσ t X hX
    exact (thresholdGoal_two_species_fresh D r M n hM hn ρ σ hρ hσ t X hX).1
  · intro M n γ
    exact thresholdGoal_sign_error_budget M n γ

end Qatlib.Concepts.CopyEvolution.SelfTomography
