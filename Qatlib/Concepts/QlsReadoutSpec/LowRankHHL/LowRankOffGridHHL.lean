/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

namespace Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

noncomputable def flagSuccessSet (D M : ℕ) : Finset (Fin M × (Bool × (Bool × Fin D))) :=
  Finset.univ.filter (fun p => p.2.2.1 = true)

noncomputable def lowRankAccuracy (d theta : ℝ) (k : ℕ) : ℝ :=
  min 1 (min (d*theta/2) ((1/2:ℝ)^k))

noncomputable def lowRankGrid (d theta : ℝ) (k : ℕ) : ℕ :=
  max 2 ⌈4096/(d^2*(lowRankAccuracy d theta k)^4)⌉₊

theorem lowRank_qpeKernel_zero (M : ℕ) (hM : 0 < M) (y : Fin M) :
    qpeKernel M 0 y = Ket (⟨0,hM⟩ : Fin M) y := by
  simpa using! (offgrid_phase_geometric_and_periodic M 0 y hM).2.2 (⟨0,hM⟩ : Fin M)

theorem lowRank_rotation_zero (d : ℝ) : uniformHHLRotation d 0 = (1 : Matrix Bool Bool ℂ) := by
  ext b c
  cases b <;> cases c <;> simp [uniformHHLRotation, uniformHHLGamma]

theorem lowRank_zero_forward {D M : ℕ} (hM : 0 < M) (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) (hi : eig i=0) :
    Run 1 (gridHHLQPEBlock (M := M) (continuousHHLOracle eig V))
      (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (V *ᵥ Ket i))) =
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (V *ᵥ Ket i)) := by
  rw [uniformHHLForwardReadout hM,
    qpeOutput_eigen M _ _ _ (continuousHHLOracle_mulVec_column eig V hV i)]
  simp only [hi]
  have hk : qpeKernel M 0 = Ket (⟨0,hM⟩ : Fin M) := funext (lowRank_qpeKernel_zero M hM)
  rw [hk]
  funext p
  rcases p with ⟨y,f,k⟩
  simp only [gridHHLWorkspaceState_apply, TensorState]
  ring

theorem lowRank_zero_flag {D M : ℕ} (hM : 0 < M) (d : ℝ) (v : QState (Fin D)) :
    uniformHHLFlag (D := D) (M := M) d *ᵥ
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) v) =
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) v) := by
  change ApplyGate _ _ = _
  rw [uniformHHLFlag_product]
  funext p
  rcases p with ⟨y,f,k⟩
  by_cases hy : y = (⟨0,hM⟩ : Fin M)
  · subst y
    simp [uniformHHLDecode, lowRank_rotation_zero, TensorState, Ket]
  · simp [TensorState, Ket, hy]

theorem uniform_hhl_exact_zero_mode : ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V : Operator D)
    (i : Fin D) (d : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → eig i = 0 →
  uniformHHLRun M hM (continuousHHLOracle eig V) d V i =
    uniformHHLSuccessEmbed M hM (0 : QState (Fin D)) +
    TensorState (Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (V *ᵥ Ket i))) ∧
  MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d V i) (flagSuccessSet D M) = 0
 := by
  intro D M hM eig V i d hV hd hi
  have hMp : 0 < M := by omega
  let U := continuousHHLOracle eig V
  let F := gridHHLBlockOp (D := D) (M := M) U
  let a := TensorState (Ket (⟨0,hMp⟩ : Fin M)) (TensorState (Ket false) (V *ᵥ Ket i))
  have hU := continuous_hhl_oracle_unitary eig V hV
  have hF := gridHHLBlockOp_unitary hMp U hU
  have hstar : Fᴴ*F=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hF
  have hfwd : F *ᵥ a = a := by
    simpa only [run_qpeBlock_eq] using! lowRank_zero_forward hMp eig V hV i hi
  have hback : Fᴴ *ᵥ a = a := by
    calc
      _ = Fᴴ *ᵥ (F *ᵥ a) := congrArg (fun x => Fᴴ *ᵥ x) hfwd.symm
      _ = a := by rw [Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  have hrun : uniformHHLRun M hM U d V i = phaseFlagEmbed M a := by
    rw [uniformHHLRun_eq M hM U hU d V i, run_append, run_append, run_gate, run_nil]
    simp only [ApplyGate]
    change phaseFlagEmbed M (Run 1 (gridHHLQPEBlockInv U)
      (uniformHHLFlag d *ᵥ (Run 1 (gridHHLQPEBlock U) a))) = phaseFlagEmbed M a
    rw [run_qpeBlock_eq, hfwd, lowRank_zero_flag hMp d, run_qpeBlockInv_eq]
    exact congrArg (phaseFlagEmbed M) hback
  have hout : uniformHHLRun M hM U d V i =
      TensorState (Ket (⟨0,hMp⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket false) (V *ᵥ Ket i))) := by
    rw [hrun]
    funext p
    rcases p with ⟨y,s,f,k⟩
    cases s <;> simp [a, phaseFlagEmbed, TensorState, Ket]
  refine ⟨?_, ?_⟩
  · have hz : uniformHHLSuccessEmbed M hM (0 : QState (Fin D)) = 0 := by
      funext p
      simp [uniformHHLSuccessEmbed, TensorState]
    rw [hz, zero_add]
    exact hout
  · rw [hout]
    unfold MeasureProb BornProb
    apply Finset.sum_eq_zero
    intro p hp
    have hf : p.2.2.1=true := (Finset.mem_filter.mp hp).2
    simp [TensorState, Ket, hf]

theorem lowRank_spectral_window_error (M : ℕ) (lam d eta : ℝ) (hM : 2 ≤ M)
    (hd : 0 < d) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (heig : lam=0 ∨ (d ≤ |lam| ∧ |lam| ≤ 1/4))
    (hbudget : 4096/(d^2*eta^4) ≤ (M:ℝ)) :
    (∑ y : Fin M, ‖qpeKernel M lam y‖^2 *
      ‖toEuclidean_fromVec (uniformHHLRotation d (uniformHHLDecode M y) *ᵥ Ket false -
        uniformHHLRotation d lam *ᵥ Ket false)‖^2) ≤ eta^2 := by
  rcases heig with rfl | hgap
  · have hMp : 0 < M := by omega
    have hz : (∑ y : Fin M, ‖qpeKernel M 0 y‖^2 *
        ‖toEuclidean_fromVec (uniformHHLRotation d (uniformHHLDecode M y) *ᵥ Ket false -
          uniformHHLRotation d 0 *ᵥ Ket false)‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [lowRank_qpeKernel_zero M hMp]
      by_cases h : y=(⟨0,hMp⟩ : Fin M)
      · subst y
        have hdec : uniformHHLDecode M (⟨0,hMp⟩ : Fin M) = 0 := by simp [uniformHHLDecode]
        rw [hdec, sub_self]
        simp [toEuclidean_fromVec]
      · simp [Ket, h]
    rw [hz]
    positivity
  · exact uniformHHL_spectral_window_error M lam d eta hM hd heta heta1 hgap.1 hgap.2 hbudget

theorem lowRank_spectral_error_bound {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (β : QState (Fin D)) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, eig i=0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1 / 4))
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
            (lowRank_spectral_window_error M (eig i) d η hM hd hη hη1 (heig i) hbudget) (sq_nonneg _)
      _ = η ^ 2 := by rw [← Finset.sum_mul, hβ, one_mul]
  change ‖toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
    (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 * δ p.1 i p.2.1)) p.2.2)‖ ≤ η
  nlinarith [norm_nonneg (toEuclidean_fromVec (fun p : Fin M × (Bool × Fin D) =>
    (V *ᵥ (fun i => β i * qpeKernel M (eig i) p.1 * δ p.1 i p.2.1)) p.2.2))]

theorem low_rank_uniform_hhl_full_workspace_error :
    ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
      (j : Fin D) (d η : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < η → η ≤ 1 →
      (∀ i, eig i=0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1 / 4)) →
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
  have hnorm := lowRank_spectral_error_bound hM eig V β d η hV hd hη hη1 heig hbudget hβ
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

theorem lowRank_gamma_reciprocal (d x : ℝ) (hd : 0 < d)
    (hx : x=0 ∨ d ≤ |x|) : uniformHHLGamma d x = (d/4)*x⁻¹ := by
  rcases hx with rfl | hx
  · simp [uniformHHLGamma]
  · rw [uniformHHLGamma_eq_reciprocal d x hd (by linarith)]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring

theorem lowRank_ideal_collapse {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, eig i=0 ∨ d ≤ |eig i|) :
    Collapse (uniformHHLIdeal M hM eig V d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)) =
      uniformHHLSuccessEmbed M hM ((d / 4 : ℂ) •
        (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j))) := by
  have hpinv := (singular_hermitian_pseudoinverse_and_least_squares _ eig V hV).1
  have hgamma : ∀ i, (uniformHHLGamma d (eig i) : ℂ) = (d / 4 : ℂ) * (eig i : ℂ)⁻¹ := by
    intro i
    rw [lowRank_gamma_reciprocal d (eig i) hd (heig i)]
    push_cast
    ring
  have hg : V * diagonal (fun i => (uniformHHLGamma d (eig i) : ℂ)) * Vᴴ =
      (d / 4 : ℂ) • matrixPseudoinverse (continuousHHLMatrix eig V) := by
    rw [hpinv]
    simp_rw [hgamma]
    change V * diagonal ((d / 4 : ℂ) • (fun i => (eig i : ℂ)⁻¹)) * Vᴴ = _
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  funext p
  obtain ⟨y, scratch, flag, k⟩ := p
  cases flag
  · simp [collapse_apply, uniformHHLSuccessEmbed, TensorState, Ket]
  · simp only [collapse_apply, Finset.mem_filter, Finset.mem_univ, and_true,
      if_true, uniformHHLIdeal, uniformHHLSuccessEmbed, TensorState,
      Pi.smul_apply, smul_eq_mul]
    rw [hg, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Ket, if_true]
    ring

theorem lowRank_ideal_postMeasure {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, eig i=0 ∨ d ≤ |eig i|) :
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
  rw [lowRank_ideal_collapse hM eig V B j d hV hd heig, hlinear] at he
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
    simp only [Algebra.cast, RCLike.algebraMap_eq_ofReal,
      RCLike.ofReal_eq_complex_ofReal]
    ring
  have heq := he.trans htarget.symm
  exact (WithLp.equiv 2 _).symm.injective heq

theorem lowRank_ideal_norm_lower {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (heig : ∀ i, eig i=0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1/4)) :
    d*leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j) ≤
      ‖toEuclidean_fromVec (Collapse (uniformHHLIdeal M hM eig V d B j) (flagSuccessSet D M))‖ := by
  have hA : ‖continuousHHLMatrix eig V‖ ≤ 1/4 := by
    refine (norm_conj_diagonal_le V hV (fun i => (eig i:ℂ))).trans ?_
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)).mpr
    intro i
    rcases heig i with hi | hi
    · simp [hi]
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using! hi.2
  let v := matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ (B *ᵥ Ket j)
  have ht : leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j) ≤
      (1/4)*‖toEuclidean_fromVec v‖ := by
    change ‖toEuclidean_fromVec ((continuousHHLMatrix eig V *
      matrixPseudoinverse (continuousHHLMatrix eig V)) *ᵥ (B *ᵥ Ket j))‖ ≤ _
    rw [← Matrix.mulVec_mulVec]
    exact (l2_norm_mulVec_fromVec_le _ v).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  unfold flagSuccessSet
  rw [lowRank_ideal_collapse hM eig V B j d hV hd
    (fun i => (heig i).imp id And.left), uniformHHLSuccessEmbed_norm]
  change _ ≤ ‖(d/4:ℂ) • toEuclidean_fromVec v‖
  have hc : (d/4:ℂ) = ((d/4:ℝ):ℂ) := by push_cast; rfl
  rw [norm_smul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < d/4)]
  nlinarith [mul_le_mul_of_nonneg_left ht hd.le]

theorem lowRank_output_from_error {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d E : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (hE : 0 ≤ E)
    (heig : ∀ i, eig i=0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1/4))
    (out : QState (Fin M × (Bool × (Bool × Fin D))))
    (herr : ‖toEuclidean_fromVec (out-uniformHHLIdeal M hM eig V d B j)‖ ≤ E)
    (hgap : E < d*leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)) :
    (d*leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)-E)^2 ≤
      MeasureProb out (flagSuccessSet D M) ∧ 0 < MeasureProb out (flagSuccessSet D M) ∧
    ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤
      2*E/(d*leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)) := by
  let ideal := uniformHHLIdeal M hM eig V d B j
  let S := flagSuccessSet D M
  let tau := leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)
  have hlower : d*tau ≤ ‖toEuclidean_fromVec (Collapse ideal S)‖ :=
    lowRank_ideal_norm_lower hM eig V B j d hV hd heig
  have hdt : 0 < d*tau := lt_of_le_of_lt hE hgap
  have hg : E < Real.sqrt (MeasureProb ideal S) := by
    rw [← norm_toEuclidean_collapse_eq_sqrt_measureProb]
    exact hgap.trans_le hlower
  have hp := postMeasure_error_of_gap ideal out S herr hg
  have hc := (norm_toEuclidean_collapse_sub_le ideal out S).trans herr
  have hn := norm_sub_norm_le (toEuclidean_fromVec (Collapse ideal S))
    (toEuclidean_fromVec (Collapse out S))
  change _ ≤ ‖toEuclidean_fromVec (Collapse ideal S-Collapse out S)‖ at hn
  rw [show toEuclidean_fromVec (Collapse ideal S-Collapse out S) =
    toEuclidean_fromVec (Collapse ideal S)-toEuclidean_fromVec (Collapse out S) from rfl,
    norm_sub_rev] at hn
  have hc' : ‖toEuclidean_fromVec (Collapse out S)-toEuclidean_fromVec (Collapse ideal S)‖ ≤ E := hc
  have ho : d*tau-E ≤ ‖toEuclidean_fromVec (Collapse out S)‖ := by linarith
  have hs : (d*tau-E)^2 ≤ ‖toEuclidean_fromVec (Collapse out S)‖^2 :=
    pow_le_pow_left₀ (by linarith) ho 2
  have hm : ‖toEuclidean_fromVec (Collapse out S)‖^2 = MeasureProb out S := by
    rw [norm_toEuclidean_fromVec_sq, sum_normSq_collapse]
  refine ⟨hm ▸ hs, hp.1, ?_⟩
  change ‖toEuclidean_fromVec (PostMeasure out S - uniformHHLSolutionTarget M hM eig V B j)‖ ≤ _
  rw [← lowRank_ideal_postMeasure hM eig V B j d hV hd (fun i => (heig i).imp id And.left)]
  exact hp.2.trans (div_le_div_of_nonneg_left (by positivity) hdt
    (by rwa [← norm_toEuclidean_collapse_eq_sqrt_measureProb]))

theorem low_rank_uniform_hhl_actual_ls_output : ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
    (j : Fin D) (d eta : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
  B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < eta → eta ≤ 1 →
  (∀ i, eig i = 0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1/4)) →
  4096/(d^2*eta^4) ≤ (M:ℝ) →
  let A := continuousHHLMatrix eig V
  let b := B *ᵥ Ket j
  let tau := leastSquaresOverlap A b
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  Collapse (uniformHHLIdeal M hM eig V d B j) (flagSuccessSet D M) =
    uniformHHLSuccessEmbed M hM ((d/4:ℝ) • (matrixPseudoinverse A *ᵥ b)) ∧
  (eta < d*tau →
    (d*tau-eta)^2 ≤ MeasureProb out (flagSuccessSet D M) ∧
    0 < MeasureProb out (flagSuccessSet D M) ∧
    ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤ 2*eta/(d*tau))
 := by
  intro D M hM eig V B j d eta hV hB hd heta heta1 heig hbudget
  refine ⟨?_, ?_⟩
  · have h := lowRank_ideal_collapse hM eig V B j d hV hd (fun i => (heig i).imp id And.left)
    have hc : (d/4:ℂ) = ((d/4:ℝ):ℂ) := by push_cast; rfl
    rw [hc] at h
    simpa only [flagSuccessSet, RCLike.real_smul_eq_coe_smul] using! h
  · intro hgap
    exact lowRank_output_from_error hM eig V B j d eta hV hd heta.le heig _
      (low_rank_uniform_hhl_full_workspace_error D M hM eig V B j d eta hV hB hd heta heta1 heig hbudget) hgap

theorem lowRank_run_formula {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (d : ℝ) (B : Operator D) (j : Fin D) :
    uniformHHLRun M hM (continuousHHLOracle eig V) d B j =
      phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) (continuousHHLOracle eig V))ᴴ *ᵥ
        (uniformHHLFlag d *ᵥ (gridHHLBlockOp (D := D) (M := M) (continuousHHLOracle eig V) *ᵥ
          TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (B *ᵥ Ket j))))) := by
  rw [uniformHHLRun_eq M hM _ (continuous_hhl_oracle_unitary eig V hV),
    run_append, run_append, run_gate, run_nil, run_qpeBlock_eq, run_qpeBlockInv_eq]
  rfl

theorem lowRank_actual_spectral {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (d : ℝ) (j : Fin D) :
    uniformHHLRun M hM (continuousHHLOracle eig V) d B j =
      ∑ i : Fin D, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        uniformHHLRun M hM (continuousHHLOracle eig V) d V i := by
  let beta := Vᴴ *ᵥ (B *ᵥ Ket j)
  have hi : TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (B *ᵥ Ket j)) =
      ∑ i : Fin D, beta i • TensorState (Ket (⟨0,by omega⟩ : Fin M))
        (TensorState (Ket false) (V *ᵥ Ket i)) := by
    rw [gridHHL_eigen_expansion (M := M) V hV (B *ᵥ Ket j)]
    funext p
    simp only [TensorState, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i h
    ring
  rw [lowRank_run_formula hM eig V hV d B j, hi]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hp : ∀ (vs : Fin D → QState (Fin M × (Bool × Fin D))),
      phaseFlagEmbed M (∑ i, beta i • vs i) = ∑ i, beta i • phaseFlagEmbed M (vs i) := by
    intro vs
    funext p
    rcases p with ⟨y,s,r⟩
    cases s <;> simp [phaseFlagEmbed, Pi.smul_apply]
  rw [hp]
  apply Finset.sum_congr rfl
  intro i h
  rw [lowRank_run_formula hM eig V hV d V i]

theorem lowRank_zero_overlap_coeff {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b : QState (Fin D))
    (hzero : leastSquaresOverlap (continuousHHLMatrix eig V) b = 0) :
    ∀ i : Fin D, eig i ≠ 0 → (Vᴴ *ᵥ b) i = 0 := by
  have hp := (singular_hermitian_pseudoinverse_and_least_squares D eig V hV).2.1
  have hz : spectralSupport eig V *ᵥ b = 0 := by
    have hn : ‖stateVector (spectralSupport eig V *ᵥ b)‖ = 0 := by
      simpa only [leastSquaresOverlap, hp] using! hzero
    exact (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp hn)
  have hv : Vᴴ*V=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hV
  have he : Vᴴ *ᵥ (spectralSupport eig V *ᵥ b) =
      Matrix.diagonal (fun i => if eig i=0 then (0:ℂ) else 1) *ᵥ (Vᴴ *ᵥ b) := by
    have hmat : Vᴴ*spectralSupport eig V =
        Matrix.diagonal (fun i => if eig i=0 then (0:ℂ) else 1)*Vᴴ := by
      unfold spectralSupport
      have ha : Vᴴ*((V*Matrix.diagonal (fun i => if eig i=0 then (0:ℂ) else 1))*Vᴴ) =
          ((Vᴴ*V)*Matrix.diagonal (fun i => if eig i=0 then (0:ℂ) else 1))*Vᴴ := by noncomm_ring
      rw [ha, hv, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec]
  rw [hz, Matrix.mulVec_zero] at he
  intro i hi
  have hh := congrFun he i
  simpa only [Matrix.mulVec_diagonal, if_neg hi, one_mul, Pi.zero_apply] using! hh.symm

theorem lowRank_zero_overlap_mass {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (hzero : leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)=0) :
    MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d B j) (flagSuccessSet D M) = 0 := by
  unfold MeasureProb BornProb
  apply Finset.sum_eq_zero
  intro p hp
  have hf : p.2.2.1=true := (Finset.mem_filter.mp hp).2
  have hout : uniformHHLRun M hM (continuousHHLOracle eig V) d B j p = 0 := by
    rw [lowRank_actual_spectral hM eig V B hV d j]
    simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : eig i=0
    · rw [(uniform_hhl_exact_zero_mode D M hM eig V i d hV hd hz).1]
      simp [uniformHHLSuccessEmbed, TensorState, Ket, hf]
    · rw [lowRank_zero_overlap_coeff eig V hV (B *ᵥ Ket j) hzero i hz, zero_mul]
  rw [hout]
  simp

theorem lowRank_trial_false {I : Type*} [Fintype I] [DecidableEq I]
    (out : QState I) (hn : Normalized out) (S : Finset I) (hm : MeasureProb out S=0) :
    uniformHHLFlagTrialLaw out hn S = PMF.pure false := by
  have ht : uniformHHLFlagTrialLaw out hn S true = 0 := by
    rw [uniformHHLFlagTrialLaw_true, hm]; simp
  have hf := uniformHHL_trial_total (uniformHHLFlagTrialLaw out hn S)
  rw [ht, zero_add] at hf
  ext b
  cases b <;> simp [ht, hf, PMF.pure_apply]

theorem lowRank_firstSuccess_false (R : ℕ) :
    uniformHHLFirstSuccess (PMF.pure false) R = PMF.pure (false,R) := by
  induction R with
  | zero => rfl
  | succ R ih => simp [uniformHHLFirstSuccess, ih, PMF.pure_map]

theorem low_rank_uniform_hhl_zero_overlap_timeout : ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
    (j : Fin D) (d : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d),
  leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j) = 0 →
  MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d B j) (flagSuccessSet D M) = 0 ∧
  (∀ R : ℕ, uniformHHLRetryLaw M hM eig V d B j hV hB hd R =
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (R*(2*(M-1))) (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (false,R,R*(4*(M-1)+6),R)))
 := by
  intro D M hM eig V B j d hV hB hd hzero
  have hm := lowRank_zero_overlap_mass hM eig V B j d hV hd hzero
  refine ⟨hm, ?_⟩
  intro R
  unfold uniformHHLRetryLaw
  (try dsimp only)
  have hm' : MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1=true)) = 0 := hm
  rw [lowRank_trial_false _ _ _ hm', lowRank_firstSuccess_false]
  simp [PMF.pure_map, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem low_rank_uniform_hhl_actual_access_noise : ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B W : Operator D)
    (j : Fin D) (d eta delta : ℝ), V ∈ Matrix.unitaryGroup (Fin D) ℂ →
  B ∈ Matrix.unitaryGroup (Fin D) ℂ → W ∈ Matrix.unitaryGroup (Fin D) ℂ →
  0 < d → 0 < eta → eta ≤ 1 → 0 ≤ delta →
  (∀ i, eig i = 0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1/4)) →
  4096/(d^2*eta^4) ≤ (M:ℝ) → ‖W-continuousHHLOracle eig V‖ ≤ delta →
  let E := eta+2*(M-1)*delta
  let tau := leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)
  let out := uniformHHLRun M hM W d B j
  ‖toEuclidean_fromVec (out-uniformHHLIdeal M hM eig V d B j)‖ ≤ E ∧
  (E < d*tau → (d*tau-E)^2 ≤ MeasureProb out (flagSuccessSet D M) ∧
    ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤ 2*E/(d*tau))
 := by
  intro D M hM eig V B W j d eta delta hV hB hW hd heta heta1 hdelta heig hbudget hdist
  have hcast : ((M-1:ℕ):ℝ) = (M:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  have hn := uniformHHLRun_oracle_noise M hM (continuousHHLOracle eig V) W B j d
    (continuous_hhl_oracle_unitary eig V hV) hW hB hd
  have ha := low_rank_uniform_hhl_full_workspace_error D M hM eig V B j d eta
    hV hB hd heta heta1 heig hbudget
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (toEuclidean_fromVec (uniformHHLRun M hM W d B j))
    (toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j))
    (toEuclidean_fromVec (uniformHHLIdeal M hM eig V d B j))
  have he : ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j -
      uniformHHLIdeal M hM eig V d B j)‖ ≤ eta+2*(M-1)*delta := by
    have hc := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2*((M-1:ℕ):ℝ) by positivity)
    change ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j - uniformHHLIdeal M hM eig V d B j)‖ ≤
      ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j - uniformHHLRun M hM (continuousHHLOracle eig V) d B j)‖ +
      ‖toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j - uniformHHLIdeal M hM eig V d B j)‖ at ht
    rw [hcast] at hn hc
    exact ht.trans (by linarith)
  refine ⟨he, ?_⟩
  intro hgap
  have hE : 0 ≤ eta+2*(M-1)*delta := by rw [← hcast]; positivity
  have ho := lowRank_output_from_error hM eig V B j d (eta+2*(M-1)*delta) hV hd hE
    heig _ he hgap
  exact ⟨ho.1, ho.2.2⟩

theorem lowRank_parameter_budget (d theta : ℝ) (k : ℕ) (hd : 0 < d) (htheta : 0 < theta) :
    0 < lowRankAccuracy d theta k ∧ lowRankAccuracy d theta k ≤ 1 ∧
      lowRankAccuracy d theta k ≤ d*theta/2 ∧ 2 ≤ lowRankGrid d theta k ∧
      4096/(d^2*(lowRankAccuracy d theta k)^4) ≤ (lowRankGrid d theta k : ℝ) := by
  have hp : 0 < lowRankAccuracy d theta k := by
    unfold lowRankAccuracy
    positivity
  refine ⟨hp, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), le_max_left _ _, ?_⟩
  have hn : ⌈4096/(d^2*(lowRankAccuracy d theta k)^4)⌉₊ ≤ lowRankGrid d theta k := le_max_right _ _
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

theorem low_rank_uniform_hhl_computed_budget_and_retry : ∀ (D : ℕ) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
    (d theta : ℝ) (k : ℕ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d),
  0 < theta → theta ≤ leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j) →
  (∀ i, eig i = 0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1/4)) →
  0 < lowRankAccuracy d theta k ∧ lowRankAccuracy d theta k ≤ 1 ∧
  2 ≤ lowRankGrid d theta k ∧
  (∀ hM : 2 ≤ lowRankGrid d theta k,
    let M := lowRankGrid d theta k
    let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
    d^2*theta^2/4 ≤ MeasureProb out (flagSuccessSet D M) ∧
    ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤ 2*lowRankAccuracy d theta k/(d*theta) ∧
    (∀ R : ℕ, let law := uniformHHLRetryLaw M hM eig V d B j hV hB hd R
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event law (fun z => z.1.1=true)).toReal ≥ 1-(1-d^2*theta^2/4)^R ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost law ≤ ENNReal.ofReal (8*(M-1)/(d^2*theta^2)) ∧
      (∀ z ∈ law.support, z.1.2.1 ≤ R ∧ z.1.2.2.1 = z.1.2.1*(4*(M-1)+6) ∧
        z.1.2.2.2 = z.1.2.1 ∧ z.2 = z.1.2.1*(2*(M-1)))))
 := by
  intro D eig V B j d theta k hV hB hd htheta hover heig
  have hpar := lowRank_parameter_budget d theta k hd htheta
  refine ⟨hpar.1, hpar.2.1, hpar.2.2.2.1, ?_⟩
  intro hM
  let M := lowRankGrid d theta k
  let eta := lowRankAccuracy d theta k
  let tau := leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Ket j)
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  let S := flagSuccessSet D M
  have heta : 0 < eta := hpar.1
  have hcast : ((M-1:ℕ):ℝ) = (M:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  have hgap : eta < d*tau := by
    have ha : eta ≤ d*theta/2 := hpar.2.2.1
    have ht : d*theta ≤ d*tau := mul_le_mul_of_nonneg_left hover hd.le
    have hpos : 0 < d*theta := mul_pos hd htheta
    linarith
  have hout := (low_rank_uniform_hhl_actual_ls_output D M hM eig V B j d eta hV hB hd
    hpar.1 hpar.2.1 heig hpar.2.2.2.2).2 hgap
  have hmass : d^2*theta^2/4 ≤ MeasureProb out S := by
    have ha : eta ≤ d*theta/2 := hpar.2.2.1
    have ht : d*theta ≤ d*tau := mul_le_mul_of_nonneg_left hover hd.le
    have hs : d^2*theta^2/4 ≤ (d*tau-eta)^2 := by
      nlinarith [sq_nonneg (d*tau-eta-d*theta/2)]
    exact hs.trans hout.1
  have herr : ‖toEuclidean_fromVec (PostMeasure out S - uniformHHLSolutionTarget M hM eig V B j)‖ ≤
      2*eta/(d*theta) :=
    hout.2.2.trans (div_le_div_of_nonneg_left (by positivity) (mul_pos hd htheta)
      (mul_le_mul_of_nonneg_left hover hd.le))
  refine ⟨hmass, herr, ?_⟩
  intro R
  have hn : Normalized out := (normalized_iff_stateVector_norm _).mpr
    (uniformHHLRun_norm M hM _ B j d (continuous_hhl_oracle_unitary eig V hV) hB hd)
  have hp1 : MeasureProb out S ≤ 1 := measureProb_le_one hn S
  have hpow : (1-MeasureProb out S)^R ≤ (1-d^2*theta^2/4)^R :=
    pow_le_pow_left₀ (by linarith) (by linarith) R
  have hsuccess := uniformHHLRetryLaw_success M hM eig V d B j hV hB hd R
  have hexp := uniformHHLRetryLaw_expected_le M hM eig V d B j hV hB hd R hout.2.1
  have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (uniformHHLRetryLaw M hM eig V d B j hV hB hd R) ≤
      ENNReal.ofReal (8*(M-1)/(d^2*theta^2)) := by
    calc
      _ ≤ (2*(M-1):ℕ)/ENNReal.ofReal (MeasureProb out S) := hexp
      _ ≤ (2*(M-1):ℕ)/ENNReal.ofReal (d^2*theta^2/4) :=
        ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hmass) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_div_of_pos (by positivity : 0 < d^2*theta^2/4)]
        congr 1
        push_cast
        rw [hcast]
        field_simp
        ring
  refine ⟨?_, he, uniformHHLRetryLaw_ledger M hM eig V d B j hV hB hd R⟩
  rw [hsuccess]
  change 1-(1-d^2*theta^2/4)^R ≤ 1-(1-MeasureProb out S)^R
  linarith

end Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
