/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhlDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.SpecRestrictedSubgoalHarr
import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.CostRestrictedSubgoalHarr
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem qls_normVec_sqrt {I : Type} [Fintype I] [DecidableEq I] (v : QState I) :
    ‖toEuclidean_fromVec v‖ = (∑ p, ‖v p‖ ^ 2).sqrt := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]

private theorem qls_decode_bounded (M : ℕ) (z : Fin M) (hM : 2 ≤ M) :
    -1/2 ≤ sinEnvelopeDecode M z ∧ sinEnvelopeDecode M z ≤ 1/2 := by
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hz0 : (0:ℝ) ≤ z.val := by positivity
  have hz1 : (z.val:ℝ) < M := by exact_mod_cast z.isLt
  unfold sinEnvelopeDecode
  split_ifs with h
  · have hh : 2*(z.val:ℝ) ≤ M := by exact_mod_cast h
    constructor
    · have hz := div_nonneg hz0 hm0.le; linarith only [hz]
    · apply (div_le_iff₀ hm0).mpr; linarith only [hh]
  · have hh : (M:ℝ) < 2*(z.val:ℝ) := by exact_mod_cast (show M < 2*z.val by omega)
    have hzlo : (1/2:ℝ) ≤ (z.val:ℝ)/(M:ℝ) := (le_div_iff₀ hm0).mpr (by linarith only [hh])
    have hzup : (z.val:ℝ)/(M:ℝ) < 1 := (div_lt_one hm0).mpr hz1
    constructor <;> linarith only [hzlo,hzup]

private theorem qls_phase_dist_eq_abs_of_le_half {x y : ℝ} (h : |x - y| ≤ 1/2) :
    phaseDistance x y = |x - y| := by
  have hlo : (0:ℝ) ≤ x - y + 1/2 := by
    have := abs_le.mp h |>.1
    linarith
  rcases lt_or_ge (x - y + 1/2) 1 with hlt | hge
  · have hf : ⌊x - y + 1/2⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    unfold phaseDistance
    rw [hf]
    push_cast
    simp
  · have heq : x - y + 1/2 = 1 := le_antisymm (by
        have := abs_le.mp h |>.2
        linarith) hge
    have hf : ⌊x - y + 1/2⌋ = 1 := by rw [heq]; norm_num
    have hx : x - y = 1/2 := by linarith
    unfold phaseDistance
    rw [hf]
    push_cast
    rw [hx]
    norm_num

private theorem qls_phase_dist_sub_one_right (x y : ℝ) :
    phaseDistance x (y-1) = phaseDistance x y := by
  unfold phaseDistance
  have he : x-(y-1)+1/2 = (x-y+1/2)+(1:ℤ) := by push_cast; ring
  rw [he,Int.floor_add_intCast]
  push_cast
  congr 1
  ring

private theorem qls_decode_distance (M : ℕ) (φ : ℝ) (z : Fin M) :
    phaseDistance φ (sinEnvelopeDecode M z) = phaseDistance φ ((z.val:ℝ)/(M:ℝ)) := by
  unfold sinEnvelopeDecode
  split_ifs
  · rfl
  · exact qls_phase_dist_sub_one_right _ _

private theorem qls_signed_phase_distance (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/4)
    (hy : -1/2 ≤ y) (hy' : y ≤ 1/2) :
    |x-y| ≤ 3*phaseDistance x y := by
  let n : ℤ := ⌊x-y+1/2⌋
  have hn₀ : 0 ≤ n := Int.floor_nonneg.mpr (by linarith only [hx,hy'])
  have hn₁ : n < 2 := Int.floor_lt.mpr (by norm_num; linarith only [hx',hy])
  have hh := Int.floor_le (x-y+1/2)
  have he : n = 0 ∨ n = 1 := by omega
  unfold phaseDistance
  change |x-y| ≤ 3*|x-y-(n:ℝ)|
  rcases he with h|h
  · rw [h]; norm_num only [Int.cast_zero,sub_zero]
    nlinarith only [abs_nonneg (x-y)]
  · have hlo : 1/2 ≤ x-y := by dsimp [n] at h; rw [h] at hh; norm_num at hh; linarith only [hh]
    rw [h]; norm_num only [Int.cast_one]
    rw [abs_of_nonneg (by linarith only [hlo]),abs_of_nonpos (by linarith only [hx',hy])]
    linarith only [hx',hy]

private theorem qls_beta_total {D : ℕ} (V B : Operator D) (ψ : QState (Fin D))
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 = ∑ i, ‖ψ i‖^2 := by
  have hVadj : Vᴴ ∈ Matrix.unitaryGroup (Fin D) ℂ := mem_unitaryGroup_adjoint hV
  have hv := sum_normSq_mulVec_of_mem_unitaryGroup hVadj (B *ᵥ ψ)
  have hb := sum_normSq_mulVec_of_mem_unitaryGroup hB ψ
  simpa only [Complex.normSq_eq_norm_sq] using! hv.trans hb

private theorem qls_flag_mass_low (d x : ℝ) (hd : 0 < d) (hx : x ≤ 2*d) :
    sinEnvelopeFlagMass d x = 1/4 := by
  by_cases he : x = 2*d
  · rw [he]
    unfold sinEnvelopeFlagMass
    rw [(sin_envelope_filter_branch_values d hd).1,
      (sin_envelope_filter_branch_values d hd).2.1]
    norm_num
  · have hw : ¬ 2*d ≤ x := by intro h; exact he (le_antisymm hx h)
    unfold sinEnvelopeFlagMass sinEnvelopeFilterF sinEnvelopeFilterG
    simp only [if_neg hw]
    by_cases hl : d ≤ x
    · have hsin := Real.sin_sq_add_cos_sq (Real.pi/2*(x-d)/d)
      simp only [if_pos hl]
      nlinarith [hsin]
    · simp only [if_neg hl]
      norm_num

private theorem qls_filter_const_le (d x : ℝ) (hd : 0 < d) (hx : x ≤ d) :
    sinEnvelopeFilterF d x = 0 ∧ sinEnvelopeFilterG d x = 1/2 := by
  have h2 : ¬ 2*d ≤ x := by intro h; linarith
  unfold sinEnvelopeFilterF sinEnvelopeFilterG
  simp only [if_neg h2]
  by_cases hl : d ≤ x
  · have he : x = d := le_antisymm hx hl
    rw [he]
    have hz : (Real.pi/2*(d-d)/d) = 0 := by
      rw [sub_self]; simp
    simp only [if_pos (le_refl d)]
    rw [hz, Real.sin_zero, Real.cos_zero]
    norm_num
  · simp [if_neg hl]

private theorem qls_flag_mass_lower (d θ : ℝ) (hd : 0 < d) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/4) :
    min (1/4) (16*d^2) ≤ sinEnvelopeFlagMass d θ := by
  rcases le_or_gt θ (2*d) with hlow | hhigh
  · rw [qls_flag_mass_low d θ hd hlow]
    exact min_le_left _ _
  · have hwell := (sin_envelope_filter_branch_values d hd).2.2.2.2.2.2.2.2 θ (le_of_lt hhigh)
    unfold sinEnvelopeFlagMass
    rw [hwell.1, hwell.2]
    have hpos : 0 < θ := by nlinarith [hhigh, hd]
    have h1 : (d/(1/4:ℝ)) ≤ d/θ :=
      div_le_div_of_nonneg_left hd.le hpos hθ'
    have h2 : (d/(1/4:ℝ)) = 4*d := by ring_nf
    have h4 : (4*d)^2 ≤ (d/θ)^2 := by
      rw [h2] at h1
      exact pow_le_pow_left₀ (by positivity) h1 2
    have h5 : (4*d)^2 = 16*d^2 := by ring
    rw [h5] at h4
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero]
    exact le_trans (min_le_right _ _) h4

private theorem qls_joint_filter_error (M : ℕ) (hM : 2 ≤ M) (φ d : ℝ) (hd : 0 < d)
    (hφ : 0 ≤ φ) (hφ' : φ ≤ 1/4) :
    (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
      (d * (M : ℝ))^2 ≤ 2205 * sinEnvelopeFlagMass d φ := by
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsecond := sin_envelope_kernel_second_moment M φ hM
  have hconst : 4*Real.pi^2+40*Real.pi^4/3 ≤ 196*Real.pi^2 := by
    have hp : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2,Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg Real.pi)
    nlinarith only [hh,sq_nonneg Real.pi]
  have hsumR : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) ≤ 49/(M:ℝ)^2 := by
    have heq : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(2*Real.pi*(M:ℝ)*
        (phaseDistance φ ((z.val:ℝ)/(M:ℝ))))^2) =
        (4*Real.pi^2*(M:ℝ)^2)*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*
          (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    change (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(2*Real.pi*(M:ℝ)*
      (phaseDistance φ ((z.val:ℝ)/(M:ℝ))))^2) ≤ _ at hsecond
    rw [heq] at hsecond
    have hh := hsecond.trans hconst
    have hh' : (M:ℝ)^2*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*
        (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) ≤ 49 := by
      nlinarith only [hh,Real.pi_pos,sq_pos_of_pos Real.pi_pos]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hh']
  have hoff : ∀ z : Fin M, (φ - sinEnvelopeDecode M z)^2 ≤
      9 * (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 := by
    intro z
    have hc := qls_signed_phase_distance φ (sinEnvelopeDecode M z) hφ hφ'
      (qls_decode_bounded M z hM).1 (qls_decode_bounded M z hM).2
    rw [qls_decode_distance] at hc
    have h3pos : (0:ℝ) ≤ 3 * phaseDistance φ ((z.val:ℝ)/(M:ℝ)) := by
      unfold phaseDistance
      positivity
    have hsq := (sq_le_sq₀ (abs_nonneg (φ - sinEnvelopeDecode M z)) h3pos).mpr hc
    have habs : (φ - sinEnvelopeDecode M z)^2 = |φ - sinEnvelopeDecode M z|^2 := (sq_abs _).symm
    rw [← habs] at hsq
    have h3 : (3 * phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 =
        9 * (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 := by ring
    rw [h3] at hsq
    exact hsq
  have hper : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
        (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) ≤
      ‖sinEnvelopeKernel M φ z‖^2 *
        (2*Real.pi^2*(1/(2*d))^2 * (φ - sinEnvelopeDecode M z)^2 *
          sinEnvelopeFlagMass d φ) := by
    intro z
    have hst := sin_envelope_filter_stability d φ (sinEnvelopeDecode M z) hd hφ hφ'
      (qls_decode_bounded M z hM).1 (qls_decode_bounded M z hM).2
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [show (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 =
        (sinEnvelopeFilterF d φ - sinEnvelopeFilterF d (sinEnvelopeDecode M z))^2 from by ring,
      show (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2 =
        (sinEnvelopeFilterG d φ - sinEnvelopeFilterG d (sinEnvelopeDecode M z))^2 from by ring]
    simpa only [sinEnvelopeFlagMass] using! hst
  have hsum2 : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
        (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
      2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) := by
    calc (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
        ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (2*Real.pi^2*(1/(2*d))^2 * (φ - sinEnvelopeDecode M z)^2 *
            sinEnvelopeFlagMass d φ) :=
          Finset.sum_le_sum (fun z _ => hper z)
      _ ≤ ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (2*Real.pi^2*(1/(2*d))^2 * (9 * (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) *
            sinEnvelopeFlagMass d φ) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hnn : (0:ℝ) ≤ 2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFlagMass d φ := by
            unfold sinEnvelopeFlagMass; positivity
          nlinarith [hoff z]
      _ = 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
      _ ≤ 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) := by
          have hnn : (0:ℝ) ≤ 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ := by
            unfold sinEnvelopeFlagMass; positivity
          exact mul_le_mul_of_nonneg_left hsumR hnn
  have hcle : 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) *
      (d*(M:ℝ))^2 ≤ 2205 * sinEnvelopeFlagMass d φ := by
    have hpi : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
    have hmassnn : 0 ≤ sinEnvelopeFlagMass d φ := by
      unfold sinEnvelopeFlagMass; positivity
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hd
    have hmne : (M:ℝ) ≠ 0 := ne_of_gt hm0
    have halg : (1/(2*d))^2 * (d*(M:ℝ))^2 = (M:ℝ)^2/4 := by
      field_simp
      ring
    have h : 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) *
        (d*(M:ℝ))^2 = (441*Real.pi^2/2) * sinEnvelopeFlagMass d φ := by
      have hstep : 2*Real.pi^2*(1/(2*d))^2 * 9 * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) *
          (d*(M:ℝ))^2 =
          2*Real.pi^2 * 9 * ((1/(2*d))^2 * (d*(M:ℝ))^2) * sinEnvelopeFlagMass d φ * (49/(M:ℝ)^2) := by
        ring
      rw [hstep, halg]
      field_simp
      ring
    rw [h]
    have hpi2 : 441*Real.pi^2/2 ≤ 2205 := by nlinarith [hpi]
    nlinarith [hmassnn, hpi2]
  exact (mul_le_mul_of_nonneg_right hsum2 (sq_nonneg _)).trans hcle

private theorem qls_four_factor {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (w : α → ℝ) (v : β → ℝ) (c : γ → ℝ) (g : γ → δ → ℝ) :
    (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * (c s * g s k)) =
      (∑ a, w a) * (∑ b, v b) * (∑ s, ∑ k, c s * g s k) := by
  have step1 : (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * (c s * g s k))
      = ∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * (c s * ∑ k : δ, g s k) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro s _
    have h1 : (∑ k : δ, w a * v b * (c s * g s k)) = ∑ k : δ, (w a * v b * c s) * g s k := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    have h2 : (∑ k : δ, (w a * v b * c s) * g s k) = (w a * v b * c s) * ∑ k : δ, g s k :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
    ring
  rw [step1]
  have step2 : (∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * (c s * ∑ k : δ, g s k))
      = ∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.mul_sum _ _ _).symm
  rw [step2]
  have step3 : (∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k))
      = ∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) := by
    apply Finset.sum_congr rfl
    intro a _
    have h1 : (∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k))
        = ∑ b : β, w a * (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    have h2 : (∑ b : β, w a * (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)))
        = w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
  rw [step3]
  have step4 : (∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)))
      = (∑ a : α, w a) * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) :=
    (Finset.sum_mul _ _ _).symm
  rw [step4]
  have step5 : (∑ b : β, v b * ∑ s : γ, (c s * ∑ k : δ, g s k))
      = (∑ b : β, v b) * ∑ s : γ, (c s * ∑ k : δ, g s k) :=
    (Finset.sum_mul _ _ _).symm
  rw [step5]
  have step6 : (∑ s : γ, (c s * ∑ k : δ, g s k)) = ∑ s : γ, ∑ k : δ, c s * g s k :=
    Finset.sum_congr rfl fun s _ => Finset.mul_sum _ _ _
  rw [step6]
  ring

private theorem qls_ideal_joint_mass {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    MeasureProb (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M) =
      sinEnvelopeIdealMass M hM eig V B j d := by
  classical
  have hite {c : Prop} [Decidable c] (a : ℝ) :
      (if c then a else (0:ℝ)) = (if c then (1:ℝ) else 0) * a := by
    by_cases hc : c <;> simp [hc]
  have hpoint (z : Fin M) (b : Bool) (s : Fin 3) (k : Fin D) :
      ‖sinEnvelopeHHLIdeal M hM eig V d B j (z, (b, (s, k)))‖ ^ 2 =
        (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
          ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 := by
    cases b with
    | true =>
      have hk : Ket false true = (0:ℂ) := by simp [Qatlib.Foundations.PureStateMath.Ket]
      simp [sinEnvelopeHHLIdeal, TensorState, hk, norm_mul, mul_pow,
        zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    | false =>
      have hk : Ket false false = (1:ℂ) := by simp [Qatlib.Foundations.PureStateMath.Ket]
      simp only [sinEnvelopeHHLIdeal, TensorState, hk, mul_one]
      by_cases hz : z = (⟨0, by omega⟩ : Fin M)
      · have hz' : Ket (⟨0, by omega⟩ : Fin M) z = (1:ℂ) := by simp [Qatlib.Foundations.PureStateMath.Ket, hz]
        rw [hz', if_pos hz]
        simp [one_mul]
      · have hz' : Ket (⟨0, by omega⟩ : Fin M) z = (0:ℂ) := by simp [Qatlib.Foundations.PureStateMath.Ket, hz]
        rw [hz', if_neg hz]
        simp [norm_mul, mul_pow, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  have hconv (p : Fin M × (Bool × (Fin 3 × Fin D))) :
      (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then
          ((if p.1 = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if p.2.1 then (0:ℝ) else 1) *
            ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.2.2.1) * Vᴴ) *ᵥ
                (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2.2.2‖ ^ 2) else (0:ℝ)) =
      (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) *
        (if p.1 = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if p.2.1 then (0:ℝ) else 1) *
          ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.2.2.1) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2.2.2‖ ^ 2 := by
    by_cases hc : p.2.2.1 = 1 ∨ p.2.2.1 = 2 <;> simp [hc]
  have hfactor : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
      (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) *
        (if p.1 = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if p.2.1 then (0:ℝ) else 1) *
          ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.2.2.1) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2.2.2‖ ^ 2) =
      ∑ s : Fin 3, ∑ k : Fin D,
        (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 := by
    have hz : ∑ z : Fin M, (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']
      simp
    have hb : ∑ b : Bool, (if b then (0:ℝ) else 1) = 1 := by
      rw [Fintype.sum_bool]; norm_num
    have hexp : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) *
          (if p.1 = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if p.2.1 then (0:ℝ) else 1) *
            ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.2.2.1) * Vᴴ) *ᵥ
                (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2.2.2‖ ^ 2) =
        ∑ z : Fin M, ∑ b : Bool, ∑ s : Fin 3, ∑ k : Fin D,
          (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
            (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
              ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
                  (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 := by
      have e1 : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
          (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) *
            (if p.1 = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if p.2.1 then (0:ℝ) else 1) *
              ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.2.2.1) * Vᴴ) *ᵥ
                  (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2.2.2‖ ^ 2) =
          ∑ z : Fin M, ∑ q : Bool × (Fin 3 × Fin D),
            (if q.2.1 = 1 ∨ q.2.1 = 2 then (1:ℝ) else 0) *
              (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if q.1 then (0:ℝ) else 1) *
                ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) q.2.1) * Vᴴ) *ᵥ
                    (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) q.2.2‖ ^ 2 :=
        Fintype.sum_prod_type _
      rw [e1]
      apply Finset.sum_congr rfl
      intro z _
      have e2 : (∑ q : Bool × (Fin 3 × Fin D),
          (if q.2.1 = 1 ∨ q.2.1 = 2 then (1:ℝ) else 0) *
            (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if q.1 then (0:ℝ) else 1) *
              ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) q.2.1) * Vᴴ) *ᵥ
                  (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) q.2.2‖ ^ 2) =
          ∑ b : Bool, ∑ r : Fin 3 × Fin D,
            (if r.1 = 1 ∨ r.1 = 2 then (1:ℝ) else 0) *
              (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
                ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) r.1) * Vᴴ) *ᵥ
                    (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) r.2‖ ^ 2 :=
        Fintype.sum_prod_type _
      rw [e2]
      apply Finset.sum_congr rfl
      intro b _
      have e3 : (∑ r : Fin 3 × Fin D,
          (if r.1 = 1 ∨ r.1 = 2 then (1:ℝ) else 0) *
            (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
              ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) r.1) * Vᴴ) *ᵥ
                  (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) r.2‖ ^ 2) =
          ∑ s : Fin 3, ∑ k : Fin D,
            (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
              (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
                ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
                    (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 :=
        Fintype.sum_prod_type _
      rw [e3]
    rw [hexp]
    have hnorm : ∀ (z : Fin M) (b : Bool) (s : Fin 3) (k : Fin D),
        (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
            ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
                (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 =
        (if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0) * (if b then (0:ℝ) else 1) *
          ((if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
            ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
                (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2) := by
      intros; ring
    simp only [hnorm]
    have hfour := qls_four_factor
      (fun z : Fin M => if z = (⟨0, by omega⟩ : Fin M) then (1:ℝ) else 0)
      (fun b : Bool => if b then (0:ℝ) else 1)
      (fun s : Fin 3 => if s = 1 ∨ s = 2 then (1:ℝ) else 0)
      (fun s : Fin 3 => fun k : Fin D =>
        ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2)
    rw [hfour, hz, hb, one_mul, one_mul]
  have hsum : MeasureProb (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M) =
      ∑ s : Fin 3, ∑ k : Fin D,
        (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 := by
    unfold MeasureProb BornProb sinEnvelopeJointSet
    rw [Finset.sum_filter]
    simp only [hpoint, hconv]
    exact hfactor
  rw [hsum]
  have hVid : ∀ s : Fin 3,
      (∑ k : Fin D, ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
        (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2) =
      ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * ‖sinEnvelopeHVector d (eig i) s‖ ^ 2 := by
    intro s
    have hns : (∑ i : Fin D, ‖(V *ᵥ (Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) *ᵥ
        (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)))) i‖ ^ 2) =
        ∑ i : Fin D, ‖(Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) *ᵥ
            (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j))) i‖ ^ 2 := by
      simpa only [Complex.normSq_eq_norm_sq] using!
        sum_normSq_mulVec_of_mem_unitaryGroup hV
          (Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) *ᵥ (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)))
    simp only [← Matrix.mulVec_mulVec]
    rw [hns]
    simp only [Matrix.mulVec_diagonal, norm_mul, mul_pow]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmass : sinEnvelopeIdealMass M hM eig V B j d =
      ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i) := rfl
  have hkey : (∑ s : Fin 3, ∑ k : Fin D, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
        ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2) =
      ∑ s : Fin 3, ∑ i : Fin D, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
        (‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * ‖sinEnvelopeHVector d (eig i) s‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro s _
    have h1 : (∑ k : Fin D, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
        ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2) =
        (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          ∑ k : Fin D, ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    have h2 : (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          ∑ k : Fin D, ‖((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k‖ ^ 2 =
        ∑ i : Fin D, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          (‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * ‖sinEnvelopeHVector d (eig i) s‖ ^ 2) := by
      rw [hVid s]
      exact Finset.mul_sum _ _ _
    rw [h1, h2]
  rw [hkey, hmass, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hper : ∀ s : Fin 3,
      (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          (‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * ‖sinEnvelopeHVector d (eig i) s‖ ^ 2) =
        ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 *
          (if s = 1 ∨ s = 2 then ‖sinEnvelopeHVector d (eig i) s‖ ^ 2 else (0:ℝ)) := by
    intro s
    by_cases hc : s = 1 ∨ s = 2 <;> simp [hc]
  rw [Finset.sum_congr rfl (fun s _ => hper s), ← Finset.mul_sum]
  have hsum3 : (∑ s : Fin 3, (if s = 1 ∨ s = 2 then ‖sinEnvelopeHVector d (eig i) s‖ ^ 2
      else (0:ℝ))) = sinEnvelopeFilterF d (eig i) ^ 2 + sinEnvelopeFilterG d (eig i) ^ 2 := by
    rw [Fin.sum_univ_three]
    have h1 : sinEnvelopeHVector d (eig i) 1 = (sinEnvelopeFilterF d (eig i) : ℂ) := by
      simp [sinEnvelopeHVector]
    have h2 : sinEnvelopeHVector d (eig i) 2 = (sinEnvelopeFilterG d (eig i) : ℂ) := by
      simp [sinEnvelopeHVector]
    simp [h1, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsum3]
  rfl

private theorem qls_mulVec_sum {H ι : Type} [Fintype H] [DecidableEq H] [Fintype ι]
    (A : Matrix H H ℂ) (f : ι → QState H) :
    A *ᵥ (∑ i, f i) = ∑ i, A *ᵥ f i := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem qls_tensorState_smul_right {I J : Type} (ψ : QState I) (c : ℂ) (w : QState J) :
    TensorState ψ (c • w) = c • TensorState ψ w := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

private theorem qls_tensorState_sum_smul_right {I J ι : Type} [Fintype ι]
    (ψ : QState I) (β : ι → ℂ) (f : ι → QState J) :
    TensorState ψ (∑ i, β i • f i) = ∑ i, β i • TensorState ψ (f i) := by
  funext p
  simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem qls_phaseFlagEmbed_smul {I : Type} (M : ℕ) (c : ℂ) (ψ : QState (Fin M × I)) :
    phaseFlagEmbed M (c • ψ) = c • phaseFlagEmbed M ψ := by
  funext p
  obtain ⟨x, b, i⟩ := p
  cases b <;> simp [phaseFlagEmbed]

private theorem qls_phaseFlagEmbed_sum {I ι : Type} [Fintype ι] (M : ℕ)
    (f : ι → QState (Fin M × I)) :
    phaseFlagEmbed M (∑ i, f i) = ∑ i, phaseFlagEmbed M (f i) := by
  funext p
  obtain ⟨x, b, i⟩ := p
  cases b <;> simp [phaseFlagEmbed, Finset.sum_apply]

private theorem qls_clean_embed {D : ℕ} (M : ℕ) (m₀ : Fin M) (ψ : QState (Fin 3 × Fin D)) :
    TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M (TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) ψ) := by
  funext p
  obtain ⟨x, b, s, i⟩ := p
  cases b <;> simp [TensorState, phaseFlagEmbed, Qatlib.Foundations.PureStateMath.Ket]

private theorem qls_phaseFlagEmbed_eq_sector {D M : ℕ}
    (φ : QState (Fin M × (Fin 3 × Fin D))) :
    phaseFlagEmbed (I := Fin 3 × Fin D) M φ =
      relabelState (sinEnvelopeSectorEquiv D M) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) φ) := by
  funext p
  obtain ⟨a, s, f, i⟩ := p
  cases s <;> simp [phaseFlagEmbed, relabelState, sinEnvelopeSectorEquiv, TensorState,
      Qatlib.Foundations.PureStateMath.Ket]

private theorem qls_liftGate_apply {D M : ℕ}
    (G : Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ)
    (φ : QState (Fin M × (Fin 3 × Fin D))) :
    sinEnvelopeLiftGate G *ᵥ phaseFlagEmbed (I := Fin 3 × Fin D) M φ =
      phaseFlagEmbed M (G *ᵥ φ) := by
  show ApplyGate _ _ = phaseFlagEmbed M (ApplyGate G φ)
  rw [sinEnvelopeLiftGate, qls_phaseFlagEmbed_eq_sector, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, ← qls_phaseFlagEmbed_eq_sector]

private theorem qls_prepMain_apply {D M : ℕ} (m₀ : Fin M) (B : Operator D) (ψ : QState (Fin D)) :
    sinEnvelopePrepMain (M := M) B *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (B *ᵥ ψ)) := by
  show ApplyGate _ _ = TensorState _ (TensorState _ (ApplyGate B ψ))
  have hprod : TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ) =
      relabelState (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
        (TensorState (TensorState (Qatlib.Foundations.PureStateMath.Ket m₀) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3))) ψ) :=
    (relabelState_prodAssoc _ _ _).symm
  rw [sinEnvelopePrepMain, hprod, applyGate_relabelGate, applyGate_tensorGate_prodAssoc,
    applyGate_one, applyGate_one]

private theorem qls_oracle_column {D : ℕ} (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) :
    continuousHHLOracle eig V *ᵥ (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) := by
  have hUV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hV
  have hc : Vᴴ *ᵥ (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) = Qatlib.Foundations.PureStateMath.Ket i := by
    rw [Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
  unfold continuousHHLOracle
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  have hd : Matrix.diagonal (fun k => Complex.exp (2 * Real.pi * Complex.I * (eig k : ℂ)))
      *ᵥ Qatlib.Foundations.PureStateMath.Ket i = Complex.exp (2 * Real.pi * Complex.I * eig i) • Qatlib.Foundations.PureStateMath.Ket i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    by_cases hk : k = i
    · subst k; simp [Qatlib.Foundations.PureStateMath.Ket]
    · simp [Qatlib.Foundations.PureStateMath.Ket, hk]
  rw [hd, Matrix.mulVec_smul]

private theorem qls_oracleLift_eigen {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) (g : QState (Fin 3)) :
    (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) (continuousHHLOracle eig V)) *ᵥ
        TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) := by
  show ApplyGate _ _ = _
  rw [applyGate_tensorGate, applyGate_one]
  rw [show ApplyGate (continuousHHLOracle eig V) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) from
    qls_oracle_column eig V hV i]
  exact qls_tensorState_smul_right g _ _

private theorem qls_forward_image_eigen {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D)
    (g : QState (Fin 3)) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M
        (TensorState (sinEnvelopeKernel M (eig i)) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) := by
  have hψ := qls_oracleLift_eigen eig V hV i g
  have hmain := sin_envelope_forward_eigenstate (I := Fin 3 × Fin D) M hM _
    (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i)) (eig i) hψ
  have hce : phaseFlagEmbed (I := Fin 3 × Fin D) M
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) :=
    (qls_clean_embed M _ _).symm
  calc (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i)))
      = ApplyGate (evaluate (sinEnvelopeOracleLift (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
            (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i)))) :=
        congrArg _ hce
    _ = phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i)) (TensorState g (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) := by
        rw [show sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM =
            ((sinEnvelopePhaseCircuit (I := Fin 3 × Fin D) M hM).map stepToAdjoint).reverse
          from rfl, ← run_eq_evaluate]
        exact hmain

private theorem qls_ideal_state_expansion {D : ℕ} (eig : Fin D → ℝ) (V B : Operator D)
    (ψ : QState (Fin D)) (d : ℝ) :
    (fun p : Fin 3 × Fin D =>
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
          (B *ᵥ ψ)) p.2) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) := by
  funext p
  obtain ⟨s, k⟩ := p
  show ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
      (B *ᵥ ψ)) k = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_mulVec_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, TensorState, smul_eq_mul,
    Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem qls_word_eval {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D) (d : ℝ)
    (B : Operator D) :
    evaluate (sinEnvelopeOracleLift (D := D) (M := M) U) (sinEnvelopeHHLWord M hM d B) =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *
        (sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *
          (evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) *
            sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B))) := by
  rw [sinEnvelopeHHLWord, evaluate_append, evaluate_append, evaluate_append,
    evaluate_adjointCircuit]
  simp only [evaluate, instructionMatrix, mul_one]
  noncomm_ring

private theorem qls_forward_spectral {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D))
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
            (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) := by
  rw [qls_clean_embed M _ _, qls_liftGate_apply, qls_prepMain_apply _ B ψ]
  conv_lhs => rw [gridHHL_eigen_expansion (M := M) V hV (B *ᵥ ψ)]
  rw [qls_tensorState_sum_smul_right, qls_tensorState_sum_smul_right,
    qls_phaseFlagEmbed_sum]
  simp_rw [qls_phaseFlagEmbed_smul]
  rw [qls_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ ψ)) i • ·)
    (qls_forward_image_eigen M hM eig V hV i (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)))

private theorem qls_forward_ideal {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (fun p : Fin 3 × Fin D =>
            ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
              (B *ᵥ ψ)) p.2))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))) := by
  rw [qls_clean_embed M _ _, qls_ideal_state_expansion eig V B ψ d]
  rw [qls_tensorState_sum_smul_right, qls_phaseFlagEmbed_sum]
  simp_rw [qls_phaseFlagEmbed_smul]
  rw [qls_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ ψ)) i • ·)
    (qls_forward_image_eigen M hM eig V hV i (sinEnvelopeHVector d (eig i)))

private theorem qls_blockDiag_mulVec {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (W : C → Matrix (Fin n) (Fin n) ℂ) (v : QState (C × Fin n)) (c : C) (i : Fin n) :
    (BlockDiag W *ᵥ v) (c, i) = (W c *ᵥ (fun i' => v (c, i'))) i := by
  show (∑ q : C × Fin n, BlockDiag W (c, i) q * v q) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · rw [show (∑ x : Fin n, BlockDiag W (c, i) (c, x) * v (c, x)) =
        ∑ x : Fin n, W c i x * v (c, x) from Finset.sum_congr rfl fun x _ => by
      rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_pos rfl]]
    rfl
  · intro c' _ hc'
    apply Finset.sum_eq_zero
    intro x _
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_neg (fun h => hc' h.symm),
        zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

private theorem qls_flagGate_kernel_apply {D : ℕ} (M : ℕ) (d : ℝ) (hd : 0 < d)
    (θ : ℝ) (w : QState (Fin D)) :
    sinEnvelopeFlagGate (D := D) (M := M) d *ᵥ
        TensorState (sinEnvelopeKernel M θ) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) w) =
      fun p : Fin M × (Fin 3 × Fin D) =>
        sinEnvelopeKernel M θ p.1 *
          TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M p.1)) w p.2 := by
  have hstate : TensorState (sinEnvelopeKernel M θ) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) w) =
      relabelState (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
        (TensorState (TensorState (sinEnvelopeKernel M θ) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3))) w) :=
    (relabelState_prodAssoc _ _ _).symm
  show ApplyGate _ _ = _
  rw [sinEnvelopeFlagGate, hstate, applyGate_relabelGate, applyGate_tensorGate,
    applyGate_one]
  funext p
  obtain ⟨z, s, k⟩ := p
  show ((BlockDiag (fun z : Fin M => sinEnvelopeFlagRotation d (sinEnvelopeDecode M z))) *ᵥ
      (TensorState (sinEnvelopeKernel M θ) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)))) (z, s) * w k = _
  rw [qls_blockDiag_mulVec]
  have hvec : (fun s' => TensorState (sinEnvelopeKernel M θ) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (z, s')) =
      (sinEnvelopeKernel M θ z) • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) := by
    funext s'
    simp [TensorState, Pi.smul_apply, smul_eq_mul]
  rw [hvec, Matrix.mulVec_smul,
    (sin_envelope_flag_rotation_unitary_and_column d (sinEnvelopeDecode M z) hd).2]
  simp [TensorState, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem qls_liftFlag_kernel_apply {D : ℕ} (M : ℕ) (d : ℝ) (hd : 0 < d)
    (θ : ℝ) (w : QState (Fin D)) :
    sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M θ) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) w)) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M
        (fun p : Fin M × (Fin 3 × Fin D) =>
          sinEnvelopeKernel M θ p.1 *
            TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M p.1)) w p.2) := by
  rw [qls_liftGate_apply, qls_flagGate_kernel_apply M d hd θ w]

private theorem qls_flag_image {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
        ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
          (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
            TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ)))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) := by
  rw [qls_forward_spectral hM eig V B ψ hV, qls_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ ψ)) i • ·)
    (qls_liftFlag_kernel_apply M d hd (eig i) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))

private theorem qls_diff_apply {D M : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ)
    (p : Fin M × (Bool × (Fin 3 × Fin D))) :
    (∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        (phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
         phaseFlagEmbed M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p =
      if p.2.1 then 0 else
        ∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) p.1 *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M p.1) p.2.2.1 -
              sinEnvelopeHVector d (eig i) p.2.2.1) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) p.2.2.2)) := by
  obtain ⟨z, b, s, k⟩ := p
  cases b <;> simp [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, phaseFlagEmbed,
    TensorState, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem qls_norm_coe_sub_sq (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ ^ 2 = (x - y) ^ 2 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem qls_diff_weighted_reduce {D M : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ) (w : Fin 3 → ℝ) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        w p.2.2.1 * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ z : Fin M, ∑ s : Fin 3, ∑ k : Fin D,
        w s * ‖∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))‖^2 := by
  have e1 : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        w p.2.2.1 * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ z : Fin M, ∑ q : Bool × (Fin 3 × Fin D),
        w q.2.1 * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q' : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q'.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q'.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q'.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) (z, q)‖^2 :=
    Fintype.sum_prod_type _
  rw [e1]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have htrue : (∑ r : Fin 3 × Fin D, w r.1 * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        (phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q' : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q'.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q'.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q'.2) -
         phaseFlagEmbed M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) (z, (true, r))‖^2) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    obtain ⟨s, k⟩ := r
    rw [qls_diff_apply]
    simp
  rw [htrue, zero_add]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro k _
  rw [qls_diff_apply]
  simp

private theorem qls_diff_weighted_parseval {D M : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ) (w : Fin 3 → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ z : Fin M, ∑ s : Fin 3, ∑ k : Fin D,
        w s * ‖∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 := by
  have hinner : ∀ (z : Fin M) (s : Fin 3),
      (∑ k : Fin D, ‖∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))‖^2) =
        ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2) := by
    intro z s
    have hpt : ∀ k : Fin D, (∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))) =
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            (sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s)))) k := by
      intro k
      rw [matrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hpt]
    simp only [← Complex.normSq_eq_norm_sq]
    rw [sum_normSq_mulVec_of_mem_unitaryGroup hV]
    simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
  have hstep1 : (∑ z : Fin M, ∑ s : Fin 3, ∑ k : Fin D,
        w s * ‖∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))‖^2) =
      ∑ z : Fin M, ∑ s : Fin 3,
        w s * ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2) := by
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum, hinner]
  rw [hstep1]
  have hstep2 : (∑ z : Fin M, ∑ s : Fin 3,
        w s * ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2)) =
      ∑ z : Fin M, ∑ i : Fin D, (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2) *
        ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
          sinEnvelopeHVector d (eig i) s‖^2 := by
    apply Finset.sum_congr rfl
    intro z _
    have hexp : ∀ s : Fin 3, w s * ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
        (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) =
        ∑ i : Fin D, w s * (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2)) := by
      intro s
      exact Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun s _ => hexp s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hpt : ∀ s : Fin 3,
        w s * (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2)) =
        (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2) *
          (w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) := by
      intro s
      ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), ← Finset.mul_sum]
  rw [hstep2]
  have hstep3 : (∑ z : Fin M, ∑ i : Fin D, (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2) *
        ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
          sinEnvelopeHVector d (eig i) s‖^2) =
      ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hpt : ∀ z : Fin M,
        (‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2) *
          ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 =
        ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ∑ s : Fin 3, w s * ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) := by
      intro z
      ring
    rw [Finset.sum_congr rfl (fun z _ => hpt z), ← Finset.mul_sum]
  rw [hstep3]

private theorem qls_diff_parseval {D M : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 := by
  have h1 := qls_diff_weighted_reduce (M := M) eig V B ψ d (fun _ => 1)
  have h2 := qls_diff_weighted_parseval (M := M) eig V B ψ d (fun _ => 1) hV
  have hone : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
        ∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
          (1 : ℝ) * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
            (phaseFlagEmbed (I := Fin 3 × Fin D) M
              (fun q : Fin M × (Fin 3 × Fin D) =>
                sinEnvelopeKernel M (eig i) q.1 *
                  TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
             phaseFlagEmbed M
              (TensorState (sinEnvelopeKernel M (eig i))
                (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2 :=
    Finset.sum_congr rfl fun _ _ => (one_mul _).symm
  rw [hone, h1, h2]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_mul]

private theorem qls_diff_parseval_joint {D M : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p ∈ sinEnvelopeJointSet D M,
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ ψ)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2) := by
  have hsum_filter : (∑ p ∈ sinEnvelopeJointSet D M,
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2 := by
    unfold sinEnvelopeJointSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.2.2.1 = 1 ∨ p.2.2.1 = 2 <;> simp [hp]
  have hred : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (if p.2.2.1 = 1 ∨ p.2.2.1 = 2 then (1:ℝ) else 0) * ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) p‖^2) =
      ∑ z : Fin M, ∑ s : Fin 3, ∑ k : Fin D,
        (if s = 1 ∨ s = 2 then (1:ℝ) else 0) * ‖∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) k))‖^2 :=
    qls_diff_weighted_reduce eig V B ψ d (fun s => if s = 1 ∨ s = 2 then 1 else 0)
  rw [hsum_filter, hred, qls_diff_weighted_parseval (M := M) eig V B ψ d
    (fun s => if s = 1 ∨ s = 2 then 1 else 0) hV]
  apply Finset.sum_congr rfl
  intro i _
  have hs3 : ∀ z : Fin M, (∑ s : Fin 3, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
        ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s - sinEnvelopeHVector d (eig i) s‖^2) =
      ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
        (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2) := by
    intro z
    rw [Fin.sum_univ_three]
    have h1 : sinEnvelopeHVector d (sinEnvelopeDecode M z) 1 =
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ) := by
      simp [sinEnvelopeHVector]
    have h2 : sinEnvelopeHVector d (sinEnvelopeDecode M z) 2 =
        (sinEnvelopeFilterG d (sinEnvelopeDecode M z) : ℂ) := by
      simp [sinEnvelopeHVector]
    have h3 : sinEnvelopeHVector d (eig i) 1 = (sinEnvelopeFilterF d (eig i) : ℂ) := by
      simp [sinEnvelopeHVector]
    have h4 : sinEnvelopeHVector d (eig i) 2 = (sinEnvelopeFilterG d (eig i) : ℂ) := by
      simp [sinEnvelopeHVector]
    simp only [h1, h2, h3, h4, qls_norm_coe_sub_sq]
    have z0 : ¬((0 : Fin 3) = 1 ∨ (0 : Fin 3) = 2) := by decide
    have z1 : ((1 : Fin 3) = 1 ∨ (1 : Fin 3) = 2) := by decide
    have z2 : ((2 : Fin 3) = 1 ∨ (2 : Fin 3) = 2) := by decide
    simp [z0, z1, z2]
  have hz : (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        ∑ s : Fin 3, (if s = 1 ∨ s = 2 then (1:ℝ) else 0) *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) =
      (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [hs3 z]
  rw [hz]

private def qls_flag_diag {D M : ℕ}
    (G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ) :
    Prop :=
  ∀ p p' : Fin M × (Bool × (Fin 3 × Fin D)), p.2.2.1 ≠ p'.2.2.1 → G p p' = 0

private theorem qls_flag_diag_one {D M : ℕ} :
    qls_flag_diag (1 : Matrix (Fin M × (Bool × (Fin 3 × Fin D)))
      (Fin M × (Bool × (Fin 3 × Fin D))) ℂ) := by
  intro p p' h
  exact Matrix.one_apply_ne (fun he => h (by rw [he]))

private theorem qls_flag_diag_mul {D M : ℕ}
    {G G' : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : qls_flag_diag G) (hG' : qls_flag_diag G') : qls_flag_diag (G * G') := by
  intro p p' h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro p'' _
  by_cases h1 : p.2.2.1 = p''.2.2.1
  · rw [hG' p'' p' (fun hh => h (h1.trans hh)), mul_zero]
  · rw [hG p p'' h1, zero_mul]

private theorem qls_flag_diag_adjoint {D M : ℕ}
    {G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : qls_flag_diag G) : qls_flag_diag Gᴴ := by
  intro p p' h
  simp [Matrix.conjTranspose_apply, hG p' p h.symm]

private theorem qls_flag_diag_tensor_one {D M : ℕ} (T : Matrix (Fin M) (Fin M) ℂ) :
    qls_flag_diag (TensorGate T
      (1 : Matrix (Bool × (Fin 3 × Fin D)) (Bool × (Fin 3 × Fin D)) ℂ)) := by
  intro p p' h
  obtain ⟨m, b, s, i⟩ := p
  obtain ⟨m', b', s', i'⟩ := p'
  rw [tensorGate_apply,
    Matrix.one_apply_ne (fun he => h (Prod.ext_iff.mp (Prod.ext_iff.mp he).2 |>.1)), mul_zero]

private theorem qls_flag_diag_perm {D M : ℕ} (k : ℕ) :
    qls_flag_diag (D := D) (M := M)
      (permMatrix (phaseThresholdFlip (I := Fin 3 × Fin D) M k)) := by
  intro p p' h
  have hne : p ≠ phaseThresholdFlip (I := Fin 3 × Fin D) M k p' := by
    intro he
    apply h
    rw [he]
    rfl
  simp [permMatrix, hne]

private theorem qls_flag_diag_oracleLift {D M : ℕ} (U : Operator D) :
    qls_flag_diag (D := D) (M := M) (sinEnvelopeOracleLift U) := by
  intro p p' h
  obtain ⟨m, b, s, i⟩ := p
  obtain ⟨m', b', s', i'⟩ := p'
  show (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (controlOracle (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U))) (m, (b, s, i))
      (m', (b', s', i')) = 0
  rw [tensorGate_apply, mul_eq_zero]
  right
  simp only [controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply]
  by_cases hb : b = b'
  · subst hb
    rw [if_pos rfl]
    cases b
    · have hif : (if (false : Bool) = true then
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U else 1) = 1 := if_neg (by decide)
      rw [hif, Matrix.one_apply_ne (fun he => h (Prod.ext_iff.mp he).1)]
    · have hif : (if (true : Bool) = true then
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U else 1) =
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U := if_pos rfl
      rw [hif, tensorGate_apply, Matrix.one_apply_ne h, zero_mul]
  · rw [if_neg hb]

private theorem qls_flag_diag_loop_step {D : ℕ} (M n : ℕ) (U : Operator D) :
    ∀ s ∈ phaseThresholdLoop (I := Fin 3 × Fin D) M n,
      qls_flag_diag (instructionMatrix (sinEnvelopeOracleLift (D := D) (M := M) U)
        (stepToAdjoint s)) := by
  induction n with
  | zero => intro s hs; simp [phaseThresholdLoop] at hs
  | succ n ih =>
    intro s hs
    simp only [phaseThresholdLoop, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih s hs
    · simp only [phaseThresholdBlock, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact qls_flag_diag_perm n
      · exact qls_flag_diag_oracleLift U
      · exact qls_flag_diag_perm n

private theorem qls_flag_diag_forwardWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D) :
    ∀ c ∈ sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM,
      qls_flag_diag (instructionMatrix (sinEnvelopeOracleLift (D := D) (M := M) U) c) := by
  intro c hc
  rw [sinEnvelopeForwardWord, List.mem_reverse] at hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  simp only [sinEnvelopePhaseCircuit, List.mem_append, List.mem_singleton] at hs
  rcases hs with (rfl | hs) | rfl
  · exact qls_flag_diag_tensor_one _
  · exact qls_flag_diag_loop_step M _ U s hs
  · exact qls_flag_diag_tensor_one _

private theorem qls_flag_diag_evaluate {D M : ℕ}
    (O : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ)
    (l : List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D))))) :
    (∀ c ∈ l, qls_flag_diag (instructionMatrix O c)) →
      qls_flag_diag (evaluate O l) := by
  induction l with
  | nil => intro _; exact qls_flag_diag_one
  | cons c cs ih =>
    intro hl
    exact qls_flag_diag_mul (hl c List.mem_cons_self)
      (ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')))

private theorem qls_measureProb_flag_diag_joint {D M : ℕ}
    {G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : qls_flag_diag G) (hGu : G ∈ Matrix.unitaryGroup _ ℂ)
    (v : QState (Fin M × (Bool × (Fin 3 × Fin D)))) :
    MeasureProb (G *ᵥ v) (sinEnvelopeJointSet D M) =
      MeasureProb v (sinEnvelopeJointSet D M) := by
  have hcol : Collapse (G *ᵥ v) (sinEnvelopeJointSet D M) =
      G *ᵥ Collapse v (sinEnvelopeJointSet D M) := by
    funext p
    rw [collapse_apply]
    by_cases hp : p ∈ sinEnvelopeJointSet D M
    · rw [if_pos hp]
      show (∑ p', G p p' * v p') =
          ∑ p', G p p' * Collapse v (sinEnvelopeJointSet D M) p'
      apply Finset.sum_congr rfl
      intro p' _
      by_cases hp' : p' ∈ sinEnvelopeJointSet D M
      · rw [collapse_apply, if_pos hp']
      · rw [collapse_apply, if_neg hp', mul_zero]
        have h1 : p.2.2.1 = 1 ∨ p.2.2.1 = 2 := (Finset.mem_filter.mp hp).2
        have h2 : ¬(p'.2.2.1 = 1 ∨ p'.2.2.1 = 2) :=
          fun hh => hp' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        have hne : p.2.2.1 ≠ p'.2.2.1 := by
          intro hh
          exact h2 (by rw [← hh]; exact h1)
        rw [hG p p' hne, zero_mul]
    · rw [if_neg hp]
      show (0 : ℂ) = ∑ p', G p p' * Collapse v (sinEnvelopeJointSet D M) p'
      symm
      apply Finset.sum_eq_zero
      intro p' _
      by_cases hp' : p' ∈ sinEnvelopeJointSet D M
      · rw [collapse_apply, if_pos hp']
        have h2 : p'.2.2.1 = 1 ∨ p'.2.2.1 = 2 := (Finset.mem_filter.mp hp').2
        have h1 : ¬(p.2.2.1 = 1 ∨ p.2.2.1 = 2) :=
          fun hh => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        have hne : p.2.2.1 ≠ p'.2.2.1 := by
          intro hh
          exact h1 (by rw [hh]; exact h2)
        rw [hG p p' hne, zero_mul]
      · rw [collapse_apply, if_neg hp', mul_zero]
  rw [← sum_normSq_collapse, ← sum_normSq_collapse, hcol]
  simp only [← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hGu _

private theorem qls_measureProb_collapse_univ {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) : MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S := by
  simpa only [MeasureProb, BornProb] using! sum_normSq_collapse ψ S

private theorem qls_postMeasure_collapse_univ {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) : PostMeasure (Collapse ψ S) Finset.univ = PostMeasure ψ S := by
  funext i
  simp [PostMeasure, qls_measureProb_collapse_univ ψ S, collapse_apply]

private theorem qls_conditional_postMeasure {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (h : 0 < MeasureProb ψ S) :
    sinEnvelopeConditionalOutput (PostMeasure ψ S) = PostMeasure ψ S := by
  have hmass : MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S :=
    qls_measureProb_collapse_univ ψ S
  have hnz : toEuclidean_fromVec (Collapse ψ S) ≠ 0 := by
    intro hh
    have hnorm := norm_toEuclidean_collapse_eq_sqrt_measureProb ψ S
    rw [hh] at hnorm
    have h2 : Real.sqrt (MeasureProb ψ S) = 0 := hnorm.symm.trans (by simp)
    exact absurd ((Real.sqrt_eq_zero (measureProb_nonneg ψ S)).mp h2) (ne_of_gt h)
  have hnorm1 : ‖toEuclidean_fromVec (PostMeasure ψ S)‖ = 1 := by
    rw [toEuclidean_postMeasure_eq_normalize]
    exact NormedSpace.norm_normalize hnz
  have hsum : (∑ p, ‖PostMeasure ψ S p‖ ^ 2) = 1 := by
    rw [← norm_toEuclidean_fromVec_sq, hnorm1]
    simp
  unfold sinEnvelopeConditionalOutput
  rw [hsum]
  simp

private theorem qls_postMeasure_joint_gap {I : Type} [Fintype I] [DecidableEq I]
    (out ideal : QState I) (S : Finset I) {ε : ℝ}
    (hclose : ‖toEuclidean_fromVec (Collapse out S - Collapse ideal S)‖ ≤ ε)
    (hgap : ε < Real.sqrt (MeasureProb ideal S)) :
    0 < MeasureProb out S ∧
      ‖toEuclidean_fromVec (PostMeasure out S - PostMeasure ideal S)‖ ≤
        2 * ε / Real.sqrt (MeasureProb ideal S) := by
  have hmass : MeasureProb (Collapse ideal S) Finset.univ = MeasureProb ideal S :=
    qls_measureProb_collapse_univ ideal S
  have hmassOut : MeasureProb (Collapse out S) Finset.univ = MeasureProb out S :=
    qls_measureProb_collapse_univ out S
  have hgap' : ε < Real.sqrt (MeasureProb (Collapse ideal S) Finset.univ) := by
    rw [hmass]; exact hgap
  have h := postMeasure_error_of_gap (Collapse ideal S) (Collapse out S) Finset.univ
    hclose hgap'
  refine ⟨?_, ?_⟩
  · rw [← hmassOut]
    exact h.1
  · rw [← qls_postMeasure_collapse_univ out S, ← qls_postMeasure_collapse_univ ideal S]
    rw [hmass] at h
    exact h.2

private theorem qls_collapse_sub {I : Type} [Fintype I] [DecidableEq I] (φ ψ : QState I)
    (S : Finset I) : Collapse φ S - Collapse ψ S = Collapse (φ - ψ) S := by
  funext i
  simp only [collapse_apply, Pi.sub_apply]
  split_ifs <;> simp

private theorem qls_ket_norm_sq {I : Type} [Fintype I] [DecidableEq I] (j : I) :
    ∑ i : I, ‖(Qatlib.Foundations.PureStateMath.Ket j : QState I) i‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single j]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro i _ hij
    simp [Qatlib.Foundations.PureStateMath.Ket, hij]
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem qls_ideal_mass_lower {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) :
    min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeIdealMass M hM eig V B j d := by
  have hmass : sinEnvelopeIdealMass M hM eig V B j d =
      ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i) := rfl
  have hper : ∀ i : Fin D, min (1 / 4) (16 * d ^ 2) * ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 ≤
      ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i) := by
    intro i
    have h := qls_flag_mass_lower d (eig i) hd (heig i).1 (heig i).2
    have hnn : 0 ≤ ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 := sq_nonneg _
    nlinarith
  have hb := qls_beta_total V B (Qatlib.Foundations.PureStateMath.Ket j) hV hB
  have hj := qls_ket_norm_sq j
  calc min (1 / 4) (16 * d ^ 2)
      = min (1 / 4) (16 * d ^ 2) * 1 := (mul_one _).symm
    _ = min (1 / 4) (16 * d ^ 2) * ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 := by
        rw [hb, hj]
    _ = ∑ i : Fin D, min (1 / 4) (16 * d ^ 2) * ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = sinEnvelopeIdealMass M hM eig V B j d := hmass.symm

private theorem qls_workspace_diff {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (ψ : QState (Fin D)) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeHHLWord M hM d B) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ)) -
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
        (fun p : Fin 3 × Fin D =>
          ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
            (B *ᵥ ψ)) p.2))) =
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
      (∑ i, (Vᴴ *ᵥ (B *ᵥ ψ)) i •
        (phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
         phaseFlagEmbed M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) := by
  classical
  have hU : continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    continuous_hhl_oracle_unitary eig V hV
  have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
    wellFormedAdjointCircuit_stepToAdjoint_reverse _ (sin_envelope_phase_circuit_unitary M hM)
  have ho : sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V) ∈
      Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))
  have hΦ : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) ∈ Matrix.unitaryGroup _ ℂ :=
    hf.evaluate_unitary ho
  have hΦΦ : (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
      (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hΦ
    rwa [Matrix.star_eq_conjTranspose] at h
  have hE2 := qls_forward_ideal hM eig V B ψ d hV
  have hflag := qls_flag_image hM eig V B ψ d hd hV
  have hrun : (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeHHLWord M hM d B)) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ)) =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        (sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
          ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
            (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
              TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
                (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) ψ))))) := by
    rw [qls_word_eval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  have hideal : TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
        (fun p : Fin 3 × Fin D =>
          ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
            (B *ᵥ ψ)) p.2)) =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
          TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
            (fun p : Fin 3 × Fin D =>
              ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
                (B *ᵥ ψ)) p.2))) := by
    rw [Matrix.mulVec_mulVec, hΦΦ, Matrix.one_mulVec]
  rw [hrun, hideal, ← Matrix.mulVec_sub]
  congr 1
  rw [hflag, hE2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm

theorem clause58 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d ε : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < ε → ε ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        (C : ℝ) / (d * ε) ≤ (M : ℝ) →
        let out := sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j
        let S := sinEnvelopeJointSet D M

        (min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeJointIdealMass M hM eig V B j d ∧
          0 < MeasureProb out S ∧

          ‖toEuclidean_fromVec (sinEnvelopeConditionalOutput (PostMeasure out S) -
              sinEnvelopeConditionalOutput
                (PostMeasure (sinEnvelopeHHLIdeal M hM eig V d B j) S))‖ ≤ ε) ∧

      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        21 / (d * η) ≤ (M : ℝ) →
        ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
            sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η) ∧

      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        21 / (d * η) ≤ (M : ℝ) →
        |sinEnvelopeActualMass M hM eig V B j d -
            sinEnvelopeIdealMass M hM eig V B j d| ≤
          (47 / (d * (M : ℝ))) * sinEnvelopeIdealMass M hM eig V B j d) := by
  refine ⟨200, by norm_num, ?_⟩
  intro D M hM eig V B j d ε hV hB hd hε hε1 heig hbudget
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have key :
      (min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeJointIdealMass M hM eig V B j d ∧
        0 < MeasureProb (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
            (sinEnvelopeJointSet D M) ∧
        ‖toEuclidean_fromVec (sinEnvelopeConditionalOutput
              (PostMeasure (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
                (sinEnvelopeJointSet D M)) -
            sinEnvelopeConditionalOutput
              (PostMeasure (sinEnvelopeHHLIdeal M hM eig V d B j)
                (sinEnvelopeJointSet D M)))‖ ≤ ε) ∧
      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        21 / (d * η) ≤ (M : ℝ) →
        ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
            sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η) ∧
      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        21 / (d * η) ≤ (M : ℝ) →
        |sinEnvelopeActualMass M hM eig V B j d -
            sinEnvelopeIdealMass M hM eig V B j d| ≤
          (47 / (d * (M : ℝ))) * sinEnvelopeIdealMass M hM eig V B j d) := by
    refine ⟨?_, ?_, ?_⟩
    · have ha : min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeIdealMass M hM eig V B j d :=
        qls_ideal_mass_lower M hM eig V B j d hd hV hB heig
      have hmassPos : (0 : ℝ) < sinEnvelopeIdealMass M hM eig V B j d := by
        have h1 : (0 : ℝ) < min (1 / 4) (16 * d ^ 2) := by
          rw [lt_min_iff]
          constructor
          · norm_num
          · positivity
        exact lt_of_lt_of_le h1 ha
      have hU : continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
        continuous_hhl_oracle_unitary eig V hV
      have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
        wellFormedAdjointCircuit_stepToAdjoint_reverse _
          (sin_envelope_phase_circuit_unitary M hM)
      have ho : sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V) ∈
          Matrix.unitaryGroup _ ℂ :=
        tensorGate_unitary (Submonoid.one_mem _)
          (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))
      have hΦ : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) ∈ Matrix.unitaryGroup _ ℂ :=
        hf.evaluate_unitary ho
      have hΦdiag : qls_flag_diag
          (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) :=
        qls_flag_diag_evaluate _ _ (qls_flag_diag_forwardWord M hM _)
      have hD : (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
            sinEnvelopeHHLIdeal M hM eig V d B j) =
          (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
            (∑ i, (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i •
              (phaseFlagEmbed (I := Fin 3 × Fin D) M
                (fun q : Fin M × (Fin 3 × Fin D) =>
                  sinEnvelopeKernel M (eig i) q.1 *
                    TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1))
                      (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
               phaseFlagEmbed M
                (TensorState (sinEnvelopeKernel M (eig i))
                  (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i))))) :=
        qls_workspace_diff hM eig V B (Qatlib.Foundations.PureStateMath.Ket j) d hd hV
      have hmassEq : MeasureProb (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
            sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M) =
          ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
            ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2) := by
        rw [hD]
        have hfd := qls_measureProb_flag_diag_joint
          (qls_flag_diag_adjoint hΦdiag) (mem_unitaryGroup_adjoint hΦ)
          (∑ i, (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i •
            (phaseFlagEmbed (I := Fin 3 × Fin D) M
              (fun q : Fin M × (Fin 3 × Fin D) =>
                sinEnvelopeKernel M (eig i) q.1 *
                  TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1))
                    (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) q.2) -
             phaseFlagEmbed M
              (TensorState (sinEnvelopeKernel M (eig i))
                (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i)))))
        rw [hfd]
        exact mod_cast (by
          simpa only [MeasureProb, BornProb] using!
            qls_diff_parseval_joint (M := M) eig V B (Qatlib.Foundations.PureStateMath.Ket j) d hV)
      have hbound : (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
            ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2)) *
          (d * (M : ℝ))^2 ≤ 2205 * sinEnvelopeIdealMass M hM eig V B j d := by
        have hper : ∀ i : Fin D,
            (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2)) *
              (d * (M : ℝ))^2 ≤ 2205 * sinEnvelopeFlagMass d (eig i) :=
          fun i => qls_joint_filter_error M hM (eig i) d hd (heig i).1 (heig i).2
        have hnn : ∀ i :
            Fin D, 0 ≤ ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 :=
            fun _ => sq_nonneg _
        rw [show sinEnvelopeIdealMass M hM eig V B j d =
            ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 * sinEnvelopeFlagMass d (eig i) from rfl]
        rw [Finset.sum_mul]
        calc ∑ i : Fin D, (‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
              (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
                ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                  (sinEnvelopeFilterG d (sinEnvelopeDecode M z) -
                    sinEnvelopeFilterG d (eig i))^2))) * (d * (M : ℝ))^2
            = ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
                ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
                  ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                    (sinEnvelopeFilterG d (sinEnvelopeDecode M z) -
                      sinEnvelopeFilterG d (eig i))^2)) * (d * (M : ℝ))^2) :=
              Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 * (2205 * sinEnvelopeFlagMass d (eig i)) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hper i) (hnn i)
          _ = 2205 * ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 * sinEnvelopeFlagMass d (eig i) := by
              have hpt : ∀ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
                  (2205 * sinEnvelopeFlagMass d (eig i)) =
                  2205 * (‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 * sinEnvelopeFlagMass d (eig i)) :=
                fun _ => by ring
              rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum]
      have hmpos : 0 < d * (M : ℝ) := mul_pos hd hMpos
      have hM200 : (200 : ℝ) / ε ≤ d * (M : ℝ) := by
        have h1 : (200 : ℝ) ≤ (M : ℝ) * (d * ε) :=
          (div_le_iff₀ (mul_pos hd hε)).mp hbudget
        have h2 : (M : ℝ) * (d * ε) = (M : ℝ) * d * ε := by ring
        have h3 : (M : ℝ) * d * ε = d * (M : ℝ) * ε := by ring
        rw [h2, h3] at h1
        exact (div_le_iff₀ hε).mpr h1
      have hsqr : Real.sqrt (2205 * sinEnvelopeIdealMass M hM eig V B j d / (d * (M : ℝ))^2) =
          Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) / (d * (M : ℝ)) := by
        have hn1 : 0 ≤ (2205 : ℝ) := by norm_num
        have hn2 : 0 ≤ sinEnvelopeIdealMass M hM eig V B j d := hmassPos.le
        rw [Real.sqrt_div (mul_nonneg hn1 hn2), Real.sqrt_mul hn1,
          Real.sqrt_sq hmpos.le]
      have hclose : ‖toEuclidean_fromVec
            (Collapse (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
              sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M))‖ ≤
          Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) / (d * (M : ℝ)) := by
        have hsq : ‖toEuclidean_fromVec
              (Collapse (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
                sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M))‖ =
            Real.sqrt (MeasureProb
              (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
                sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M)) :=
          norm_toEuclidean_collapse_eq_sqrt_measureProb _ _
        rw [hsq, hmassEq]
        have hle : (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i‖^2 *
            ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 +
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d (eig i))^2)) ≤
            2205 * sinEnvelopeIdealMass M hM eig V B j d / (d * (M : ℝ))^2 := by
          rw [le_div_iff₀ (sq_pos_of_pos hmpos)]
          exact hbound
        exact le_trans (Real.sqrt_le_sqrt hle) (by rw [hsqr])
      have hgap : Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) /
            (d * (M : ℝ)) < Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) := by
        have hnn3 : 0 < Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) :=
          Real.sqrt_pos.mpr hmassPos
        have h2205 : Real.sqrt 2205 ≤ (100 : ℝ) := by
          have h := Real.sqrt_le_sqrt (by norm_num : (2205 : ℝ) ≤ (100 : ℝ) ^ 2)
          rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)] at h
        have hre : Real.sqrt 2205 ≤ (200 : ℝ) := by linarith
        have h2 : Real.sqrt 2205 < d * (M : ℝ) := by
          have h200 : (200 : ℝ) ≤ d * (M : ℝ) := by
            have := hM200
            have : (200 : ℝ) / ε ≥ 200 :=
              (le_div_iff₀ hε).mpr (by nlinarith [hε1])
            linarith
          linarith
        have h3 : Real.sqrt 2205 / (d * (M : ℝ)) < 1 := by
          exact (div_lt_one hmpos).mpr h2
        calc Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) / (d * (M : ℝ))
            = (Real.sqrt 2205 / (d * (M : ℝ))) *
                Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) := by
              rw [mul_div_assoc]
              ring
          _ < 1 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) :=
              mul_lt_mul_of_pos_right h3 hnn3
          _ = Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) := one_mul _
      have hclose' : ‖toEuclidean_fromVec
          (Collapse (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
              sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M))‖ ≤
          Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) / (d * (M : ℝ)) :=
        hclose
      have hclosetri : ‖toEuclidean_fromVec
          (Collapse (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
              (sinEnvelopeJointSet D M) -
            Collapse (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M))‖ ≤
          Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) / (d * (M : ℝ)) := by
        rw [qls_collapse_sub]
        exact hclose'
      have hgap' : Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) /
            (d * (M : ℝ)) < Real.sqrt (MeasureProb
              (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M)) := by
        rw [qls_ideal_joint_mass M hM eig V B j d hV]
        exact hgap
      have hPM := qls_postMeasure_joint_gap
        (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
        (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M)
        hclosetri hgap'
      have h2 : (2 : ℝ) * Real.sqrt 2205 / (d * (M : ℝ)) ≤ ε := (div_le_iff₀ hmpos).mpr (by
        have h2205 : Real.sqrt 2205 ≤ (100 : ℝ) := by
          have h := Real.sqrt_le_sqrt (by norm_num : (2205 : ℝ) ≤ (100 : ℝ) ^ 2)
          rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)] at h
        have h2b : (2 : ℝ) * Real.sqrt 2205 ≤ 200 := by nlinarith
        have h1 : (200 : ℝ) ≤ (M : ℝ) * (d * ε) :=
          (div_le_iff₀ (mul_pos hd hε)).mp hbudget
        nlinarith [mul_pos hd hε])
      have hfinal : ‖toEuclidean_fromVec
          (PostMeasure (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
              (sinEnvelopeJointSet D M) -
            PostMeasure (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M))‖ ≤ ε := by
        refine le_trans hPM.2 ?_
        have hmS : MeasureProb (sinEnvelopeHHLIdeal M hM eig V d B j) (sinEnvelopeJointSet D M)
            = sinEnvelopeIdealMass M hM eig V B j d := qls_ideal_joint_mass M hM eig V B j d hV
        rw [hmS]
        have hrew : (2 : ℝ) * (Real.sqrt 2205 * Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) /
              (d * (M : ℝ))) / Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) =
            (2 : ℝ) * Real.sqrt 2205 / (d * (M : ℝ)) := by
          have hb : Real.sqrt (sinEnvelopeIdealMass M hM eig V B j d) ≠ 0 :=
            Real.sqrt_ne_zero'.mpr hmassPos
          have hc : (d * (M : ℝ)) ≠ 0 := ne_of_gt hmpos
          field_simp [hb, hc]
        rw [hrew]
        exact h2
      refine ⟨?_, ?_, ?_⟩
      · show min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeJointIdealMass M hM eig V B j d
        exact ha
      · exact hPM.1
      · have hrun : 0 < MeasureProb (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
            (sinEnvelopeJointSet D M) := hPM.1
        have hideal : 0 < MeasureProb (sinEnvelopeHHLIdeal M hM eig V d B j)
            (sinEnvelopeJointSet D M) := by
          rw [qls_ideal_joint_mass M hM eig V B j d hV]
          exact hmassPos
        rw [qls_conditional_postMeasure _ _ hrun, qls_conditional_postMeasure _ _ hideal]
        exact hfinal
    · intro D M hM eig V B j d η hV hB hd hη hη1 heig hbudget'
      exact sin_envelope_hhl_full_workspace_error M hM eig V B j d η hV hB hd hη hη1 heig hbudget'
    · intro D M hM eig V B j d η hV hB hd hη hη1 heig hbudget'
      exact sin_envelope_postselection_mass_stability M hM eig V B j d η hV hB hd hη hη1 heig
        hbudget'
  exact key

private theorem qls_star_ket {I : Type} [Fintype I] [DecidableEq I] (j i : I) :
    (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket j i) = Qatlib.Foundations.PureStateMath.Ket j i := by
  by_cases h : i = j <;> simp [Qatlib.Foundations.PureStateMath.Ket, h]

private theorem qls_ket_prod {I : Type} [Fintype I] [DecidableEq I] (j j' : I) :
    (∑ i : I, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket j i) * Qatlib.Foundations.PureStateMath.Ket j' i) = if j = j' then (1 : ℂ) else 0 := by
  rw [show (∑ i : I, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket j i) * Qatlib.Foundations.PureStateMath.Ket j' i) = ∑ i : I, Qatlib.Foundations.PureStateMath.Ket j i * Qatlib.Foundations.PureStateMath.Ket j' i from
      Finset.sum_congr rfl fun i _ => by rw [qls_star_ket]]
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp [Qatlib.Foundations.PureStateMath.Ket]
    · intro i _ hi; simp [Qatlib.Foundations.PureStateMath.Ket, hi]
    · intro hh; exact absurd (Finset.mem_univ j) hh
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = j
    · subst hi
      rw [ket_apply, if_pos rfl, ket_apply, if_neg h, mul_zero]
    · rw [ket_apply, if_neg hi, zero_mul]

private theorem qls_inner_mulVec {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (x y : QState I) :
    (∑ i, (starRingEnd ℂ) ((U *ᵥ x) i) * (U *ᵥ y) i) =
      ∑ j, (starRingEnd ℂ) (x j) * y j := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  have hUU : ∀ j k : I, (∑ i, (starRingEnd ℂ) (U i k) * U i j) = if k = j then (1 : ℂ) else 0 := by
    intro j k
    have heq : (∑ i, (starRingEnd ℂ) (U i k) * U i j) = (Uᴴ * U) k j := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    rw [heq, hU, Matrix.one_apply]
  calc ∑ i, (starRingEnd ℂ) ((U *ᵥ x) i) * (U *ᵥ y) i
      = ∑ i, (∑ j, (starRingEnd ℂ) (U i j) * (starRingEnd ℂ) (x j)) * ∑ k, U i k * y k := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    _ = ∑ i, ∑ j, ∑ k, ((starRingEnd ℂ) (U i j) * (starRingEnd ℂ) (x j)) * (U i k * y k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, ∑ i, ((starRingEnd ℂ) (U i j) * (starRingEnd ℂ) (x j)) * (U i k * y k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
    _ = ∑ j, ∑ k, ((starRingEnd ℂ) (x j) * y k) * ∑ i, (starRingEnd ℂ) (U i j) * U i k := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        have hpt : ∀ i : I, ((starRingEnd ℂ) (U i j) * (starRingEnd ℂ) (x j)) * (U i k * y k) =
            ((starRingEnd ℂ) (x j) * y k) * ((starRingEnd ℂ) (U i j) * U i k) := by
          intro i; ring
        rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum]
    _ = ∑ j, ∑ k, ((starRingEnd ℂ) (x j) * y k) * (if j = k then (1 : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hUU k j]
    _ = ∑ j, (starRingEnd ℂ) (x j) * y j := by
        apply Finset.sum_congr rfl
        intro j _
        have hs : (∑ k : I, ((starRingEnd ℂ) (x j) * y k) * (if j = k then (1 : ℂ) else 0)) =
            ((starRingEnd ℂ) (x j) * y j) * (if j = j then (1 : ℂ) else 0) := by
          apply Finset.sum_eq_single j
          · intro k _ hk
            rw [if_neg (Ne.symm hk), mul_zero]
          · intro hh; exact absurd (Finset.mem_univ j) hh
        rw [hs, if_pos rfl, mul_one]

private theorem qls_ket_basis {D : ℕ} (ψ : QState (Fin D)) :
    ψ = ∑ j : Fin D, ψ j • Qatlib.Foundations.PureStateMath.Ket j := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro j _ hj
    rw [ket_apply, if_neg (Ne.symm hj), mul_zero]
  · intro hh; exact absurd (Finset.mem_univ k) hh

private theorem qls_four_factor_c {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (w : α → ℂ) (v : β → ℂ) (c : γ → ℂ) (g : γ → δ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * (c s * g s k)) =
      (∑ a, w a) * (∑ b, v b) * (∑ s, ∑ k, c s * g s k) := by
  have step1 : (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * (c s * g s k))
      = ∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * (c s * ∑ k : δ, g s k) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro s _
    have h1 : (∑ k : δ, w a * v b * (c s * g s k)) = ∑ k : δ, (w a * v b * c s) * g s k := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    have h2 : (∑ k : δ, (w a * v b * c s) * g s k) = (w a * v b * c s) * ∑ k : δ, g s k :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
    ring
  rw [step1]
  have step2 : (∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * (c s * ∑ k : δ, g s k))
      = ∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.mul_sum _ _ _).symm
  rw [step2]
  have step3 : (∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k))
      = ∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) := by
    apply Finset.sum_congr rfl
    intro a _
    have h1 : (∑ b : β, (w a * v b) * ∑ s : γ, (c s * ∑ k : δ, g s k))
        = ∑ b : β, w a * (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    have h2 : (∑ b : β, w a * (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)))
        = w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
  rw [step3]
  have step4 : (∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)))
      = (∑ a : α, w a) * ∑ b : β, (v b * ∑ s : γ, (c s * ∑ k : δ, g s k)) :=
    (Finset.sum_mul _ _ _).symm
  rw [step4]
  have step5 : (∑ b : β, v b * ∑ s : γ, (c s * ∑ k : δ, g s k))
      = (∑ b : β, v b) * ∑ s : γ, (c s * ∑ k : δ, g s k) :=
    (Finset.sum_mul _ _ _).symm
  rw [step5]
  have step6 : (∑ s : γ, (c s * ∑ k : δ, g s k)) = ∑ s : γ, ∑ k : δ, c s * g s k :=
    Finset.sum_congr rfl fun s _ => Finset.mul_sum _ _ _
  rw [step6]
  ring

private theorem qls_clean_inner {D M : ℕ} (m0 : Fin M) (j j' : Fin D) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (starRingEnd ℂ)
          ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p) *
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j')))) p)) = if j = j' then (1 : ℂ) else 0 := by
  have hstar : ∀ p : Fin M × (Bool × (Fin 3 × Fin D)),
      (starRingEnd ℂ)
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p) =
      (TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p := by
    intro p
    obtain ⟨z, b, s, k⟩ := p
    simp only [TensorState, map_mul]
    rw [qls_star_ket, qls_star_ket, qls_star_ket, qls_star_ket]
  have hprod : ∀ p : Fin M × (Bool × (Fin 3 × Fin D)),
      (starRingEnd ℂ)
          ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p) *
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j')))) p) =
      ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p) *
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j')))) p) := by
    intro p
    rw [hstar p]
  rw [Finset.sum_congr rfl (fun p _ => hprod p)]
  have hpt : ∀ (z : Fin M) (b : Bool) (s : Fin 3) (k : Fin D),
      ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) (z, (b, (s, k)))) *
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j')))) (z, (b, (s, k)))) =
      (Qatlib.Foundations.PureStateMath.Ket m0 z * Qatlib.Foundations.PureStateMath.Ket m0 z) * (Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
        ((Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) := by
    intro z b s k
    simp only [TensorState]
    ring
  have hsum : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) p) *
          ((TensorState (Qatlib.Foundations.PureStateMath.Ket m0) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j')))) p)) =
      ∑ z : Fin M, ∑ b : Bool, ∑ s : Fin 3, ∑ k : Fin D,
        (Qatlib.Foundations.PureStateMath.Ket m0 z * Qatlib.Foundations.PureStateMath.Ket m0 z) * (Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
          ((Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    exact hpt z b s k
  rw [hsum, qls_four_factor_c]
  have hz : (∑ z : Fin M, Qatlib.Foundations.PureStateMath.Ket m0 z * Qatlib.Foundations.PureStateMath.Ket m0 z) = 1 := by
    rw [show (∑ z : Fin M, Qatlib.Foundations.PureStateMath.Ket m0 z * Qatlib.Foundations.PureStateMath.Ket m0 z) =
        ∑ z : Fin M, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket m0 z) * Qatlib.Foundations.PureStateMath.Ket m0 z from
      Finset.sum_congr rfl fun z _ => by rw [qls_star_ket]]
    rw [qls_ket_prod]
    simp
  have hb : (∑ b : Bool, Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) = 1 := by
    rw [show (∑ b : Bool, Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) =
        ∑ b : Bool, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket false b) * Qatlib.Foundations.PureStateMath.Ket false b from
      Finset.sum_congr rfl fun b _ => by rw [qls_star_ket]]
    rw [qls_ket_prod]
    simp
  have hz0 : (∑ s : Fin 3, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) = 1 := by
    rw [show (∑ s : Fin 3, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) =
        ∑ s : Fin 3, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s from
      Finset.sum_congr rfl fun s _ => by rw [qls_star_ket]]
    rw [qls_ket_prod]
    simp
  have hk : (∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k) = if j = j' then (1 : ℂ) else 0 := by
    rw [show (∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k) =
        ∑ k : Fin D, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket j k) * Qatlib.Foundations.PureStateMath.Ket j' k from
      Finset.sum_congr rfl fun k _ => by rw [qls_star_ket]]
    rw [qls_ket_prod]
  have hsp : (∑ s : Fin 3, ∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s *
        (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) = if j = j' then (1 : ℂ) else 0 := by
    have h1 : (∑ s : Fin 3, ∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s *
          (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) =
        (∑ s : Fin 3, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * ∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k := by
      have hinner : ∀ s : Fin 3,
          (∑ k : Fin D, (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) =
          (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) * (∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k) :=
        fun s => (Finset.mul_sum _ _ _).symm
      conv_lhs =>
        rw [show (∑ s : Fin 3, ∑ k : Fin D, Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s *
            (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k)) =
          ∑ s : Fin 3, ∑ k : Fin D, (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s * Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) s) *
            (Qatlib.Foundations.PureStateMath.Ket j k * Qatlib.Foundations.PureStateMath.Ket j' k) from
          Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
      rw [Finset.sum_congr rfl (fun s _ => hinner s)]
      exact (Finset.sum_mul _ _ _).symm
    rw [h1, hz0, hk, one_mul]
  rw [hz, hb, hsp]
  ring

private theorem qls_ket_self {I : Type} [Fintype I] [DecidableEq I] (j : I) :
    (∑ i : I, Qatlib.Foundations.PureStateMath.Ket j i * Qatlib.Foundations.PureStateMath.Ket j i) = 1 := by
  have h := qls_ket_prod j j
  rw [show (∑ i : I, Qatlib.Foundations.PureStateMath.Ket j i * Qatlib.Foundations.PureStateMath.Ket j i) =
      ∑ i : I, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket j i) * Qatlib.Foundations.PureStateMath.Ket j i from
    Finset.sum_congr rfl fun i _ => by rw [qls_star_ket]]
  rw [h, if_pos rfl]

private theorem qls_star_mul_scale (h z w : ℂ) :
    (starRingEnd ℂ) (h * z) * (h * w) = ((‖h‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) z * w) := by
  have hh : (starRingEnd ℂ) h * h = ((‖h‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [map_mul, mul_mul_mul_comm, hh]

private theorem qls_mulVec_sum_smul {H ι : Type} [Fintype H] [DecidableEq H] [Fintype ι]
    (A : Matrix H H ℂ) (β : ι → ℂ) (g : ι → QState H) :
    A *ᵥ (∑ i, β i • g i) = ∑ i, β i • (A *ᵥ g i) :=
  (qls_mulVec_sum A (fun i => β i • g i)).trans
    (Finset.sum_congr rfl fun i _ => Matrix.mulVec_smul _ _ _)

private theorem qls_mulVec_basis {D : ℕ} (A : Operator D) (w : QState (Fin D)) :
    A *ᵥ w = ∑ j : Fin D, w j • (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
  conv_lhs => rw [qls_ket_basis w]
  exact qls_mulVec_sum_smul A (fun j => w j) (fun j => Qatlib.Foundations.PureStateMath.Ket j)

private theorem qls_three_factor_c {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (w : α → ℂ) (v : β → ℂ) (g : γ → δ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * g s k) =
      (∑ a, w a) * (∑ b, v b) * (∑ s, ∑ k, g s k) := by
  have step1 : (∑ a : α, ∑ b : β, ∑ s : γ, ∑ k : δ, w a * v b * g s k)
      = ∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * ∑ k : δ, g s k := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro s _
    have h1 : (∑ k : δ, w a * v b * g s k) = ∑ k : δ, (w a * v b) * g s k := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    have h2 : (∑ k : δ, (w a * v b) * g s k) = (w a * v b) * ∑ k : δ, g s k :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
  rw [step1]
  have step2 : (∑ a : α, ∑ b : β, ∑ s : γ, (w a * v b) * ∑ k : δ, g s k)
      = ∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, ∑ k : δ, g s k := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.mul_sum _ _ _).symm
  rw [step2]
  have step3 : (∑ a : α, ∑ b : β, (w a * v b) * ∑ s : γ, ∑ k : δ, g s k)
      = ∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, ∑ k : δ, g s k) := by
    apply Finset.sum_congr rfl
    intro a _
    have h1 : (∑ b : β, (w a * v b) * ∑ s : γ, ∑ k : δ, g s k)
        = ∑ b : β, w a * (v b * ∑ s : γ, ∑ k : δ, g s k) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    have h2 : (∑ b : β, w a * (v b * ∑ s : γ, ∑ k : δ, g s k))
        = w a * ∑ b : β, (v b * ∑ s : γ, ∑ k : δ, g s k) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2]
  rw [step3]
  have step4 : (∑ a : α, w a * ∑ b : β, (v b * ∑ s : γ, ∑ k : δ, g s k))
      = (∑ a : α, w a) * ∑ b : β, (v b * ∑ s : γ, ∑ k : δ, g s k) :=
    (Finset.sum_mul _ _ _).symm
  rw [step4]
  have step5 : (∑ b : β, v b * ∑ s : γ, ∑ k : δ, g s k)
      = (∑ b : β, v b) * ∑ s : γ, ∑ k : δ, g s k :=
    (Finset.sum_mul _ _ _).symm
  rw [step5]
  ring

private theorem qls_cleanOp_run_mulVec {D M : ℕ} (hM : 2 ≤ M) (U : Operator D) (d : ℝ)
    (B : Operator D) (v : QState (Fin D)) :
    sinEnvelopeActualCleanOp M hM U d B *ᵥ v =
      ∑ j : Fin D, v j • sinEnvelopeHHLRun M hM U d B j := by
  funext p
  simp only [sinEnvelopeActualCleanOp, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem qls_cleanOp_ideal_mulVec {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (v : QState (Fin D)) :
    sinEnvelopeIdealCleanOp M hM eig V d B *ᵥ v =
      ∑ j : Fin D, v j • sinEnvelopeHHLIdeal M hM eig V d B j := by
  funext p
  simp only [sinEnvelopeIdealCleanOp, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem qls_cleanOp_diff_mulVec {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (v : QState (Fin D)) :
    (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B -
      sinEnvelopeIdealCleanOp M hM eig V d B) *ᵥ v =
      (∑ j : Fin D, v j • sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j) -
        (∑ j : Fin D, v j • sinEnvelopeHHLIdeal M hM eig V d B j) := by
  rw [Matrix.sub_mulVec, qls_cleanOp_run_mulVec, qls_cleanOp_ideal_mulVec]

private theorem qls_clean_tensor_sum {D M : ℕ} (hM : 2 ≤ M) (v : QState (Fin D)) :
    TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) v)) =
      ∑ j : Fin D, v j • TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j))) := by
  conv_lhs => rw [qls_ket_basis v]
  have hinner : TensorState (Qatlib.Foundations.PureStateMath.Ket false)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (∑ j : Fin D, v j • Qatlib.Foundations.PureStateMath.Ket j)) =
      ∑ j : Fin D, v j • TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)) := by
    have h2 : TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (∑ j : Fin D, v j • Qatlib.Foundations.PureStateMath.Ket j) =
        ∑ j : Fin D, v j • TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j) :=
      qls_tensorState_sum_smul_right (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (fun j => v j) (fun j => Qatlib.Foundations.PureStateMath.Ket j)
    rw [h2, qls_tensorState_sum_smul_right]
  rw [hinner, qls_tensorState_sum_smul_right]

private theorem qls_run_sum {D M : ℕ} (hM : 2 ≤ M) (U : Operator D) (d : ℝ) (B : Operator D)
    (v : QState (Fin D)) :
    (∑ j : Fin D, v j • sinEnvelopeHHLRun M hM U d B j) =
      evaluate (sinEnvelopeOracleLift U) (sinEnvelopeHHLWord M hM d B) *ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) v)) := by
  rw [qls_clean_tensor_sum hM, qls_mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => (Matrix.mulVec_smul _ _ _).symm

private theorem qls_ideal_pointwise {D : ℕ} (eig : Fin D → ℝ) (V B : Operator D) (d : ℝ)
    (s : Fin 3) (v : QState (Fin D)) (k : Fin D) :
    (∑ j : Fin D, v j *
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) =
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ (B *ᵥ v)) k := by
  have hAB : ∀ (A : Operator D) (w : QState (Fin D)),
      A *ᵥ w = ∑ j : Fin D, w j • (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := fun A w => qls_mulVec_basis A w
  have h := congrFun (qls_mulVec_sum_smul
      (V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ)
      (fun j => v j) (fun j => B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k
  rw [hAB B v, h, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_eq_mul]

private theorem qls_ideal_sum {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
    (d : ℝ) (v : QState (Fin D)) :
    (∑ j : Fin D, v j • sinEnvelopeHHLIdeal M hM eig V d B j) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
        (fun p : Fin 3 × Fin D =>
          ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
            (B *ᵥ v)) p.2)) := by
  have hcore : (∑ j : Fin D, v j • (fun p : Fin 3 × Fin D =>
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
        (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2)) =
      (fun p : Fin 3 × Fin D =>
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
        (B *ᵥ v)) p.2) := by
    funext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact qls_ideal_pointwise eig V B d p.1 v p.2
  have h2 : (∑ j : Fin D, v j • TensorState (Qatlib.Foundations.PureStateMath.Ket false)
      (fun p : Fin 3 × Fin D =>
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2)) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket false) (∑ j : Fin D, v j • (fun p : Fin 3 × Fin D =>
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2)) :=
    (qls_tensorState_sum_smul_right (Qatlib.Foundations.PureStateMath.Ket false) (fun j => v j) _).symm
  have h1 : (∑ j : Fin D, v j • sinEnvelopeHHLIdeal M hM eig V d B j) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
        (∑ j : Fin D, v j • TensorState (Qatlib.Foundations.PureStateMath.Ket false)
          (fun p : Fin 3 × Fin D =>
            ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2)) := by
    conv_lhs => simp only [sinEnvelopeHHLIdeal]
    rw [← qls_tensorState_sum_smul_right]
  rw [h1, h2, hcore]

private theorem qls_ideal_sk_inner {D : ℕ} (eig : Fin D → ℝ) (V B : Operator D) (d : ℝ)
    (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (j j' : Fin D) :
    (∑ s : Fin 3, ∑ k : Fin D,
        (starRingEnd ℂ)
          (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k) = if j = j' then (1 : ℂ) else 0 := by
  have hcol : ∀ (s : Fin 3) (w : QState (Fin D)),
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ w) =
        V *ᵥ (fun i => sinEnvelopeHVector d (eig i) s * (Vᴴ *ᵥ w) i) := by
    intro s w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  have hterm : ∀ (s : Fin 3),
      (∑ k : Fin D,
          (starRingEnd ℂ)
            (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
          ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k) =
        ∑ i : Fin D, ((‖sinEnvelopeHVector d (eig i) s‖ ^ 2 : ℝ) : ℂ) *
          ((starRingEnd ℂ) ((Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i) * (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) i) := by
    intro s
    rw [hcol s (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j),
        hcol s (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')]
    rw [qls_inner_mulVec hV]
    apply Finset.sum_congr rfl
    intro i _
    exact qls_star_mul_scale (sinEnvelopeHVector d (eig i) s) _ _
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Finset.sum_comm]
  have hnorm : ∀ i : Fin D,
      (∑ s : Fin 3, ((‖sinEnvelopeHVector d (eig i) s‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    intro i
    rw [← Complex.ofReal_sum, sin_envelope_h_normalized d (eig i) hd, Complex.ofReal_one]
  have hi : ∀ i : Fin D,
      (∑ s : Fin 3, ((‖sinEnvelopeHVector d (eig i) s‖ ^ 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ) ((Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i) * (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) i)) =
      (starRingEnd ℂ) ((Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i) * (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) i := by
    intro i
    rw [← Finset.sum_mul, hnorm i, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  rw [qls_inner_mulVec (mem_unitaryGroup_adjoint hV), qls_inner_mulVec hB, qls_ket_prod]

private theorem qls_norm_mulVec_unitary {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (w : QState I) :
    (∑ p : I, ‖(U *ᵥ w) p‖ ^ 2) = ∑ p : I, ‖w p‖ ^ 2 := by
  have h := sum_normSq_mulVec_of_mem_unitaryGroup hU w
  simp only [Complex.normSq_eq_norm_sq] at h
  exact h

private theorem qls_actual_column_inner {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (j j' : Fin D) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (starRingEnd ℂ) (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B p j) *
          sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B p j') =
      if j = j' then (1 : ℂ) else 0 := by
  have hword : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
      (sinEnvelopeHHLWord M hM d B) ∈ Matrix.unitaryGroup _ ℂ :=
    (sin_envelope_word_legality_and_counts D M hM d hd B (continuousHHLOracle eig V) hB
      (continuous_hhl_oracle_unitary eig V hV)).2.1
  have hrun : ∀ j : Fin D, sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j =
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeHHLWord M hM d B) *ᵥ
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))) := fun _ => rfl
  simp only [sinEnvelopeActualCleanOp, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun p _ => by rw [hrun j, hrun j'])]
  rw [qls_inner_mulVec hword]
  exact qls_clean_inner (⟨0, by omega⟩ : Fin M) j j'

private theorem qls_ideal_column_inner {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (j j' : Fin D) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (starRingEnd ℂ) (sinEnvelopeIdealCleanOp M hM eig V d B p j) *
          sinEnvelopeIdealCleanOp M hM eig V d B p j') = if j = j' then (1 : ℂ) else 0 := by
  classical
  have hpt : ∀ (z : Fin M) (b : Bool) (s : Fin 3) (k : Fin D),
      (starRingEnd ℂ) (sinEnvelopeIdealCleanOp M hM eig V d B (z, (b, (s, k))) j) *
        sinEnvelopeIdealCleanOp M hM eig V d B (z, (b, (s, k))) j' =
      (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z * Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z) *
        (Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
        ((starRingEnd ℂ)
          (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
          ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
            (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k) := by
    intro z b s k
    simp only [sinEnvelopeIdealCleanOp, Matrix.of_apply, sinEnvelopeHHLIdeal, TensorState,
      map_mul]
    rw [qls_star_ket, qls_star_ket]
    ring
  have hsum : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        (starRingEnd ℂ) (sinEnvelopeIdealCleanOp M hM eig V d B p j) *
          sinEnvelopeIdealCleanOp M hM eig V d B p j') =
      ∑ z : Fin M, ∑ b : Bool, ∑ s : Fin 3, ∑ k : Fin D,
        (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z * Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z) *
          (Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
          ((starRingEnd ℂ)
            (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
            ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    exact hpt z b s k
  rw [hsum]
  have hfac : (∑ z : Fin M, ∑ b : Bool, ∑ s : Fin 3, ∑ k : Fin D,
        (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z * Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z) *
          (Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
          ((starRingEnd ℂ)
            (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
            ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k)) =
      (∑ z : Fin M, Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z * Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M) z) *
        (∑ b : Bool, Qatlib.Foundations.PureStateMath.Ket false b * Qatlib.Foundations.PureStateMath.Ket false b) *
        (∑ s : Fin 3, ∑ k : Fin D,
          (starRingEnd ℂ)
            (((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) k) *
            ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
              (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j')) k) :=
    qls_three_factor_c _ _ _
  rw [hfac, qls_ket_self, qls_ket_self, one_mul, one_mul,
    qls_ideal_sk_inner eig V B d hd hV hB j j']

private theorem qls_actual_isometry {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B)ᴴ *
      (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B) = 1 := by
  ext j j'
  show ∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
      (starRingEnd ℂ) (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B p j) *
        sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B p j'
    = if j = j' then (1 : ℂ) else 0
  exact qls_actual_column_inner hM eig V B d hd hV hB j j'

private theorem qls_ideal_isometry {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (d : ℝ) (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (sinEnvelopeIdealCleanOp M hM eig V d B)ᴴ * (sinEnvelopeIdealCleanOp M hM eig V d B) = 1 := by
  ext j j'
  show ∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
      (starRingEnd ℂ) (sinEnvelopeIdealCleanOp M hM eig V d B p j) *
        sinEnvelopeIdealCleanOp M hM eig V d B p j'
    = if j = j' then (1 : ℂ) else 0
  exact qls_ideal_column_inner hM eig V B d hd hV hB j j'

private theorem qls_cleanOp_bound {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
    (d : ℝ) (hd : 0 < d) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) :
    CleanInputOperatorBound
      (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B -
        sinEnvelopeIdealCleanOp M hM eig V d B) (21 / (d * (M : ℝ))) := by
  intro v
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hη : (0 : ℝ) < 21 / (d * M) := by positivity
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hΦ : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
      (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) ∈ Matrix.unitaryGroup _ ℂ := by
    have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
      wellFormedAdjointCircuit_stepToAdjoint_reverse _ (sin_envelope_phase_circuit_unitary M hM)
    have ho : sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V) ∈
        Matrix.unitaryGroup _ ℂ :=
      tensorGate_unitary (Submonoid.one_mem _)
        (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _)
          (continuous_hhl_oracle_unitary eig V hV)))
    exact hf.evaluate_unitary ho
  have hcalc : (21 : ℝ) / (d * (21 / (d * (M : ℝ)))) = (M : ℝ) := by
    field_simp [hd0, hM0] <;> ring
  have hper : ∀ i : Fin D,
      ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖ ^ 2 *
          ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖ ^ 2) ≤
      ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 * (21 / (d * (M : ℝ))) ^ 2 := by
    intro i
    have hflag := sin_envelope_decoded_flag_error M hM (eig i) d (21 / (d * (M : ℝ)))
      (heig i).1 (heig i).2 hd hη hcalc.le
    exact mul_le_mul_of_nonneg_left hflag (sq_nonneg _)
  have htotal : (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖ ^ 2 *
          ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖ ^ 2)) ≤
      (21 / (d * (M : ℝ))) ^ 2 * ∑ i : Fin D, ‖v i‖ ^ 2 := by
    have h1 : (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖ ^ 2 *
          ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖ ^ 2)) ≤
        ∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 * (21 / (d * (M : ℝ))) ^ 2 :=
      Finset.sum_le_sum fun i _ => hper i
    have h2 : (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2 * (21 / (d * (M : ℝ))) ^ 2) =
        (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2) * (21 / (d * (M : ℝ))) ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    have h3 : (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2) = ∑ i : Fin D, ‖v i‖ ^ 2 :=
      qls_beta_total V B v hV hB
    have h4 : (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ v)) i‖ ^ 2) * (21 / (d * (M : ℝ))) ^ 2 =
        (21 / (d * (M : ℝ))) ^ 2 * ∑ i : Fin D, ‖v i‖ ^ 2 := by
      rw [h3]; ring
    exact h1.trans (le_of_eq (h2.trans h4))
  have hws := qls_workspace_diff hM eig V B v d hd hV
  rw [qls_cleanOp_diff_mulVec, qls_run_sum, qls_ideal_sum, hws]
  simp only [qls_normVec_sqrt]
  rw [qls_norm_mulVec_unitary (mem_unitaryGroup_adjoint hΦ),
    qls_diff_parseval eig V B v d hV]
  have hs := Real.sqrt_le_sqrt htotal
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη.le] at hs
  exact hs

theorem clause59 :
    (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (d : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) → 21 ≤ d * (M : ℝ) →

        ((sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B)ᴴ *
            (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B) = 1 ∧
          (sinEnvelopeIdealCleanOp M hM eig V d B)ᴴ *
            (sinEnvelopeIdealCleanOp M hM eig V d B) = 1 ∧

          CleanInputOperatorBound
            (sinEnvelopeActualCleanOp M hM (continuousHHLOracle eig V) d B -
              sinEnvelopeIdealCleanOp M hM eig V d B) (21 / (d * (M : ℝ))))) ∧

      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        21 / (d * η) ≤ (M : ℝ) →
        ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
            sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η) ∧

      Qatlib.Concepts.HhlAlgorithms.GridExactHHL.SpecRestrictedSubgoal := by
  refine ⟨?_, ?_, ?_⟩
  · intro D M hM eig V B d hV hB hd heig hbudget
    exact ⟨qls_actual_isometry hM eig V B d hd hV hB,
      qls_ideal_isometry hM eig V B d hd hV hB,
      qls_cleanOp_bound hM eig V B d hd hV hB heig⟩
  · intro D M hM eig V B j d η hV hB hd hη hη1 heig hbudget
    exact sin_envelope_hhl_full_workspace_error M hM eig V B j d η hV hB hd hη hη1 heig hbudget
  · exact Qatlib.Concepts.HhlAlgorithms.GridExactHHL.specRestrictedSubgoal

set_option maxHeartbeats 1000000
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
noncomputable def coarseSparseSynthesis (S : SparseAccessSystem) (hw : qlsBitWidth S.dim < S.wireCount) :
    SparseHamiltonianSynthesis S :=
  ⟨[.local [.inl (⟨qlsBitWidth S.dim,hw⟩,PauliX)]],
    [.local [.inl (⟨qlsBitWidth S.dim,hw⟩,PauliX)]]⟩

theorem coarseSparseSynthesis_matrix (S : SparseAccessSystem)
    (hw : qlsBitWidth S.dim < S.wireCount) :
    (coarseSparseSynthesis S hw).matrix S (coarseSparseSynthesis S hw).forward =
      wireGate S.wireCount ⟨qlsBitWidth S.dim,hw⟩ PauliX := by
  simp [coarseSparseSynthesis,SparseHamiltonianSynthesis.matrix,sparsePipelineMatrix,
    sparseStepMatrix,reflectionProgramMatrix,reflectionGateMatrix]

theorem coarseSparseSynthesis_zero_corner (S : SparseAccessSystem)
    (hw : qlsBitWidth S.dim < S.wireCount) :
    qlsCompressMatrix (qlsDataEmbed S.dim S.wireCount)
      ((coarseSparseSynthesis S hw).matrix S (coarseSparseSynthesis S hw).forward) = 0 := by
  rw [coarseSparseSynthesis_matrix]
  ext i j
  simp only [qlsCompressMatrix,Matrix.of_apply,wireGate_apply]
  simp [qlsDataEmbed,PauliX,permMatrix]

theorem coarseSparseSynthesis_implements (S : SparseAccessSystem)
    (hw : qlsBitWidth S.dim < S.wireCount) (eig : Fin S.dim → ℝ) (V : Operator S.dim)
    (hV : V ∈ Matrix.unitaryGroup _ ℂ) :
    SparseHamiltonianSynthesis.ImplementsAt S (coarseSparseSynthesis S hw) eig V 0 := by
  intro _
  change ‖qlsCompressMatrix _ ((coarseSparseSynthesis S hw).matrix S
    (coarseSparseSynthesis S hw).forward)-continuousHHLOracle eig V‖ ≤ (1/2:ℝ)^0 ∧
    ‖qlsCompressMatrix _ ((coarseSparseSynthesis S hw).matrix S
      (coarseSparseSynthesis S hw).forward)-(continuousHHLOracle eig V)ᴴ‖ ≤ (1/2:ℝ)^0
  rw [coarseSparseSynthesis_zero_corner]
  simp only [zero_sub,norm_neg,pow_zero,Matrix.l2_opNorm_conjTranspose]
  exact ⟨l2_norm_unitary_le_one (continuous_hhl_oracle_unitary eig V hV),
    l2_norm_unitary_le_one (continuous_hhl_oracle_unitary eig V hV)⟩

theorem instance_dependent_sparse_budget (S : SparseAccessSystem) (Y : SparseHamiltonianSynthesis S)
    (s k : ℕ) : SparseHamiltonianSynthesis.BudgetBounded S Y s k := by
  let f := sparsePipelineLedger S.data Y.forward
  let b := sparsePipelineLedger S.data Y.backward
  let c := f.positionCalls+f.valueCalls+f.elementaryGates+f.classicalBitOps+
    b.positionCalls+b.valueCalls+b.elementaryGates+b.classicalBitOps+S.wireCount
  have hc : c ≤ c*(s+1)^2 := Nat.le_mul_of_pos_right c (by positivity)
  refine ⟨c,0,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [pow_zero,mul_one]
  all_goals dsimp only [c,f,b] at hc ⊢
  all_goals omega

theorem sparse_spectral_certificate (S : SparseAccessSystem) (hS : S.data.matrix.IsHermitian) :
    ∃ (eig : Fin S.dim → ℝ) (V : Operator S.dim),
      V ∈ Matrix.unitaryGroup _ ℂ ∧ continuousHHLMatrix eig V = S.data.matrix := by
  refine ⟨hS.eigenvalues,hS.eigenvectorUnitary,?_,?_⟩
  · exact hS.eigenvectorUnitary.property
  · exact hS.spectral_theorem.symm

theorem evaluate_contraction {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : ‖U‖ ≤ 1) (cs : List (AdjointStep I))
    (hcs : WellFormedAdjointCircuit cs) : ‖evaluate U cs‖ ≤ 1 := by
  induction cs with
  | nil => exact l2_norm_one_le
  | cons c cs ih =>
    have ht := (WellFormedAdjointCircuit.cons_iff c cs).mp hcs |>.2
    have hi := ih ht
    have hc : ‖instructionMatrix U c‖ ≤ 1 := by
      cases c with
      | gate A => exact l2_norm_unitary_le_one (hcs A (by simp))
      | forward => exact hU
      | backward => simpa only [instructionMatrix,Matrix.l2_opNorm_conjTranspose] using! hU
    exact (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul hc hi (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem zero_control_contraction {I : Type} [Fintype I] [DecidableEq I] :
    ‖controlOracle (0 : Matrix I I ℂ)‖ ≤ 1 := by
  have he : (controlOracle (0 : Matrix I I ℂ))ᴴ * controlOracle 0 = controlOracle 0 := by
    rw [controlOracle_adjoint,Matrix.conjTranspose_zero,controlOracle_mul,Matrix.zero_mul]
  have hn := CStarRing.norm_star_mul_self (x := controlOracle (0 : Matrix I I ℂ))
  rw [Matrix.star_eq_conjTranspose,he] at hn
  nlinarith [norm_nonneg (controlOracle (0 : Matrix I I ℂ))]

theorem zero_sin_oracle_contraction (D M : ℕ) :
    ‖sinEnvelopeOracleLift (D := D) (M := M) 0‖ ≤ 1 := by
  simp only [sinEnvelopeOracleLift,TensorGate,Matrix.kronecker_zero]
  rw [l2_norm_kronecker]
  exact (mul_le_mul l2_norm_one_le zero_control_contraction (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem coarse_sin_run_norm (D M : ℕ) (hM : 2 ≤ M) (B : Operator D) (j : Fin D)
    (d : ℝ) (hd : 0 < d) (hB : B ∈ Matrix.unitaryGroup _ ℂ) :
    ‖toEuclidean_fromVec (qlsSynthAccessRun M hM 0 d B j)‖ ≤ 1 := by
  have hw := (sin_envelope_word_legality_and_counts D M hM d hd B 1 hB (by simp)).1
  have hn := evaluate_contraction (sinEnvelopeOracleLift (D := D) (M := M) 0)
    (zero_sin_oracle_contraction D M) (sinEnvelopeHHLWord M hM d B) hw
  have hi := l2_norm_mulVec_fromVec_le
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) 0) (sinEnvelopeHHLWord M hM d B))
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j))))
  have hk {I : Type} [Fintype I] [DecidableEq I] (i : I) :
      ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket i)
  simp only [tensorState_l2_norm,hk,mul_one] at hi
  exact hi.trans hn

theorem coarse_sin_transport (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup _ ℂ) (hB : B ∈ Matrix.unitaryGroup _ ℂ)
    (hd : 0 < d) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1/4) (hbudget : 21/(d*η) ≤ (M:ℝ)) :
    ‖toEuclidean_fromVec (qlsSynthAccessRun M hM 0 d B j -
      sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤
        η+(4*(M-1)+6)*(1/2:ℝ)^0*qlsSynthAccessFactor M 0 := by
  have hdM : 21 ≤ d*(M:ℝ) := by
    have hb := (div_le_iff₀ (mul_pos hd hη)).mp hbudget
    have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hiso : IsIsometry (sinEnvelopeIdealCleanOp M hM eig V d B) :=
    (clause59.1 D M hM eig V B d hV hB hd heig hdM).2.1
  have he : sinEnvelopeIdealCleanOp M hM eig V d B *ᵥ Qatlib.Foundations.PureStateMath.Ket j =
      sinEnvelopeHHLIdeal M hM eig V d B j := by
    ext p
    simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,sinEnvelopeIdealCleanOp,mul_ite]
  have hn := isometry_mulVec_norm hiso (Qatlib.Foundations.PureStateMath.Ket j)
  rw [he,(normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)] at hn
  have hr := coarse_sin_run_norm D M hM B j d hd hB
  have ht := norm_sub_le (toEuclidean_fromVec (qlsSynthAccessRun M hM 0 d B j))
    (toEuclidean_fromVec (sinEnvelopeHHLIdeal M hM eig V d B j))
  have he' : toEuclidean_fromVec (qlsSynthAccessRun M hM 0 d B j - sinEnvelopeHHLIdeal M hM eig V d B j) =
      toEuclidean_fromVec (qlsSynthAccessRun M hM 0 d B j) -
        toEuclidean_fromVec (sinEnvelopeHHLIdeal M hM eig V d B j) := rfl
  rw [he']
  have hp : (1:ℝ) ≤ 2^(4*(M-1)+6) := one_le_pow₀ (by norm_num)
  simp only [pow_zero,mul_one,qlsSynthAccessFactor] at hp ⊢
  norm_num only [pow_zero,one_add_one_eq_two] at ⊢
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hc : (6:ℝ) ≤ 4*((M:ℝ)-1)+6 := by linarith only [hMr]
  have hprod : (6:ℝ) ≤ (4*((M:ℝ)-1)+6)*2^(4*(M-1)+6) :=
    hc.trans (le_mul_of_one_le_right (by linarith only [hc]) hp)
  linarith only [ht,hn,hr,hprod,hη]

theorem clause54 : (
∀ (S : SparseAccessSystem) (s : ℕ), S.Legal s →
    ∃ (eig : Fin S.dim → ℝ) (V : Operator S.dim)
      (Y : SparseHamiltonianSynthesis S) (k : ℕ),

      V ∈ Matrix.unitaryGroup (Fin S.dim) ℂ ∧
        continuousHHLMatrix eig V = S.data.matrix ∧

      SparseHamiltonianSynthesis.ImplementsAt S Y eig V k ∧

      SparseHamiltonianSynthesis.BudgetBounded S Y s k ∧

      (∀ (M : ℕ) (hM : 2 ≤ M) (B : Operator S.dim) (j : Fin S.dim) (d η : ℝ),
        B ∈ Matrix.unitaryGroup (Fin S.dim) ℂ → 0 < d → 0 < η → η ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) → 21 / (d * η) ≤ (M : ℝ) →
        ‖toEuclidean_fromVec (qlsSynthAccessRun M hM
            (qlsCompressMatrix (qlsDataEmbed S.dim S.wireCount) (Y.matrix S Y.forward))
            d B j - sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤
          η + (4 * (M - 1) + 6) * (1 / 2 : ℝ) ^ k * qlsSynthAccessFactor M k) ∧

      (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B W : Operator D)
          (j : Fin D) (d η : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ →
        B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        W ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < η → η ≤ 1 → (∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) →
        4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) →
        ‖toEuclidean_fromVec (uniformHHLRun M hM W d B j -
            uniformHHLIdeal M hM eig V d B j)‖ ≤
            η + 2 * (M - 1 : ℕ) * ‖W - continuousHHLOracle eig V‖)
) := by
  intro S s hS
  obtain ⟨eig,V,hV,hmat⟩ := sparse_spectral_certificate S hS.2.2.2.1.1
  have hw : qlsBitWidth S.dim < S.wireCount := by have := hS.2.1; omega
  refine ⟨eig,V,coarseSparseSynthesis S hw,0,hV,hmat,
    coarseSparseSynthesis_implements S hw eig V hV,
    instance_dependent_sparse_budget S _ s 0,?_,?_⟩
  · intro M hM B j d η hB hd hη hη1 heig hb
    rw [coarseSparseSynthesis_zero_corner]
    exact coarse_sin_transport S.dim M hM eig V B j d η hV hB hd hη hη1 heig hb
  · exact uniform_offgrid_hhl_actual_unitary_access_noise

noncomputable def canonicalSignedFilter : SignedSinEnvelopeFilter where
  filterF d θ := (if θ < 0 then -1 else 1) * sinEnvelopeFilterF d |θ|
  filterG d θ := sinEnvelopeFilterG d |θ|

theorem canonicalSignedFilter_consistent : canonicalSignedFilter.Consistent := by
  have hz (d : ℝ) (hd : 0 < d) : sinEnvelopeFilterF d 0 = 0 ∧ sinEnvelopeFilterG d 0 = 1/2 := by
    simp [sinEnvelopeFilterF,sinEnvelopeFilterG,show ¬ 2*d ≤ 0 by linarith,not_le_of_gt hd]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro d θ hd
    by_cases h0 : θ = 0
    · subst θ
      simp [canonicalSignedFilter,(hz d hd).1]
    · by_cases hn : θ < 0
      · simp [canonicalSignedFilter,abs_neg,hn,show ¬ -θ < 0 by linarith]
      · simp [canonicalSignedFilter,abs_neg,hn,show -θ < 0 by rcases lt_or_gt_of_ne h0 with h | h <;> linarith]
  · intro d θ hd
    simp [canonicalSignedFilter]
  · intro d hd
    simpa [canonicalSignedFilter] using! hz d hd
  · intro d θ hd hθ
    simp [canonicalSignedFilter,abs_of_nonneg hθ,not_lt_of_ge hθ]
  · intro d θ hd
    have h := sin_envelope_filter_bounded d |θ| hd
    change sinEnvelopeFilterF d |θ|^2+sinEnvelopeFilterG d |θ|^2 ≤ 1/4 at h
    dsimp only [canonicalSignedFilter]
    split_ifs <;> nlinarith only [h]

open Matrix
open scoped Classical Matrix.Norms.L2Operator

noncomputable def signedWellPhase (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => if i=1 ∧ θ<0 then -1 else 1)

theorem signedWellPhase_unitary (θ : ℝ) : signedWellPhase θ ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  simp only [signedWellPhase,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i=1 ∧ θ<0 <;> simp [hi]

noncomputable def canonicalSignedProgram : SignedSinEnvelopeProgram where
  filter := canonicalSignedFilter
  rotation d θ := signedWellPhase θ * sinEnvelopeFlagRotation d |θ|

theorem canonicalSignedProgram_rotation (d θ : ℝ) (hd : 0<d) :
    canonicalSignedProgram.rotation d θ ∈ Matrix.unitaryGroup _ ℂ ∧
    canonicalSignedProgram.rotation d θ *ᵥ Qatlib.Foundations.PureStateMath.Ket (0:Fin 3) = canonicalSignedProgram.filter.hVector d θ := by
  have hu := sin_envelope_flag_rotation_unitary_and_column d |θ| hd
  refine ⟨(Matrix.unitaryGroup _ ℂ).mul_mem (signedWellPhase_unitary θ) hu.1,?_⟩
  change (signedWellPhase θ * sinEnvelopeFlagRotation d |θ|) *ᵥ Qatlib.Foundations.PureStateMath.Ket (0:Fin 3) = _
  rw [← Matrix.mulVec_mulVec,hu.2]
  ext i
  fin_cases i <;> by_cases hθ : θ<0 <;>
    simp [signedWellPhase,Matrix.mulVec_diagonal,canonicalSignedProgram,canonicalSignedFilter,
      SignedSinEnvelopeFilter.hVector,sinEnvelopeHVector,hθ]

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

theorem canonicalSignedProgram_word_laws (D M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (B : Operator D) (hd : 0<d) (hB : B ∈ Matrix.unitaryGroup _ ℂ) :
    WellFormedAdjointCircuit (canonicalSignedProgram.word M hM d B) ∧
    adjointQueryCount (canonicalSignedProgram.word M hM d B) = 2*(M-1) ∧
    adjointGateCount (canonicalSignedProgram.word M hM d B) = 4*(M-1)+6 := by
  have hw := (sin_envelope_word_legality_and_counts D M hM d hd B 1 hB (Submonoid.one_mem _)).1
  have hf : canonicalSignedProgram.flagGate (D := D) (M := M) d ∈ Matrix.unitaryGroup _ ℂ := by
    apply (relabelGate_mem_unitaryGroup _ _).mpr
    exact tensorGate_unitary (blockDiag_unitary _ fun z =>
      (canonicalSignedProgram_rotation d (sinEnvelopeDecode M z) hd).1) (Submonoid.one_mem _)
  have hfl : sinEnvelopeLiftGate (canonicalSignedProgram.flagGate (D := D) (M := M) d)
      ∈ Matrix.unitaryGroup _ ℂ := by
    apply (relabelGate_mem_unitaryGroup _ _).mpr
    exact tensorGate_unitary (Submonoid.one_mem _) hf
  refine ⟨?_,?_,?_⟩
  · simp only [SignedSinEnvelopeProgram.word, sinEnvelopeHHLWord,
      WellFormedAdjointCircuit.append_iff, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.nil,and_true] at hw ⊢
    exact ⟨⟨⟨hw.1.1.1,hfl⟩,hw.1.2⟩,hw.2⟩
  · have h := (sin_envelope_forward_word_counts (I := Fin 3 × Fin D) M hM).1
    simp only [SignedSinEnvelopeProgram.word,adjointQueryCount_append,
      adjointQueryCount_adjointCircuit,adjointQueryCount,h]
    omega
  · have h := (sin_envelope_forward_word_counts (I := Fin 3 × Fin D) M hM).2
    simp only [SignedSinEnvelopeProgram.word,adjointGateCount_append,
      adjointGateCount_adjointCircuit,adjointGateCount,h]
    omega

theorem signed_well_target_half (P : SignedSinEnvelopeProgram) (hc : P.filter.Consistent)
    (M : ℕ) (hM : 2 ≤ M) :
    P.wellTarget M hM (fun _ : Fin 1 => (1/4:ℝ)) 1 (1/8) 1 0 =
      (1/2:ℂ) • Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩,false,1,0) := by
  have hf := (hc.2.2.2.1 (1/8) (1/4) (by norm_num) (by norm_num)).1
  norm_num [sinEnvelopeFilterF] at hf
  simp only [one_div] at hf
  ext ⟨z,b,s,i⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  cases b <;> fin_cases s <;>
    simp [SignedSinEnvelopeProgram.wellTarget,qlsWellBranch,SignedSinEnvelopeProgram.ideal,
      TensorState,Qatlib.Foundations.PureStateMath.Ket,Matrix.mulVec,dotProduct,SignedSinEnvelopeFilter.hVector,hf]

theorem signed_well_target_norm (P : SignedSinEnvelopeProgram) (hc : P.filter.Consistent)
    (M : ℕ) (hM : 2 ≤ M) :
    ‖toEuclidean_fromVec (P.wellTarget M hM (fun _ : Fin 1 => (1/4:ℝ)) 1 (1/8) 1 0)‖ = 1/2 := by
  rw [signed_well_target_half P hc M hM]
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket ((⟨0,by omega⟩ : Fin M),false,(1:Fin 3),(0:Fin 1)))‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _)
  change ‖(1/2:ℂ) • toEuclidean_fromVec
      (Qatlib.Foundations.PureStateMath.Ket ((⟨0,by omega⟩ : Fin M),false,(1:Fin 3),(0:Fin 1)))‖ = 1/2
  rw [norm_smul,hk]
  norm_num

theorem quarter_scalar_overlap : leastSquaresOverlap
    (continuousHHLMatrix (fun _ : Fin 1 => (1/4:ℝ)) 1)
    ((1 : Operator 1) *ᵥ Qatlib.Foundations.PureStateMath.Ket 0) = 1 := by
  let A : Operator 1 := continuousHHLMatrix (fun _ : Fin 1 => (1/4:ℝ)) 1
  have hi : A * ((4:ℂ) • (1 : Operator 1)) = 1 := by
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i
    subst j
    norm_num [A,continuousHHLMatrix,Matrix.mul_apply,Fin.sum_univ_one]
  have hr : A * matrixPseudoinverse A = 1 := by
    have h := congrArg (fun B : Operator 1 => B*((4:ℂ) • (1 : Operator 1)))
      (mul_matrixPseudoinverse_mul A)
    (try dsimp only at h)
    rw [Matrix.mul_assoc (A * matrixPseudoinverse A),hi,Matrix.mul_one] at h
    exact h
  change ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector
    ((A*matrixPseudoinverse A) *ᵥ ((1 : Operator 1)*ᵥKet 0))‖ = 1
  rw [hr,Matrix.one_mulVec,Matrix.one_mulVec]
  exact (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket (0:Fin 1))

theorem not_clause60 : ¬ (
∃ (P : SignedSinEnvelopeProgram) (C : ℕ),

    P.filter.Consistent ∧
    (∀ (d θ : ℝ), 0 < d →
      P.rotation d θ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
        P.rotation d θ *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) = P.filter.hVector d θ) ∧

    (∀ (D M : ℕ) (hM : 2 ≤ M) (d : ℝ) (B U : Operator D),
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → U ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 < d →
      WellFormedAdjointCircuit (P.word M hM d B) ∧
        adjointQueryCount (P.word M hM d B) = 2 * (M - 1) ∧
        adjointGateCount (P.word M hM d B) = 4 * (M - 1) + 6) ∧

    (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
        (d : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 < d → 2 * d ≤ 1 / 4 →
      (∀ i, eig i = 0 ∨ ((d : ℝ) ≤ |eig i| ∧ |eig i| ≤ 1 / 4)) →
      (C : ℝ) ≤ d * (M : ℝ) →
      ‖toEuclidean_fromVec (P.run M hM (continuousHHLOracle eig V) d B j -
          P.ideal M hM eig V d B j)‖ ≤ (C : ℝ) / (d * (M : ℝ))) ∧

    (∀ (D M k : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B W : Operator D)
        (j : Fin D) (d : ℚ) (δ : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      W ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 2 * (d : ℝ) ≤ 1 / 4 →
      (∀ i, eig i = 0 ∨ (2 * (d : ℝ) ≤ |eig i| ∧ |eig i| ≤ 1 / 4)) →
      (C : ℝ) ≤ (d : ℝ) * (M : ℝ) → ‖W - continuousHHLOracle eig V‖ ≤ δ →
      let E := (C : ℝ) / ((d : ℝ) * (M : ℝ)) + 32 / 2 ^ k +
          2 * ((M - 1 : ℕ) : ℝ) * δ
      let tau :=
          leastSquaresOverlap (continuousHHLMatrix eig V)
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)
      let out := P.run M hM W (d : ℝ) B j
      let S := sinEnvelopeWellSetCorrected D M
      E < (d : ℝ) * tau →
        ((d : ℝ) * tau - E) ^ 2 ≤ MeasureProb out S ∧
          ‖toEuclidean_fromVec (PostMeasure out S -
              P.wellTarget M hM eig V (d : ℝ) B j)‖ ≤ 2 * E / ((d : ℝ) * tau)) ∧

    (∀ (D M k : ℕ) (hM : 2 ≤ M) (U B : Operator D) (j : Fin D) (d : ℚ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 < d →
      ‖toEuclidean_fromVec (rationalHHLRun M hM U d k B j -
          uniformHHLRun M hM U (d : ℝ) B j)‖ ≤ 32 / 2 ^ k) ∧

    (∀ (D M bits : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B W : Operator D)
        (j : Fin D) (d : ℚ) (eta δ : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      W ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < eta → eta ≤ 1 → 0 ≤ δ →
      (∀ i, eig i = 0 ∨ ((d : ℝ) ≤ |eig i| ∧ |eig i| ≤ 1 / 4)) →
      4096 / ((d : ℝ) ^ 2 * eta ^ 4) ≤ (M : ℝ) →
      ‖W - continuousHHLOracle eig V‖ ≤ δ →
      let E := eta + 32 / 2 ^ bits + 2 * ((M - 1 : ℕ) : ℝ) * δ
      let tau :=
          leastSquaresOverlap (continuousHHLMatrix eig V)
          (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)
      let out := rationalHHLRun M hM W d bits B j
      E < (d : ℝ) * tau →
        ((d : ℝ) * tau - E) ^ 2 ≤ MeasureProb out (flagSuccessSet D M) ∧
          ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
              uniformHHLSolutionTarget M hM eig V B j)‖ ≤ 2 * E / ((d : ℝ) * tau))
) := by
  intro h
  obtain ⟨P,C,hc,_,_,_,hls,_,_⟩ := h
  let M := 8192*(C+1)
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hM0 : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hC : (0:ℝ) ≤ C := Nat.cast_nonneg _
  have hbudget : (C:ℝ) ≤ (1/8)*(M:ℝ) := by
    dsimp [M]
    push_cast
    nlinarith only [hC]
  have hpart : (C:ℝ)/((1/8)*(M:ℝ)) ≤ 1/1024 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (1/8)*(M:ℝ))).mpr
    dsimp [M]
    push_cast
    nlinarith only [hC]
  have hh := hls 1 M 16 hM (fun _ : Fin 1 => (1/4:ℝ)) 1 1
    (continuousHHLOracle (fun _ : Fin 1 => (1/4:ℝ)) 1) 0 (1/8) 0
    (by simp) (by simp) (continuous_hhl_oracle_unitary _ _ (by simp))
    (by norm_num) (by norm_num) (by intro i; right; norm_num)
    (by simpa using! hbudget) (by simp)
  (try dsimp only at hh)
  rw [quarter_scalar_overlap] at hh
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_mul,add_zero,mul_one] at hh
  have he : (C:ℝ)/((1/8)*(M:ℝ)) + 32/(2:ℝ)^16 < 1/8 := by
    norm_num
    linarith only [hpart]
  obtain ⟨hs,hd⟩ := hh (by norm_num at he ⊢; exact he)
  let out := P.run M hM (continuousHHLOracle (fun _ : Fin 1 => (1/4:ℝ)) 1) (1/8) 1 0
  let S := sinEnvelopeWellSetCorrected 1 M
  have hp : 0 < MeasureProb out S := by
    apply lt_of_lt_of_le _ hs
    apply sq_pos_of_pos
    norm_num at he ⊢
    linarith only [he]
  have hn : ‖toEuclidean_fromVec (PostMeasure out S)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_postMeasure hp)
  have ht := signed_well_target_norm P hc M hM
  have hgap := abs_norm_sub_norm_le (toEuclidean_fromVec (PostMeasure out S))
    (toEuclidean_fromVec (P.wellTarget M hM (fun _ : Fin 1 => (1/4:ℝ)) 1 (1/8) 1 0))
  rw [hn,ht] at hgap
  norm_num at hgap
  change ‖toEuclidean_fromVec (PostMeasure out S) -
    toEuclidean_fromVec (P.wellTarget M hM (fun _ : Fin 1 => (1/4:ℝ)) 1 (1/8) 1 0)‖ ≤ _ at hd
  norm_num at hd
  nlinarith only [hgap,hd,hpart]
end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
