/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentationCorrectedStat
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentation
import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation16Simu
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

private theorem reduced_eq_traceLeft (σ : Matrix (J × I) (J × I) ℂ) :
    ReducedState σ = σ.traceLeft := rfl

private theorem amplified_unitary (W : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (hW : W ∈ Matrix.unitaryGroup (J × I) ℂ) :
    ObliviousAmplitudeAmplification (FiberProjector j₀) W ∈ Matrix.unitaryGroup (J × I) ℂ := by
  have hp := isOrthogonalProjector_fiberProjector (I := I) j₀
  exact obliviousAmplitudeAmplification_mem_unitary _ _ ⟨hp.1,hp.2⟩ hW

private theorem unitary_fiber_trace (O : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (hO : O ∈ Matrix.unitaryGroup (J × I) ℂ) (ρ : Matrix I I ℂ) :
    Matrix.trace (O*AncillaSystemOp (vecOuter (Ket j₀)) ρ*Oᴴ) = Matrix.trace ρ := by
  have hunit : Oᴴ*O=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hO
  have hF := encodingFiber_isIsometry (I := I) j₀
  rw [ancillaSystemOp_ket_eq_fiberEmbed,← encodingFiber_mul_mul_conjTranspose]
  rw [Matrix.trace_mul_comm,Matrix.mul_assoc,← Matrix.mul_assoc Oᴴ,hunit,Matrix.one_mul]
  rw [Matrix.trace_mul_comm,Matrix.mul_assoc,hF,Matrix.mul_one]

theorem resetDiscardStepCorrected_density (W : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (hW : W ∈ Matrix.unitaryGroup (J × I) ℂ) (ρ : Matrix I I ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) :
    (ResetDiscardStepCorrected W j₀ ρ).PosSemidef ∧ Matrix.trace (ResetDiscardStepCorrected W j₀ ρ)=1 := by
  let O := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  have hO := amplified_unitary W j₀ hW
  have hp : (O*AncillaSystemOp (vecOuter (Ket j₀)) ρ*Oᴴ).PosSemidef := by
    rw [ancillaSystemOp_ket_eq_fiberEmbed,← encodingFiber_mul_mul_conjTranspose]
    exact (hρ.mul_mul_conjTranspose_same _).mul_mul_conjTranspose_same O
  change (ReducedState _).PosSemidef ∧ Matrix.trace (ReducedState _)=1
  rw [reduced_eq_traceLeft]
  exact ⟨hp.traceLeft,(Matrix.traceLeft_trace _).trans ((unitary_fiber_trace O j₀ hO ρ).trans ht)⟩

private theorem reduced_split (σ : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    ReducedState σ = ReducedState (FiberProjector j₀*σ*FiberProjector j₀)+
      ReducedState ((1-FiberProjector j₀)*σ*(1-FiberProjector j₀)) := by
  have he : (1-FiberProjector j₀)*σ*(1-FiberProjector j₀) =
      σ-FiberProjector j₀*σ-σ*FiberProjector j₀+FiberProjector j₀*σ*FiberProjector j₀ := by noncomm_ring
  rw [he]
  ext i j
  simp only [ReducedState,Matrix.of_apply,Matrix.add_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberProjector_mul,mul_fiberProjector,Matrix.of_apply,Matrix.sub_apply]
  by_cases ha : a=j₀ <;> simp [ha]

theorem resetDiscardStepCorrected_error_from_corner
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ)
    (hW : W ∈ Matrix.unitaryGroup (J × I) ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) :
    Matrix.traceNorm (ResetDiscardStepCorrected W j₀ ρ-U*ρ*Uᴴ) ≤
      2*Matrix.traceNorm (BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀*
        ρ*(BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀)ᴴ-U*ρ*Uᴴ) := by
  let O := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  let σ := O*AncillaSystemOp (vecOuter (Ket j₀)) ρ*Oᴴ
  let C := BlockCorner O j₀
  let F := ReducedState ((1-FiberProjector j₀)*σ*(1-FiberProjector j₀))
  have hO := amplified_unitary W j₀ hW
  have hσ : σ.PosSemidef := by
    dsimp [σ]
    rw [ancillaSystemOp_ket_eq_fiberEmbed,← encodingFiber_mul_mul_conjTranspose]
    exact (hρ.mul_mul_conjTranspose_same _).mul_mul_conjTranspose_same O
  have hQ : (1-FiberProjector (I := I) j₀)ᴴ=1-FiberProjector j₀ := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
    exact congrArg (fun P => 1-P) (isOrthogonalProjector_fiberProjector (I := I) j₀).2
  have hF : F.PosSemidef := by
    change (ReducedState _).PosSemidef
    rw [reduced_eq_traceLeft]
    have hh := hσ.mul_mul_conjTranspose_same (1-FiberProjector j₀)
    rw [hQ] at hh
    exact hh.traceLeft
  have hsplit : ResetDiscardStepCorrected W j₀ ρ = C*ρ*Cᴴ+F := by
    change ReducedState σ = _
    rw [reduced_split σ j₀]
    have hc := resetDiscardStep_eq_corner O j₀ ρ
    change ReducedState (FiberProjector j₀*σ*FiberProjector j₀)=C*ρ*Cᴴ at hc
    rw [hc]
  have htr := (resetDiscardStepCorrected_density W j₀ hW ρ hρ ht).2
  rw [hsplit,Matrix.trace_add] at htr
  have htu : Matrix.trace (U*ρ*Uᴴ)=1 := by
    have hu : Uᴴ*U=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
    rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,hu,Matrix.one_mul,ht]
  have htf : Matrix.trace F = -Matrix.trace (C*ρ*Cᴴ-U*ρ*Uᴴ) := by
    rw [Matrix.trace_sub,htu]
    linear_combination htr
  have hfn : Matrix.traceNorm F = ‖Matrix.trace F‖ := by
    rw [← hF.traceNorm_eq_trace,RCLike.norm_ofReal,
      abs_of_nonneg (Matrix.traceNorm_nonneg F)]
  have hfbound : Matrix.traceNorm F ≤ Matrix.traceNorm (C*ρ*Cᴴ-U*ρ*Uᴴ) := by
    rw [hfn,htf,norm_neg]
    exact Matrix.abs_trace_le_traceNorm _
  rw [hsplit]
  have he : C*ρ*Cᴴ+F-U*ρ*Uᴴ = (C*ρ*Cᴴ-U*ρ*Uᴴ)+F := by abel
  rw [he]
  exact (Matrix.traceNorm_add_le _ _).trans (by linarith only [hfbound])

theorem resetDiscardStepCorrected_corner
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X : Matrix I I ℂ) (s : ℝ)
    (hW : IsBlockEncoding W j₀ X s) :
    BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀ =
      ((3/s:ℝ):ℂ) • X-((4/s^3:ℝ):ℂ) • (X*Xᴴ*X) := by
  have he := projected_obliviousAmplitudeAmplification_blockEncoding W j₀ X s hW
  rw [Matrix.mul_assoc,fiberProjector_mul_mul_corner] at he
  ext i j
  have hh := congrArg (fun A : Matrix (J × I) (J × I) ℂ => A (j₀,i) (j₀,j)) he
  simpa only [fiberEmbed_apply,and_self,if_true] using hh

theorem resetDiscardStepCorrected_error
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (e : ℝ)
    (hW : W ∈ Matrix.unitaryGroup (J × I) ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (herr : ‖BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀-U‖ ≤ e)
    (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) :
    Matrix.traceNorm (ResetDiscardStepCorrected W j₀ ρ-U*ρ*Uᴴ) ≤ 4*e := by
  let O := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  let C := BlockCorner O j₀
  have hC : ‖C‖ ≤ 1 := by
    change ‖BlockCorner O j₀‖ ≤ 1
    rw [← compress_encodingFiber_blockCorner]
    exact l2_norm_compress_le_one (encodingFiber_isIsometry j₀)
      (amplified_unitary W j₀ hW) (encodingFiber_isIsometry j₀)
  have hn : Matrix.traceNorm ρ=1 := by
    have hh := hρ.traceNorm_eq_trace
    rw [ht] at hh
    have hr := congrArg RCLike.re hh
    simpa using hr
  have hc := oaa_traceNorm_conjugation_error C U ρ hC (l2_norm_unitary_le_one hU)
  rw [hn,mul_one] at hc
  have he : Matrix.traceNorm (C*ρ*Cᴴ-U*ρ*Uᴴ) ≤ 2*e :=
    hc.trans (mul_le_mul_of_nonneg_left herr (by norm_num))
  exact (resetDiscardStepCorrected_error_from_corner W j₀ U hW hU ρ hρ ht).trans
    (by linarith only [he])

theorem resetDiscardStepCorrected_iterate_error
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (e : ℝ)
    (hW : W ∈ Matrix.unitaryGroup (J × I) ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (herr : ‖BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀-U‖ ≤ e)
    (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) (r : ℕ) :
    Matrix.traceNorm ((ResetDiscardStepCorrected W j₀)^[r] ρ-U^r*ρ*(Uᴴ)^r) ≤ 4*(r:ℝ)*e := by
  have hd (n : ℕ) : ((ResetDiscardStepCorrected W j₀)^[n] ρ).PosSemidef ∧
      Matrix.trace ((ResetDiscardStepCorrected W j₀)^[n] ρ)=1 := by
    induction n with
    | zero => exact ⟨hρ,ht⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact resetDiscardStepCorrected_density W j₀ hW _ ih.1 ih.2
  induction r with
  | zero => simp
  | succ n ih =>
    let ν := (ResetDiscardStepCorrected W j₀)^[n] ρ
    let μ := U^n*ρ*(Uᴴ)^n
    have he : (ResetDiscardStepCorrected W j₀)^[n+1] ρ-U^(n+1)*ρ*(Uᴴ)^(n+1) =
        (ResetDiscardStepCorrected W j₀ ν-U*ν*Uᴴ)+U*(ν-μ)*Uᴴ := by
      rw [Function.iterate_succ_apply']
      nth_rw 1 [pow_succ']
      rw [pow_succ]
      dsimp [ν,μ]
      noncomm_ring
    rw [he]
    have hs := resetDiscardStepCorrected_error W j₀ U e hW hU herr ν (hd n).1 (hd n).2
    have hn : Matrix.traceNorm (U*(ν-μ)*Uᴴ) ≤ Matrix.traceNorm (ν-μ) :=
      Matrix.traceNorm_sandwich_le (l2_norm_unitary_le_one hU)
        (by rw [Matrix.l2_opNorm_conjTranspose]; exact l2_norm_unitary_le_one hU)
    have hh := (Matrix.traceNorm_add_le _ _).trans (add_le_add hs (hn.trans ih))
    exact hh.trans_eq (by push_cast; ring)

theorem resetDiscardSegmentation : ResetDiscardSegmentationCorrected := by
  intro J I _ _ _ _ W j₀ X U s δ₁ δ₂ r hW hU hX hs hclose hδ ρ hρ ht
  apply resetDiscardStepCorrected_iterate_error W j₀ U _ hW.1 hU _ ρ hρ ht r
  rw [resetDiscardStepCorrected_corner W j₀ X s hW]
  exact oaa_cubic_operator_error_le X U s δ₁ δ₂ hU hX hs hclose hδ
end Qatlib.Concepts.CoherentSim.ResetDiscard
