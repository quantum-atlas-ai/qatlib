/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation16Stat
import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Simu
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

theorem reducedState_fiber_outer {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (v : QState I) :
    ReducedState (vecOuter (TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) v))=vecOuter v := by
  ext i j
  simp [ReducedState, vecOuter, TensorState, Qatlib.Foundations.PureStateMath.Ket]

theorem vecOuter_mulVec {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (v : QState I) : vecOuter (A *ᵥ v)=A*vecOuter v*Aᴴ := by
  change Matrix.vecMulVec (A *ᵥ v) (star (A *ᵥ v))=
    A*Matrix.vecMulVec v (star v)*Aᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem oaa_traceNorm_conjugation_error {I : Type*} [Fintype I] [DecidableEq I]
    (C U ρ : Matrix I I ℂ) (hC : ‖C‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    Matrix.traceNorm (C*ρ*Cᴴ-U*ρ*Uᴴ) ≤ 2*‖C-U‖*Matrix.traceNorm ρ := by
  have he : C*ρ*Cᴴ-U*ρ*Uᴴ=(C-U)*ρ*Cᴴ+U*ρ*(C-U)ᴴ := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  rw [he]
  have ha : Matrix.traceNorm ((C-U)*ρ*Cᴴ) ≤ ‖C-U‖*Matrix.traceNorm ρ := by
    calc
      _ ≤ ‖C-U‖*Matrix.traceNorm ρ*‖Cᴴ‖ :=
        (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _) (norm_nonneg _))
      _ ≤ ‖C-U‖*Matrix.traceNorm ρ*1 := mul_le_mul_of_nonneg_left
        (by simpa only [Matrix.l2_opNorm_conjTranspose] using hC)
          (mul_nonneg (norm_nonneg _) (Matrix.traceNorm_nonneg _))
      _ = _ := mul_one _
  have hb : Matrix.traceNorm (U*ρ*(C-U)ᴴ) ≤ Matrix.traceNorm ρ*‖C-U‖ := by
    calc
      _ ≤ ‖U‖*Matrix.traceNorm ρ*‖(C-U)ᴴ‖ :=
        (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _) (norm_nonneg _))
      _ ≤ 1*Matrix.traceNorm ρ*‖(C-U)ᴴ‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hU (Matrix.traceNorm_nonneg _)) (norm_nonneg _)
      _ = _ := by rw [one_mul, Matrix.l2_opNorm_conjTranspose]
  exact (Matrix.traceNorm_add_le _ _).trans (by nlinarith)

theorem oaa_cubic_contraction {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ)
    (j₀ : J) (X : Matrix I I ℂ) (s : ℝ) (hW : IsBlockEncoding W j₀ X s) :
    ‖((3/s : ℝ) : ℂ) • X-((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)‖ ≤ 1 := by
  let O := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  have hp := isOrthogonalProjector_fiberProjector (I := I) j₀
  have hO : O ∈ Matrix.unitaryGroup (J × I) ℂ :=
    obliviousAmplitudeAmplification_mem_unitary _ _
      ⟨hp.1, hp.2⟩ hW.1
  have he := projected_obliviousAmplitudeAmplification_blockEncoding W j₀ X s hW
  rw [Matrix.mul_assoc, fiberProjector_mul_mul_corner] at he
  have hc : BlockCorner O j₀=((3/s : ℝ) : ℂ) • X-((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X) := by
    ext i j
    have hv := congrArg (fun A : Matrix (J × I) (J × I) ℂ => A (j₀,i) (j₀,j)) he
    simpa only [fiberEmbed_apply, and_self, if_true] using hv
  rw [← hc, ← compress_encodingFiber_blockCorner]
  exact l2_norm_compress_le_one (encodingFiber_isIsometry j₀) hO (encodingFiber_isIsometry j₀)

theorem equation16 : Equation16 := by
  intro J I _ _ _ _ W j₀ X U s δ₁ δ₂ hW hU hX hs hd hδ ψ hψ
  let C : Matrix I I ℂ := ((3/s : ℝ) : ℂ) • X-((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)
  have hC : ‖C‖ ≤ 1 := oaa_cubic_contraction W j₀ X s hW
  have herror : ‖C-U‖ ≤ (15+12*δ₁+4*δ₁^2)*δ₁+15*δ₂ :=
    oaa_cubic_operator_error_le X U s δ₁ δ₂ hU hX hs hd hδ
  have hρ : Matrix.traceNorm (vecOuter ψ)=1 := by
    have hp : (vecOuter ψ).PosSemidef := outerProduct_posSemidef ψ
    have ht : Matrix.trace (vecOuter ψ)=1 := by
      change Matrix.trace (outerProduct ψ)=1
      rw [trace_outerProduct, hψ]
      norm_num
    have hh := hp.traceNorm_eq_trace
    rw [ht] at hh
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_one] using! hh
  rw [equation14 J I W j₀ X s hW ψ, reducedState_fiber_outer, reducedState_fiber_outer,
    vecOuter_mulVec, vecOuter_mulVec]
  have hh := oaa_traceNorm_conjugation_error C U (vecOuter ψ) hC (l2_norm_unitary_le_one hU)
  rw [hρ, mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left herror (by norm_num))

end Qatlib.Concepts.CoherentSim.ResetDiscard
