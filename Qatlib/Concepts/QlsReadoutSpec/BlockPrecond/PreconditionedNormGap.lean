/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioning
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioningPseudoinverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator
variable {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

omit [DecidableEq I] in

theorem solved_outerProduct_norm (B : Matrix I O ℂ) (b : QState O) (hb : Normalized b) :
    ‖B*outerProduct b‖=‖stateVector (B*ᵥb)‖ := by
  have he : B*outerProduct b=Matrix.vecMulVec (B*ᵥb) (star b) := by
    ext i j
    simp only [Matrix.mul_apply,outerProduct_apply,Matrix.vecMulVec_apply,Pi.star_apply]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    rfl
  let x:=stateVector (B*ᵥb)
  let y:=stateVector b
  have hm : (Matrix.toEuclideanLin (𝕜:=ℂ) (m:=I) (n:=O)).symm
      (InnerProductSpace.rankOne ℂ x y).toLinearMap=B*outerProduct b := by
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne,he]
  have hlin : (B*outerProduct b).toEuclideanLin=(InnerProductSpace.rankOne ℂ x y).toLinearMap := by
    rw [← hm,LinearEquiv.apply_symm_apply]
  have hc : ((Matrix.toEuclideanLin (𝕜:=ℂ) (m:=I) (n:=O)).trans LinearMap.toContinuousLinearMap) (B*outerProduct b)=
      InnerProductSpace.rankOne ℂ x y := by
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hlin v
  rw [Matrix.l2_opNorm_def,hc,InnerProductSpace.norm_rankOne]
  have hy : ‖y‖=1 := (normalized_iff_stateVector_norm b).mp hb
  rw [hy,mul_one]

theorem state_complement_norm_le_one (b : QState O) (hb : Normalized b) :
    ‖(1-outerProduct b:Matrix O O ℂ)‖≤1 := by
  have hp:=isOrthogonalProjector_outerProduct hb
  have hpid : outerProduct b*outerProduct b=outerProduct b := hp.1
  have hpstar : (outerProduct b)ᴴ=outerProduct b := hp.2
  apply shared_projector_norm_le_one
  constructor
  · change (1-outerProduct b)*(1-outerProduct b)=1-outerProduct b
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hpid]
    abel
  · change (1-outerProduct b)ᴴ=1-outerProduct b
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hpstar]

theorem preconditioned_pseudoinverse_norm (A : Matrix O I ℂ) (b : QState O) (κ t c s : ℝ)
    (hb : Normalized b) (hκ : 1<κ) (hc : 1< c) (ht : 0< t) (hs : s=t/(c*κ))
    (hgap : ∀ i : Fin (Fintype.card I),0< matrixSingularValues A i → κ⁻¹≤ matrixSingularValues A i)
    (hconsistent : ∃ z : QState I,A*ᵥz=b)
    (hτ : ‖stateVector (matrixPseudoinverse A*ᵥb)‖< c*t) :
    ‖matrixPseudoinverse (stateScaling s b*A)‖≤2*c^2*κ := by
  have hκ0 : 0<κ := by linarith
  have hc0 : 0< c := by linarith
  have hs0 : 0< s := by rw [hs];positivity
  have hA : ‖matrixPseudoinverse A‖≤κ := by
    simpa only [inv_inv] using! matrixPseudoinverse_norm_le (inv_pos.mpr hκ0) hgap
  rw [stateScaling_pseudoinverse_of_consistent A s b hs0.ne' hb hconsistent]
  have he : matrixPseudoinverse A*stateScalingInverse s b=
      ((s:ℝ)⁻¹:ℂ)•(matrixPseudoinverse A*outerProduct b)+matrixPseudoinverse A*(1-outerProduct b) := by
    simp only [stateScalingInverse,one_smul,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul]
    module
  rw [he]
  have hX : ‖((s:ℝ)⁻¹:ℂ)•(matrixPseudoinverse A*outerProduct b)‖≤ c^2*κ := by
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0,solved_outerProduct_norm _ b hb]
    have hh : (s:ℝ)⁻¹*‖stateVector (matrixPseudoinverse A*ᵥb)‖≤(s:ℝ)⁻¹*(c*t) :=
        mul_le_mul_of_nonneg_left hτ.le (inv_pos.mpr hs0).le
    have hcoef : (s:ℝ)⁻¹*(c*t)=c^2*κ := by rw [hs];field_simp
    exact hh.trans_eq hcoef
  have hY : ‖matrixPseudoinverse A*(1-outerProduct b)‖≤κ :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hA (state_complement_norm_le_one b hb) (norm_nonneg _) hκ0.le).trans_eq (mul_one κ))
  apply (norm_add_le _ _).trans
  have hc2 : 1≤ c^2 := by nlinarith
  nlinarith

theorem singular_gap_of_pseudoinverse_norm (B : Matrix O I ℂ) (K : ℝ) (hK : 0< K)
    (hB : ‖matrixPseudoinverse B‖≤ K) :
    ∀ i : Fin (Fintype.card I),0< matrixSingularValues B i → K⁻¹≤ matrixSingularValues B i := by
  intro i hi
  have hcol : (matrixPseudoinverse B*B)*basisColumns (rightSingularBasis B)=
      basisColumns (rightSingularBasis B)*singularSupport B := by
    rw [matrixPseudoinverse_mul]
    simp only [Matrix.mul_assoc,basisColumns_adjoint_mul,Matrix.mul_one]
  have hact : (matrixPseudoinverse B*B)*ᵥ(⇑(rightSingularBasis B i))=⇑(rightSingularBasis B i) := by
    funext j
    have he:=congrArg (fun M=>M j i) hcol
    (try dsimp only at he)
    rw [singularSupport,Matrix.mul_diagonal,if_neg hi.ne',mul_one] at he
    exact he
  have hnorm : ‖stateVector (B*ᵥ(⇑(rightSingularBasis B i)))‖=matrixSingularValues B i := by
    have hh:=norm_apply_rightSingularBasis B i
    exact hh
  have hu : ‖stateVector (⇑(rightSingularBasis B i))‖=1 := norm_rightSingularBasis B i
  have hn :
      ‖stateVector
      (matrixPseudoinverse B*ᵥ(B*ᵥ(⇑(rightSingularBasis B i))))‖≤‖matrixPseudoinverse B‖*‖stateVector (B*ᵥ(⇑(rightSingularBasis B i)))‖ := l2_norm_mulVec_fromVec_le (matrixPseudoinverse B) (B*ᵥ(⇑(rightSingularBasis B i)))
  rw [Matrix.mulVec_mulVec,hact,hu,hnorm] at hn
  have hh:=hn.trans (mul_le_mul_of_nonneg_right hB hi.le)
  exact (inv_le_iff_one_le_mul₀ hK).mpr (by simpa only [mul_comm] using! hh)
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
