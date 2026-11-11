/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioning
import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioningPseudoinverse

/-!
# One-flag encoding of the preconditioned matrix

This module proves that `scalingPrepare` and the two preconditioned branches form an exact block
encoding of the lifted state scaling followed by the input unitary. Compression through
`flagFrame` then gives `preconditioned_projectedEncoding`, a projected unitary encoding of
`stateScaling s b * A` for a normalized state and scale strictly between zero and one.

The construction uses linear combinations of unitaries within the projected-encoding framework
[GilyenSuLowWiebe2019].

## Main statements

* `preconditionedUnitary_blockEncoding`: Proves the exact lifted block encoding.
* `compress_flag_corner`: Identifies compression through flagged frames with the false-flag
  corner.
* `preconditioned_projectedEncoding`: Transfers the original projected encoding to the
  state-preconditioned matrix.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical
variable {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

omit [DecidableEq H] in

/-- The rank-one state projector lifted through an isometric frame is an orthogonal projector
when the state is normalized. -/
theorem lifted_state_projector (L : Matrix H O ℂ) (b : QState O) (hL : IsIsometry L) (hb : Normalized b) :
    IsOrthogonalProjector (L*outerProduct b*Lᴴ) := by
  have hP:=isOrthogonalProjector_outerProduct hb
  constructor
  · calc
      _ = L*(outerProduct b*(Lᴴ*L)*outerProduct b)*Lᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [show Lᴴ*L=1 from hL,Matrix.mul_one,hP.1]
  · change (L*outerProduct b*Lᴴ)ᴴ=L*outerProduct b*Lᴴ
    have hstar : (outerProduct b)ᴴ=outerProduct b := hP.2
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hstar,Matrix.mul_assoc]

/-- For `0 < s < 1`, `scalingPrepare s` prepares the weights `scalingWeights s` from the `false`
basis state. -/
theorem scalingPrepare_isPrepare (s : ℝ) (hs0 : 0< s) (hs1 : s<1) :
    IsPrepare (scalingPrepare s) (scalingWeights s) false := by
  have h0 : 0≤(1-s)/2 := by linarith
  have h1 : 0≤(1+s)/2 := by linarith
  constructor
  · rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    ext i j
    cases i <;> cases j <;>
      norm_num [scalingPrepare,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_bool,-Real.sqrt_div] <;>
      norm_cast <;> field_simp <;> nlinarith [Real.sq_sqrt h0,Real.sq_sqrt h1,Real.sq_sqrt (by linarith : 0≤1-s),Real.sq_sqrt (by linarith : 0≤1+s),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  · funext j
    cases j <;> simp
        [scalingPrepare,scalingWeights,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]

/-- Both preconditioned branches are unitary when the frame is isometric, the state is
normalized, and the input matrix is unitary. -/
theorem preconditionedBranches_unitary (L : Matrix H O ℂ) (b : QState O) (s : ℝ)
    (U : Matrix H H ℂ) (hL : IsIsometry L) (hb : Normalized b) (hU : U∈Matrix.unitaryGroup H ℂ) :
    ∀ j,preconditionedBranches L b s U j∈Matrix.unitaryGroup H ℂ := by
  have hp:=lifted_state_projector L b hL hb
  have hr : (1-(2:ℂ)•(L*outerProduct b*Lᴴ):Matrix H H ℂ)∈Matrix.unitaryGroup H ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    have hpstar : (L*outerProduct b*Lᴴ)ᴴ=L*outerProduct b*Lᴴ := hp.2
    have hpid : (L*outerProduct b*Lᴴ)*(L*outerProduct b*Lᴴ)=L*outerProduct b*Lᴴ := hp.1
    have ha : (1-(2:ℂ)•(L*outerProduct b*Lᴴ):Matrix H H ℂ)ᴴ=1-(2:ℂ)•(L*outerProduct b*Lᴴ) := by
      simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul,hpstar]
      norm_num
    rw [ha]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_smul,hpid]
    module
  intro j
  cases j
  · simpa only [preconditionedBranches,one_smul] using (Matrix.unitaryGroup H ℂ).mul_mem hr hU
  · exact hU

/-- For an isometric frame, normalized state, unitary input, and `0 < s < 1`, the preconditioned
workspace exactly block-encodes `liftedStateScaling L b s * U` at scale one in the
false-flag corner. -/
theorem preconditionedUnitary_blockEncoding (L : Matrix H O ℂ) (b : QState O) (s : ℝ)
    (U : Matrix H H ℂ) (hL : IsIsometry L) (hb : Normalized b)
    (hs0 : 0< s) (hs1 : s<1) (hU : U∈Matrix.unitaryGroup H ℂ) :
    IsBlockEncoding (preconditionedUnitary L b s U) false (liftedStateScaling L b s*U) 1 := by
  have hw : ∀ j,0≤ scalingWeights s j := by intro j;cases j <;> dsimp [scalingWeights] <;> linarith
  have hh:=lcu_isBlockEncoding (preconditionedBranches L b s U)
    (preconditionedBranches_unitary L b s U hL hb hU) hw (scalingPrepare_isPrepare s hs0 hs1)
  have he : (∑ j,scalingWeights s j•preconditionedBranches L b s U j)=liftedStateScaling L b s*U := by
    simp only [Fintype.sum_bool,scalingWeights,preconditionedBranches,liftedStateScaling,Matrix.add_mul,Matrix.smul_mul]
    ext i j
    simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.one_mul]
    simp only [Complex.real_smul]
    push_cast
    ring
  simpa only [preconditionedUnitary,he] using hh

omit [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] in

/-- Compression through flagged frames equals compression of the false-flag block corner through
the original frames. -/
theorem compress_flag_corner (V : Matrix (Bool×H) (Bool×H) ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) :
    compress (flagFrame L) V (flagFrame R)=Lᴴ*BlockCorner V false*R := by
  ext o i
  simp [compress,flagFrame,BlockCorner,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type]

/-- A projected unitary encoding of `A` yields a projected unitary encoding of `stateScaling s b
* A` through the preconditioned unitary and flagged frames when `b` is normalized and `0 < s
< 1`. -/
theorem preconditioned_projectedEncoding (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (b : QState O) (s : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hb : Normalized b) (hs0 : 0< s) (hs1 : s<1) :
    ProjectedUnitaryEncoding (stateScaling s b*A) (preconditionedUnitary L b s U) (flagFrame L) (flagFrame R) := by
  have hh:=preconditionedUnitary_blockEncoding L b s U henc.left_isometry hb hs0 hs1 henc.unitary
  refine ⟨hh.1,flagFrame_isIsometry henc.left_isometry,flagFrame_isIsometry henc.right_isometry,?_⟩
  rw [compress_flag_corner,hh.2.2]
  simp only [inv_one,Complex.ofReal_one,one_smul]
  rw [← Matrix.mul_assoc,stateScaling_intertwining L b s henc.left_isometry]
  have he : Lᴴ*(U*R)=A := by simpa only [compress,Matrix.mul_assoc] using henc.encoded
  rw [Matrix.mul_assoc,Matrix.mul_assoc,he]
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
