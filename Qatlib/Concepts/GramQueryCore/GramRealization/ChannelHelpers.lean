/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem inner_sum_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : I → ℂ) (w : I → E) :
    inner ℂ (∑ i, a i • w i) (∑ i, a i • w i) =
      ∑ i, ∑ j, a j * starRingEnd ℂ (a i) * inner ℂ (w i) (w j) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

omit [DecidableEq I] in

theorem gram_determinacy {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a : I → ℂ) (w : I → E) (v : I → F)
    (hG : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) :
    ‖∑ i, a i • w i‖ ^ 2 = ‖∑ i, a i • v i‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.inner_sum_expand, Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.inner_sum_expand]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hG i j]

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

omit [DecidableEq I] [Fintype J] [DecidableEq J] in

private theorem wrap_sum (a : I → ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) :
    Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (fun b => ∑ i, a i * w i b) =
      ∑ i, a i • Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (w i) := by
  ext b
  simp [Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec]

omit [DecidableEq I] in

theorem native_gram_determinacy (a : I → ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (v : I → Qatlib.Foundations.PureStateMath.QState K)
    (hG : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (w i) (w j) = Qatlib.Foundations.PureStateMath.Inner (v i) (v j)) :
    (∑ b, ‖∑ i, a i * w i b‖ ^ 2) = ∑ b, ‖∑ i, a i * v i b‖ ^ 2 := by
  rw [← Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclidean_fromVec_sq,
      ← Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclidean_fromVec_sq, wrap_sum, wrap_sum]
  exact Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.gram_determinacy a (fun i => Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (w i))
    (fun i => Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (v i)) (by simpa only [Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec] using hG)

def taggedState (w : I → Qatlib.Foundations.PureStateMath.QState J) :
    Qatlib.Foundations.PureStateMath.QState (I × J) := fun p => w p.1 p.2

noncomputable def output (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) : Qatlib.Foundations.PureStateMath.QState (I × J) :=
  Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)) (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState w)

omit [DecidableEq I] in

theorem output_apply (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (i : I) (b : J) :
    Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w (i,b) = ∑ x, U i x * w x b := by
  simp [Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output, Qatlib.Foundations.PureStateMath.ApplyGate, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState, Matrix.one_apply, mul_ite, ite_mul]

theorem marginal_eq (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (i : I) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) (Finset.univ.filter (fun p : I × J => p.1 = i)) =
      ∑ b, ‖∑ x, U i x * w x b‖ ^ 2 := by
  simp [Qatlib.Foundations.PureStateMath.MeasureProb, Finset.sum_filter,
      Fintype.sum_prod_type, Qatlib.Foundations.PureStateMath.BornProb, Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output_apply]

theorem marginal_eq_of_gram (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (v : I → Qatlib.Foundations.PureStateMath.QState K)
    (hG : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (w i) (w j) = Qatlib.Foundations.PureStateMath.Inner (v i) (v j)) (i : I) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) (Finset.univ.filter (fun p : I × J => p.1 = i)) =
      Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U v) (Finset.univ.filter (fun p : I × K => p.1 = i)) := by
  rw [Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.marginal_eq,
      Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.marginal_eq]
  exact Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.native_gram_determinacy
      (fun x => U i x) w v hG

theorem output_normalized (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hw : Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState w)) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) :=
  Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Foundations.PureStateMath.tensorGate_unitary hU (Submonoid.one_mem _)) hw

end Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout
