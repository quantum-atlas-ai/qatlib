/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Gram matrices determine readout marginals

This module proves that equal Gram matrices determine the squared norms of all common linear
combinations of finite state families. The tagged-state construction `taggedState` and its
transformed `output` turn this fact into equality of output marginals under a common operation
on the tag register; see [Watrous2018] for the underlying state-space formalism.

## Main statements

* `gram_determinacy`: Families with the same Gram matrix give equal squared norms for every
  common finite linear combination.

* `native_gram_determinacy`: Equal Gram matrices of finite state families imply equality of the
  total squared coordinate masses of every common linear combination.

* `marginal_eq_of_gram`: Families with equal Gram matrices have equal output tag marginals after
  the same matrix acts on their tag registers.

* `output_normalized`: Applying a unitary matrix on the tag register preserves normalization of
  the tagged state.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The Hermitian self-pairing of a finite linear combination expands as a double sum of
coefficient products and pairwise inner products. -/
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

/-- Families with the same Gram matrix give equal squared norms for every common finite linear
combination. -/
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

/-- Converting a coordinatewise linear combination of state vectors to Euclidean space agrees
with taking the corresponding linear combination after conversion. -/
private theorem wrap_sum (a : I → ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) :
    Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (fun b => ∑ i, a i * w i b) =
      ∑ i, a i • Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (w i) := by
  ext b
  simp [Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec]

omit [DecidableEq I] in

/-- Equal Gram matrices of finite state families imply equality of the total squared coordinate
masses of every common linear combination. -/
theorem native_gram_determinacy (a : I → ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (v : I → Qatlib.Foundations.PureStateMath.QState K)
    (hG : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (w i) (w j) = Qatlib.Foundations.PureStateMath.Inner (v i) (v j)) :
    (∑ b, ‖∑ i, a i * w i b‖ ^ 2) = ∑ b, ‖∑ i, a i * v i b‖ ^ 2 := by
  rw [← Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclidean_fromVec_sq,
      ← Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclidean_fromVec_sq, wrap_sum, wrap_sum]
  exact Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.gram_determinacy a (fun i => Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (w i))
    (fun i => Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (v i)) (by simpa only [Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec] using hG)

/-- The joint state with amplitude `w i b` at the tagged coordinate `(i, b)`. -/
def taggedState (w : I → Qatlib.Foundations.PureStateMath.QState J) :
    Qatlib.Foundations.PureStateMath.QState (I × J) := fun p => w p.1 p.2

/-- The tagged state after applying `U` to its tag register and the identity to its second
register. -/
noncomputable def output (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) : Qatlib.Foundations.PureStateMath.QState (I × J) :=
  Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)) (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState w)

omit [DecidableEq I] in

/-- The output amplitude at `(i, b)` is the sum of `U i x * w x b` over tags `x`. -/
theorem output_apply (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (i : I) (b : J) :
    Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w (i,b) = ∑ x, U i x * w x b := by
  simp [Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output, Qatlib.Foundations.PureStateMath.ApplyGate, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState, Matrix.one_apply, mul_ite, ite_mul]

/-- The measurement weight of an output tag is the sum over the second register of the squared
norms of its transformed amplitudes. -/
theorem marginal_eq (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (i : I) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) (Finset.univ.filter (fun p : I × J => p.1 = i)) =
      ∑ b, ‖∑ x, U i x * w x b‖ ^ 2 := by
  simp [Qatlib.Foundations.PureStateMath.MeasureProb, Finset.sum_filter,
      Fintype.sum_prod_type, Qatlib.Foundations.PureStateMath.BornProb, Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output_apply]

/-- Families with equal Gram matrices have equal output tag marginals after the same matrix acts
on their tag registers. -/
theorem marginal_eq_of_gram (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J) (v : I → Qatlib.Foundations.PureStateMath.QState K)
    (hG : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (w i) (w j) = Qatlib.Foundations.PureStateMath.Inner (v i) (v j)) (i : I) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) (Finset.univ.filter (fun p : I × J => p.1 = i)) =
      Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U v) (Finset.univ.filter (fun p : I × K => p.1 = i)) := by
  rw [Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.marginal_eq,
      Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.marginal_eq]
  exact Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.native_gram_determinacy
      (fun x => U i x) w v hG

/-- Applying a unitary matrix on the tag register preserves normalization of the tagged state. -/
theorem output_normalized (U : Matrix I I ℂ) (w : I → Qatlib.Foundations.PureStateMath.QState J)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hw : Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState w)) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.output U w) :=
  Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Foundations.PureStateMath.tensorGate_unitary hU (Submonoid.one_mem _)) hw

end Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout
