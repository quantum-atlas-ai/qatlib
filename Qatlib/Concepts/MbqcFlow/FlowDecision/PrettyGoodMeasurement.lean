/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementFrame
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Pretty-good measurement from a matrix frame

Constructs `prettyGoodPOVM` from the normalized frame `prettyGoodFrame W`. The effects indexed
by `some i` are the outer products of frame columns, while `none` carries the complementary
effect `1 - prettyGoodSupport W`.

The positivity and normalization proofs produce a POVM for every matrix `W`, without requiring
its columns to span the ambient space. See [Watrous2018] for the quantum measurement framework.

## Main statements

* `prettyGoodEffect`: frame-column effects and a complementary effect.
* `prettyGoodPOVM`: the resulting normalized positive operator-valued measure.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}

/-- The Hermitian matrix `F * Fᴴ` associated with the pretty-good frame `F`. -/
noncomputable def prettyGoodSupport (W : Matrix (Fin D) I ℂ) :
    HermitianMat (Fin D) ℂ :=
  ⟨prettyGoodFrame W * (prettyGoodFrame W)ᴴ,
    (pretty_good_frame_support_contract I D W).2.2.1⟩

/-- The outer product of frame column `i` at `some i`, with the complementary support effect at
`none`. -/
noncomputable def prettyGoodEffect (W : Matrix (Fin D) I ℂ) :
    Option I → HermitianMat (Fin D) ℂ
  | none => 1 - prettyGoodSupport W
  | some i => ⟨outerProduct (fun d => prettyGoodFrame W d i),
      outerProduct_isHermitian _⟩

/-- Every pretty-good measurement effect, including the complementary effect, is nonnegative. -/
private theorem pretty_good_effect_nonneg (W : Matrix (Fin D) I ℂ)
    (o : Option I) : 0 ≤ prettyGoodEffect W o := by
  rw [HermitianMat.zero_le_iff]
  cases o with
  | none => exact (pretty_good_frame_support_contract I D W).2.2.2.2
  | some i => exact outerProduct_posSemidef _

/-- The sum of the frame-column effects equals `prettyGoodSupport W`. -/
private theorem pretty_good_columns_sum (W : Matrix (Fin D) I ℂ) :
    ∑ i : I, (prettyGoodEffect W (some i)).mat =
      (prettyGoodSupport W).mat := by
  ext d e
  simp only [prettyGoodEffect, prettyGoodSupport, HermitianMat.mat_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, outerProduct_apply]
  rfl

/-- The pretty-good effects, including the complementary outcome, sum to the identity. -/
private theorem pretty_good_effect_sum (W : Matrix (Fin D) I ℂ) :
    ∑ o : Option I, prettyGoodEffect W o = 1 := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum, Fintype.sum_option,
    pretty_good_columns_sum]
  change (1 - (prettyGoodSupport W).mat) + (prettyGoodSupport W).mat = 1
  exact sub_add_cancel _ _

/-- The POVM formed by the pretty-good frame-column effects together with their complementary
support effect. -/
noncomputable def prettyGoodPOVM (W : Matrix (Fin D) I ℂ) :
    POVM (Option I) (Fin D) where
  mats := prettyGoodEffect W
  nonneg := pretty_good_effect_nonneg W
  normalized := pretty_good_effect_sum W

end Qatlib.Concepts.MbqcFlow.FlowDecision
