/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeStat

/-!
# Statement of repeated-segment simulation error

`Corollary4CompositeError` specifies the error bound for powers of a contraction approximating a
single interaction-picture segment. The target is evolution under the sum of two Hermitian
matrices for the total segment duration. These estimates support the interaction-picture
simulation analysis of [LowWiebe2018].

## Main statements

* `Corollary4CompositeError`: the proposition bounding the accumulated error by `L * δ`.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

/-- The proposition that a contraction within δ of one exact interaction-picture segment has its
`L`th power within `L * δ` of `HamiltonianEvolution (A + B) (L * τ)`. -/
def Corollary4CompositeError : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ),
    A.IsHermitian → B.IsHermitian →
    ∀ (L : ℕ) (τ δ : ℝ), 0 ≤ δ → ∀ W : Matrix I I ℂ,
      ‖W‖ ≤ 1 →
      ‖W - (HamiltonianEvolution A τ *
        orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 τ)‖ ≤ δ →
      ‖W ^ L - HamiltonianEvolution (A + B) ((L : ℝ) * τ)‖ ≤ (L : ℝ) * δ

end Qatlib.Concepts.InteractionEvo.SegmentProduct
