/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeStat

/-!
# Exact composition of interaction-picture segments

`lemma6SegmentComposite` identifies repeated exact interaction-picture segments with evolution
under `A + B` for the total duration. The matrices `A` and `B` are Hermitian, and the identity
holds for every natural number of segments and real segment duration. These estimates support
the interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `lemma6SegmentComposite`: the exact `L`-segment evolution identity.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

/-- Proves that the `L`th power of an exact interaction-picture segment equals evolution under
`A + B` through time `L * τ`; see [Low and Wiebe, Lemma 6][LowWiebe2018]. -/
theorem lemma6SegmentComposite : Lemma6SegmentComposite := by
  intro I _ _ A B hA hB L τ
  have hseg := ordered_interaction_picture_identity I A (fun _ => B)
    hA continuous_const (fun _ => hB) τ
  rw [← hseg, orderedEvolution_constant_hamiltonian, sub_zero]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [pow_succ, ih, ← hamiltonianEvolution_add]
    congr 1
    simp [Nat.cast_add, add_mul]

end Qatlib.Concepts.InteractionEvo.SegmentProduct
