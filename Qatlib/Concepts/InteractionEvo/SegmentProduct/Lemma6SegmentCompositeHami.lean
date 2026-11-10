/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

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
