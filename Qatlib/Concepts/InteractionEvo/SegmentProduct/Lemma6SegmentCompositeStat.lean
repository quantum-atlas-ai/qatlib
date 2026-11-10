/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

def Lemma6SegmentComposite : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ),
    A.IsHermitian → B.IsHermitian →
    ∀ (L : ℕ) (τ : ℝ),
      (HamiltonianEvolution A τ *
        orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 τ) ^ L
        = HamiltonianEvolution (A + B) ((L : ℝ) * τ)

end Qatlib.Concepts.InteractionEvo.SegmentProduct
