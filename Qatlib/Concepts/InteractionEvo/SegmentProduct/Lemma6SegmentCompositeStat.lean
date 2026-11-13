/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers

/-!
# Statement of exact segment composition

`Lemma6SegmentComposite` records the equality between powers of a single exact
interaction-picture segment and the full Hamiltonian evolution. The statement applies to two
finite-dimensional Hermitian matrices. These estimates support the interaction-picture
simulation analysis of [LowWiebe2018].

## Main statements

* `Lemma6SegmentComposite`: the exact composition proposition.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

/-- The proposition that repeating the exact interaction-picture segment `L` times gives
`HamiltonianEvolution (A + B) (L * τ)` for Hermitian `A` and `B`. -/
def Lemma6SegmentComposite : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ),
    A.IsHermitian → B.IsHermitian →
    ∀ (L : ℕ) (τ : ℝ),
      (HamiltonianEvolution A τ *
        orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 τ) ^ L
        = HamiltonianEvolution (A + B) ((L : ℝ) * τ)

end Qatlib.Concepts.InteractionEvo.SegmentProduct
