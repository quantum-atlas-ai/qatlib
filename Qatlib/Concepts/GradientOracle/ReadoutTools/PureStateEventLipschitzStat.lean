/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineGradient

/-!
# Specification of pure-state event stability

`PureStateEventLipschitz` specifies a Euclidean-distance bound for differences of event
probabilities on normalized finite pure states. This is the measurement stability principle used
in the finite-dimensional framework of [Watrous2018].

## Main statements

* `PureStateEventLipschitz`: the absolute event-probability difference is bounded by the norm of
  the state-vector difference.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical

/-- The proposition that every event-probability difference for two normalized finite pure
states is at most the Euclidean norm of their difference. -/
def PureStateEventLipschitz : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (u v : QState I),
    Normalized u → Normalized v → ∀ E : Finset I,
      |MeasureProb u E - MeasureProb v E| ≤ ‖toEuclidean_fromVec (u-v)‖

end Qatlib.Concepts.GradientOracle.ReadoutTools
