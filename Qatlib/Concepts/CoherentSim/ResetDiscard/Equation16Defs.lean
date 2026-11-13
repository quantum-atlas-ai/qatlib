/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Stat
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels

/-!
# Reduced operators and vector outer products

`ReducedState` traces out the ancillary index of a matrix on a product space, while `vecOuter`
forms the rank-one operator of a vector. These constructions express reduced-state errors for
the Taylor amplification analysis [BerryEtAl2015Taylor].

## Main statements

* `ReducedState`: Partial trace over the ancillary register.
* `vecOuter`: The outer product of a vector with its conjugate.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

/-- The reduced operator obtained by summing the diagonal ancillary blocks of a matrix on the
product space. -/
noncomputable def ReducedState {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (A : Matrix (J × I) (J × I) ℂ) : Matrix I I ℂ :=
  Matrix.of fun i i' => ∑ a : J, A (a, i) (a, i')

/-- The vector outer product with entries `v i * conj (v i')`, without a normalization
requirement. -/
noncomputable def vecOuter {I : Type*} [Fintype I] [DecidableEq I] (v : QState I) : Matrix I I ℂ :=
  Matrix.of fun i i' => v i * (starRingEnd ℂ) (v i')
end Qatlib.Concepts.CoherentSim.ResetDiscard
