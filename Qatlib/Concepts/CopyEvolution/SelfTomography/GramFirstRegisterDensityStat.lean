/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.CopyEvolution.GramReadout
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# The Gram first-register density specification

This module defines `GramFirstRegisterDensity`, which relates the weighted Gram state to its
reduced density operator. The proposition requires normalized input states and nonnegative
weights whose squares sum to one.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `GramFirstRegisterDensity`: normalization of `gramState`, its partial trace, and positivity
  and unit trace of `gramMatrix`.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Matrix

/-- The proposition that a normalized weighted Gram state has first-register reduction
`gramMatrix`, and that this matrix is a density operator. -/
def GramFirstRegisterDensity : Prop :=
  ∀ (r d : ℕ) (ψ : Fin r → QState (Fin d)), (∀ i, Normalized (ψ i)) →
    ∀ (w : Fin r → ℝ), (∀ i, 0 ≤ w i) → (∑ i, (w i) ^ 2 = 1) →
    Normalized (gramState ψ w) ∧
    PartialTrace (outerProduct (gramState ψ w)) = gramMatrix ψ w ∧
    IsDensityOperator (gramMatrix ψ w)

end Qatlib.Concepts.CopyEvolution.SelfTomography
