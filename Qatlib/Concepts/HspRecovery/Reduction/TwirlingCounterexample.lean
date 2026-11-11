/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Qatlib.Concepts.HspRecovery.RecordExtract.TwirlingCounterexampleAuxiliary

/-!
# A specification separating invariance from coset states

`TwirlingCounterexample` states a two-point-group example of a positive trace-one state that is
supported on a subgroup-fixed space and unchanged by right twirling, yet differs from the
associated coset density. The density-operator terminology follows [Watrous2018].

The same proposition includes the nonexistence of a single conversion function producing every
subgroup's coset density from all states satisfying the corresponding support condition. This
module defines the proposition.

## Main definitions

* `TwirlingCounterexample`: the concrete state properties and universal conversion obstruction.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract
open scoped ComplexOrder
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The proposition asserting that `sourcePlusDensity` is positive, trace one, supported on the
trivial subgroup's fixed space, and unchanged by right twirling, yet differs from its coset
density. It also asserts that no single conversion function produces the coset density for
every subgroup and every density matrix supported on that subgroup's fixed space. -/
def TwirlingCounterexample : Prop := by
  classical
  exact
  sourcePlusDensity.PosSemidef ∧ sourcePlusDensity.trace = 1 ∧
    sourceFixedProjector SourceTwoPointGroup ⊥ * sourcePlusDensity *
      sourceFixedProjector SourceTwoPointGroup ⊥ = sourcePlusDensity ∧
    sourceRightTwirl SourceTwoPointGroup sourcePlusDensity = sourcePlusDensity ∧
    sourcePlusDensity ≠ sourceCosetDensity SourceTwoPointGroup ⊥ ∧
    ¬ ∃ convert : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ →
        Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ,
      ∀ (H : Subgroup SourceTwoPointGroup) (rho : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ),
        rho.PosSemidef → rho.trace = 1 →
          sourceFixedProjector SourceTwoPointGroup H * rho *
            sourceFixedProjector SourceTwoPointGroup H = rho →
          convert rho = sourceCosetDensity SourceTwoPointGroup H

end Qatlib.Concepts.HspRecovery.ReductionCore
