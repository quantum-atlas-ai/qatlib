/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.TwirlingCounterexample

/-!
# A counterexample to universal invariant-state conversion

This module states and refutes a precise universal conversion condition associated with
Proposition 8.2 of [Kuperberg2005]. `SourcePurelyHInvariantConversion` requires one
matrix-valued map, independent of the subgroup, to send every positive semidefinite trace-one
matrix satisfying the fixed-projector support equation to that subgroup's coset density.

`prop82_universal_conversion_refuted` disproves this condition for `SourceTwoPointGroup`.
`prop82_counterexample` packages the underlying `TwirlingCounterexample` witness.

## Main statements

* `SourcePurelyHInvariantConversion`: the subgroup-independent conversion condition.
* `prop82_universal_conversion_refuted`: failure of this condition on the two-point group.
* `prop82_counterexample`: the supplied counterexample witness.

## References

* [Kuperberg, 2005, Proposition 8.2][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open scoped ComplexOrder

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Prop82

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.RecordExtract

/-- The existence of one matrix-valued map, independent of the subgroup, sending every positive
semidefinite trace-one matrix satisfying the fixed-projector support equation to that
subgroup's coset density. -/
def SourcePurelyHInvariantConversion (G : Type*) [Group G] [Fintype G] : Prop :=
  ∃ convert : Matrix G G ℂ → Matrix G G ℂ,
    ∀ (H : Subgroup G) (rho : Matrix G G ℂ),
      rho.PosSemidef → rho.trace = 1 →
      sourceFixedProjector G H * rho * sourceFixedProjector G H = rho →
      convert rho = sourceCosetDensity G H

/-- No subgroup-independent conversion map satisfies `SourcePurelyHInvariantConversion` on
`SourceTwoPointGroup`. This refutes the stated universal formulation associated with
[Kuperberg, Proposition 8.2][Kuperberg2005]. -/
theorem prop82_universal_conversion_refuted :
    ¬ SourcePurelyHInvariantConversion SourceTwoPointGroup := by
  intro h
  exact sourceTwirlingCounterexample.2.2.2.2.2 h

/-- Provides `sourceTwirlingCounterexample` as a witness of `TwirlingCounterexample` for the
conversion formulation associated with [Kuperberg, Proposition 8.2][Kuperberg2005]. -/
theorem prop82_counterexample : TwirlingCounterexample :=
  sourceTwirlingCounterexample

end Qatlib.Concepts.HspRecovery.OpenSieve.Prop82
