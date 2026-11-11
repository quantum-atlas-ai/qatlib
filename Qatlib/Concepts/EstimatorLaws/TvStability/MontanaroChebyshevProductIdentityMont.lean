/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityStat

/-!
# Gibbs ratio moment identities

Proves the first- and second-moment identities for the exponential ratio observable between two
inverse temperatures. These finite exponential-sum identities are the partition-function input
to the Chebyshev cooling-schedule analysis in [Montanaro2015].

## Main statements

* `montanaroChebyshevProductIdentitySubgoal` identifies the two weighted moments with
  partition-function ratios at `β₂` and `2 * β₂ - β₁`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open scoped BigOperators
set_option autoImplicit false

/-- Proves the Gibbs ratio observable's first- and second-moment identities used in the
cooling-schedule argument of [Montanaro2015] by combining exponential factors. -/
theorem montanaroChebyshevProductIdentitySubgoal : MontanaroChebyshevProductIdentitySubgoal := by
  intro Ω _ H β₁ β₂ _hβ _hβ12 _hZ₁ _hZ₂
  constructor
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

end Qatlib.Concepts.EstimatorLaws.TvStability
