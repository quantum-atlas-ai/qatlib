/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityStat

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open scoped BigOperators
set_option autoImplicit false

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
