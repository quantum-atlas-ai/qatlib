/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.StateDependentCopyPrecisionStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.CopyStateDependentPrecision
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder
set_option autoImplicit false

theorem stateDependentCopyPrecision : StateDependentCopyPrecision := by
  intro D r ρ t n X hρ hX hn
  exact ⟨copy_state_dependent_fresh_global_error D r ρ t n X hρ hX hn,
    by rw [freshCopyResourceCounts_eq, List.length_replicate]⟩
end Qatlib.Concepts.CopyEvolution.CopyExponent
