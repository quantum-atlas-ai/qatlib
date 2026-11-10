/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.KernelWitnessContracts

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections
open scoped BigOperators

theorem kernelWitness : KernelWitness := by
  classical
  intro X _ _ n m input f v W _ _
  constructor
  · intro x _
    refine ⟨0, ?_, ?_⟩ <;> simp
  · intro x _
    refine ⟨0, ?_, ?_⟩ <;> simp [Qatlib.Foundations.PureStateMath.Inner]

end Qatlib.Concepts.QueryComplexity.Reflections
