/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.KernelWitnessContracts

/-!
# Zero-vector realization of the kernel-witness contract

Proves `KernelWitness` by choosing zero for both existential witnesses. The contract's kernel
equations and homogeneous overlap inequalities all hold for these choices because it contains no
nonzero requirement.

This proof records the weakness of the uncorrected interface rather than a nonzero witness
construction. The explicit corrected witnesses used in reflection-query algorithms are treated
separately in the framework of [Reichardt2011].

## Main statements

* `kernelWitness`: the uncorrected kernel-witness proposition is satisfied by zero vectors.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections
open scoped BigOperators

/-- The proposition `KernelWitness` holds by choosing the zero vector for both of its
existential witnesses. -/
theorem kernelWitness : KernelWitness := by
  classical
  intro X _ _ n m input f v W _ _
  constructor
  · intro x _
    refine ⟨0, ?_, ?_⟩ <;> simp
  · intro x _
    refine ⟨0, ?_, ?_⟩ <;> simp [Qatlib.Foundations.PureStateMath.Inner]

end Qatlib.Concepts.QueryComplexity.Reflections
