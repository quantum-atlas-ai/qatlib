/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts

/-!
# Corrected triangle-search statement

`Theorem4` names `theorem4WalkFreshValidation`, the triangle-search contract with least-power
subset parameters and a checker using separate validation seeds. It packages soundness, a
finite-seed failure bound, and a cost bound proportional to n^(13/10) with explicit solver
constants and logarithmic factors.

The underlying triangle-search complexity is discussed in [Ambainis2005].

## References

* [Ambainis, 2005][Ambainis2005]
-/

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- The triangle-search proposition `theorem4WalkFreshValidation`, using least-power subset
sizes, separate validation seeds, and explicit solver-dependent cost constants. -/
def Theorem4 : Prop := theorem4WalkFreshValidation

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
