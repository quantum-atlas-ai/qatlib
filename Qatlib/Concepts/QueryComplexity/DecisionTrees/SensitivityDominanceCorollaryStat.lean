/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions

/-!
# Statement of the block sensitivity cubic bound

This module defines `SensitivityDominanceCorollary`, the assertion that every total Boolean
function has deterministic query complexity at most the cube of its block sensitivity. The
inequality is the consequence of the certificate estimates developed in [BealsEtAl2001].

## Main statements

* `SensitivityDominanceCorollary`: the proposition D(f) ≤ bs(f)³.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

/-- The statement that the deterministic query complexity of every total Boolean function is at
most the cube of its block sensitivity. -/
def SensitivityDominanceCorollary : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → Bool),
    deterministicQueryComplexity f ≤ blockSensitivity f ^ 3

end Qatlib.Concepts.QueryComplexity.DecisionTrees
