/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

def SensitivityDominanceCorollary : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → Bool),
    deterministicQueryComplexity f ≤ blockSensitivity f ^ 3

end Qatlib.Concepts.QueryComplexity.DecisionTrees
