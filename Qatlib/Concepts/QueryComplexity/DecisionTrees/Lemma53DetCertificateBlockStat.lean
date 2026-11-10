/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

def Lemma53DeterministicCertificateBlock : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → Bool),
    ∃ t : BoolQueryTree (Fin N) Bool,
      (∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x) ∧
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ oneCertificateComplexity f * blockSensitivity f

end Qatlib.Concepts.QueryComplexity.DecisionTrees
