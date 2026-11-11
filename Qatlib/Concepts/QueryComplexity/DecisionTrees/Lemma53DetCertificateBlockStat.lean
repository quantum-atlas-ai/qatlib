/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

/-!
# Statement of the deterministic certificate bound

This module defines `Lemma53DeterministicCertificateBlock`, the existence of a correct
deterministic query tree with maximum query count bounded by one certificate complexity times
block sensitivity. It expresses the decision tree bound of Lemma 5.3 in [BealsEtAl2001].

## Main statements

* `Lemma53DeterministicCertificateBlock`: the proposition asserting a correct tree with query
  budget C¹(f)bs(f).

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

/-- The statement that every total Boolean function has a correct deterministic query tree using
at most its one certificate complexity times its block sensitivity queries. -/
def Lemma53DeterministicCertificateBlock : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → Bool),
    ∃ t : BoolQueryTree (Fin N) Bool,
      (∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x) ∧
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t ≤ oneCertificateComplexity f * blockSensitivity f

end Qatlib.Concepts.QueryComplexity.DecisionTrees
