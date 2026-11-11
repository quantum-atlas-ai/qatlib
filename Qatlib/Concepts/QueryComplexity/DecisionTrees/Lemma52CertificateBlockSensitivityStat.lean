/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions

/-!
# Statement of certificate complexity bounds

This module defines `Lemma52CertificateBlockSensitivity`, the pair of inequalities relating one
certificate complexity, certificate complexity, and block sensitivity for total Boolean
functions. These are the certificate bounds used in [BealsEtAl2001].

## Main statements

* `Lemma52CertificateBlockSensitivity`: the proposition C¹(f) ≤ C(f) ≤ bs(f)².

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

/-- The statement that every total Boolean function has one certificate complexity at most its
certificate complexity and certificate complexity at most the square of its block
sensitivity. -/
def Lemma52CertificateBlockSensitivity : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → Bool),
    oneCertificateComplexity f ≤ certificateComplexity f ∧
      certificateComplexity f ≤ blockSensitivity f ^ 2

end Qatlib.Concepts.QueryComplexity.DecisionTrees
