/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators

def ApproximatePolynomialBlockSensitivity : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (p : MvPolynomial (Fin n) ℝ) (ε : ℝ),
    0 ≤ ε → ε < 1/2 →
    (∀ x : Fin n → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1 ∧
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
        (if f x then (1 : ℝ) else 0)| ≤ ε) →
    (1 - 2 * ε) * (blockSensitivity f : ℝ) ≤
      (2 - 2 * ε) * (p.totalDegree : ℝ)^2

end Qatlib.Concepts.QueryComplexity.DegreeMethod
