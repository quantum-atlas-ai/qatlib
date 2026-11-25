/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolyMethod01.MainResults.OrDegree

@[expose] public section

/-!
# Boolean OR degree and exact query minimum

This bridge combines the exact degree and query minimum for OR with the generic
degree bound of Theorem 4.3. For positive input dimension, the generic bound gives
a lower bound of `⌈n / 2⌉` queries, which is strictly below the exact minimum
for `n ≥ 2`. The degree inequality is an equality at `n = 0`.

The source model is the finite clean Boolean-query program class exposed by the imported
`Qatlib` declarations.  No asymptotic or circuit-synthesis claim is added here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PolyMethod01.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
open Qatlib.Papers.PolyMethod01.MainResults

/-- Boolean OR has exact degree and exact query minimum `n` and satisfies the generic degree bound. -/
theorem or_polynomial_method_main (n : ℕ) :
    n ≤ 2 * exactMinimum (@orValue n) ∧
      exactMinimum (@orValue n) = n ∧
      exactDegree (@orValue n) = n := by
  refine ⟨?_, or_exactMinimum_eq n, or_exactDegree n⟩
  calc
    n = exactDegree (@orValue n) := (or_exactDegree n).symm
    _ ≤ 2 * exactMinimum (@orValue n) := (minimum_degree_bounds (@orValue n)).1

end Qatlib.Papers.PolyMethod01.MainResults
