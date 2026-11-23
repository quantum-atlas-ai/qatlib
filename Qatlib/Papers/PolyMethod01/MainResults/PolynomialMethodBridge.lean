/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolyMethod01.MainResults.OrDegree

@[expose] public section

/-!
# A tight polynomial-method instance for Boolean OR

This bridge packages the exact degree calculation for OR with the exact query minimum
and the Beals polynomial-method inequality.  It is a concrete, finite Boolean instance
of Theorem 4.3, including the zero-input boundary case.

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

/-- The polynomial method lower bound is tight for Boolean OR in the exact query model. -/
theorem or_polynomial_method_main (n : ℕ) :
    n ≤ 2 * exactMinimum (@orValue n) ∧
      exactMinimum (@orValue n) = n ∧
      exactDegree (@orValue n) = n := by
  refine ⟨?_, or_exactMinimum_eq n, or_exactDegree n⟩
  calc
    n = exactDegree (@orValue n) := (or_exactDegree n).symm
    _ ≤ 2 * exactMinimum (@orValue n) := (minimum_degree_bounds (@orValue n)).1

end Qatlib.Papers.PolyMethod01.MainResults
