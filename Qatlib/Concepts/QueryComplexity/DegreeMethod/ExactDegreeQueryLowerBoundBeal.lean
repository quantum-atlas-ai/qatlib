/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeQueryLowerBoundStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# Exact quantum query lower bound from polynomial degree

The theorem `exactDegreeQueryLowerBound` proves `ExactDegreeQueryLowerBound` by representing a
circuit's acceptance probability with a Boolean acceptance polynomial. Exact computation of a
Boolean function therefore bounds its exact polynomial degree by twice the circuit's query
count.

This is the degree lower bound for exact quantum queries from [BealsEtAl2001]. The proof uses
acceptance-polynomial multilinearization to obtain the required representation and degree bound.

## Main statements

* `exactDegreeQueryLowerBound`: exact polynomial degree is at most twice the number of oracle
  queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- An exact Boolean acceptance circuit computes a function of exact polynomial degree at most
twice its query count, as in [Beals et al., Theorem 4.3][BealsEtAl2001]. -/
theorem exactDegreeQueryLowerBound : ExactDegreeQueryLowerBound := by
  intro I W _ _ _ _ C ψ E f hf
  obtain ⟨hd,_,he⟩ := acceptance_boolean_multilinearization_preserves_run C ψ E
  apply le_trans ?_ hd
  unfold exactDegree
  apply csInf_le'
  refine ⟨booleanAcceptancePolynomial C ψ E, ?_, rfl⟩
  intro g
  rw [boolEval, he g]
  exact hf g

end Qatlib.Concepts.QueryComplexity.DegreeMethod
