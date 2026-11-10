/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BoundedErrorApproxDegreeLowerBoundStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

theorem boundedErrorApproxDegreeQueryLowerBound : BoundedErrorApproxDegreeQueryLowerBound := by
  intro I W _ _ _ _ C ψ E f hf
  obtain ⟨hd,_,he⟩ := acceptance_boolean_multilinearization_preserves_run C ψ E
  apply le_trans ?_ hd
  unfold approxDegree
  apply csInf_le'
  refine ⟨booleanAcceptancePolynomial C ψ E, ?_, rfl⟩
  intro g
  rw [boolEval, he g]
  exact hf g

end Qatlib.Concepts.QueryComplexity.DegreeMethod
