/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.EvalRelaxed.AdversaryGamma2SandwichStat
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2EvalRelaxed

/-!
# Comparing relaxed and unrelaxed evaluation bounds

`adversaryGamma2Sandwich` compares the evaluation-masked and unmasked filtered γ₂ values with
factor `2 * (1 - 1 / Fintype.card E)`. It also bounds the operator norm of any matrix vanishing
on equal-output pairs whose query-filtered matrices are contractions.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `adversaryGamma2Sandwich`: The two value comparisons and the feasible matrix norm bound.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.EvalRelaxed
open Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The evaluation-masked filtered γ₂ value is no larger than the unmasked value, which is at
most `2 * (1 - 1 / Fintype.card E)` times it. Every matrix vanishing on equal-output pairs
with query-filtered norms at most one has norm bounded by the masked value [Lee et al.,
Theorem 3.4][LeeEtAl2011]. -/
theorem adversaryGamma2Sandwich : AdversaryGamma2Sandwich := by
  intro X _ _ E _ _ n input f
  refine ⟨filteredGamma2_le_of_filter_absorb (B:=gramFunctionEvaluationMatrix f) ?_,
    filteredGamma2_queryDelta_le_of_evalRelaxed input f,
    fun Γ hzero hfeas => adversary_le_filteredGamma2_evalRelaxed input f Γ hzero hfeas⟩
  intro x y
  simp only [gramFunctionEvaluationMatrix]
  split <;> simp
end Qatlib.Concepts.ConversionCore.EvalRelaxed
