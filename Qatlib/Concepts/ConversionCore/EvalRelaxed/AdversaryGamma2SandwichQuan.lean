/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.EvalRelaxed.AdversaryGamma2SandwichStat
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2EvalRelaxed
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.EvalRelaxed
open Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false

theorem adversaryGamma2Sandwich : AdversaryGamma2Sandwich := by
  intro X _ _ E _ _ n input f
  refine ⟨filteredGamma2_le_of_filter_absorb (B:=gramFunctionEvaluationMatrix f) ?_,
    filteredGamma2_queryDelta_le_of_evalRelaxed input f,
    fun Γ hzero hfeas => adversary_le_filteredGamma2_evalRelaxed input f Γ hzero hfeas⟩
  intro x y
  simp only [gramFunctionEvaluationMatrix]
  split <;> simp
end Qatlib.Concepts.ConversionCore.EvalRelaxed
