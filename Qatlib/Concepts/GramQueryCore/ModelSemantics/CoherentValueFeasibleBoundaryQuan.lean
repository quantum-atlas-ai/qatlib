/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.ModelSemantics.CoherentValueFeasibleBoundaryStat

/-!
# Feasible-set form of coherent Gram optimization

Proves that the coherent state conversion optimization equals the infimum of the filtered Gram
objective over its feasible positive semidefinite target matrices. Feasibility bounds the
unfiltered difference from the target by the given nonnegative tolerance.

This exposes the constrained optimization form used for coherent state conversion in
[LeeEtAl2011].

## Main statements

* `coherentValueFeasibleBoundary`: rewrites the coherent value as an infimum over feasible
  matrices.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped ENNReal ComplexOrder

/-- For nonnegative `δ`, rewrites `stateConversionSDP` as the infimum of the filtered objective
over positive semidefinite matrices within unfiltered budget `δ` of the target
[LeeEtAl2011]. -/
theorem coherentValueFeasibleBoundary : CoherentValueFeasibleBoundary := by
  intro X _ _ n input δ ρ σ hδ
  unfold stateConversionSDP
  apply le_antisymm
  · apply le_iInf
    intro M
    apply iInf_le_of_le ⟨M.1, M.2.1,
      (filteredGamma2_budget_boundary X 1 (M.1 - σ) (fun _ => gramFilterAllOnes) δ hδ).mp M.2.2⟩
    exact le_rfl
  · apply le_iInf
    intro M
    apply iInf_le_of_le ⟨M.1, M.2.1,
      (filteredGamma2_budget_boundary X 1 (M.1 - σ) (fun _ => gramFilterAllOnes) δ hδ).mpr M.2.2⟩
    exact le_rfl

end Qatlib.Concepts.GramQueryCore.ModelSemantics
