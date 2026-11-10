/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.ModelSemantics.CoherentValueFeasibleBoundaryStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped ENNReal ComplexOrder

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
