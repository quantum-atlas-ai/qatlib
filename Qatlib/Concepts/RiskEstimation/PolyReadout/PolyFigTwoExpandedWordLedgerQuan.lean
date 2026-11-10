/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedWordLedgerStat
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix
set_option warningAsError false

theorem polyFigTwoExpandedWordLedger : PolyFigTwoExpandedWordLedger := by
  intro n u hn A j c fp M r _ hM
  refine ⟨?_, ?_⟩
  · rw [figTwoAngleWord_length]
    exact figTwoTerms_gate_bound n (fp.natDegree*(2*u+1)) hn
  · simpa only [one_mul] using! risk_native_readout_charges
      (figTwoExpandedPreparation n A u c fp) (figTwoStart n j) M r 1 hM
end Qatlib.Concepts.RiskEstimation.PolyReadout
