/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartFirstSuccessStat
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartAttemptLawTigh
import Qatlib.Concepts.SearchStopping.PaidRestart.BranchCostOutputRelabel
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

theorem actualRestartFirstSuccess : ActualRestartFirstSuccess := by
  intro I _ _ hN T' v hT hv hprep A j hC price hp
  (try dsimp only)
  let next := bbhtActualRestartNextPrice T' v j A hC hv price
  let a := fun i : I => if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0
  let q := ENNReal.ofReal (1-MeasureProb (GroverState A j) A)
  have hl := actualRestartAttemptLaw I hN T' v hT hv hprep A j hC price
  refine ⟨?_,?_,?_⟩
  · exact unitRestart_exact_receipt next price a q hl.1 hl.2.1 hl.2.2 hp
  · intro i k hi
    exact unitRestart_zero_address next price a q hl.1 hl.2.1 hl.2.2 i
      (by simp [a,hi]) k k
  · intro i k hk
    by_contra hm
    obtain ⟨r,hr⟩ := unitRestart_support next price a q hl.1 hl.2.1 hl.2.2 hp i k hm
    exact hk r hr

end Qatlib.Concepts.SearchStopping.PaidRestart
