/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1
import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1RankProcessSubgoalAqua
import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma2
import Qatlib.Concepts.AmplitudeSearch.Amplification.Theorem1ChargedBudgetCorrected
import Qatlib.Concepts.AmplitudeSearch.Amplification.Theorem1QueryBudgetCorrected
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsAqua
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedSearchAttemptAqua

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedMinimumBudgetAqua

/-!
# Minimum-finding and amplification results

This module collects the rank-process lemmas, corrected budget theorems, minimum-budget
probability results, and amplification results for the minimum-finding algorithm of
[DurrHoyer1996]. It also imports the interrupted-call and interrupted-minimum results needed for
the budgeted execution model.

The module serves as an import interface; the statements and proofs are provided by the imported
modules, including `theorem1ChargedBudgetCorrected` and `theorem1QueryBudgetCorrected`.

## Main statements

* `theorem1ChargedBudgetCorrected`: provides the corrected theorem with charged runtime
  accounting.
* `theorem1QueryBudgetCorrected`: provides the corrected theorem with a Boolean query budget.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
