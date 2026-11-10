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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
