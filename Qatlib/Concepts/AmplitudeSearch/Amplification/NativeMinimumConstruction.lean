/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs

/-!
# Native minimum construction imports

This module imports the definitions used to connect a dyadic threshold producer with charged
minimum search. The imported interface includes `thresholdRunLaw`, `ThresholdLedger`, and
`PublicProgramLedger`, which describe bounded rejection sampling and its resource records in the
minimum-finding setting of [DurrHoyer1996].

This file introduces no declarations of its own. Its role is to expose
`NativeMinimumConstructionDefs` through the native-construction module path.

## Main statements

* The imported `thresholdRunLaw` describes accepted indices with rejection counts and an
  explicit failed outcome.
* The imported `ThresholdLedger` and `PublicProgramLedger` record producer randomness,
  workspace, and charged search cost.
- No additional definitions or theorems are introduced in this module.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]. *A quantum algorithm for finding the minimum*. 1996.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open scoped ENNReal BigOperators Classical

end Qatlib.Concepts.AmplitudeSearch.Amplification
