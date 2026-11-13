/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers

/-!
# Restricted quantum estimation of fit quality

This module proves `dataFitActualQualityRestricted` using the computed range-projection and
amplitude-estimation consumer. For a normalized prepared target and the stated projected-unitary
encoding and singular-value bounds, it estimates the squared least-squares residual with
explicit dyadic and amplitude-estimation errors.

The fit-quality task is motivated by [WiebeBraunLloyd2012], with amplitude-estimation background
in [BrassardEtAl2002].

## Main statements

* `dataFitActualQualityRestricted`: unitarity of the computed preparation and residual
  estimation with probability at least `8 / π ^ 2`.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

/-- For a projected-unitary encoding and unitary preparation of a normalized target, the
computed projection preparation is unitary and amplitude estimation approximates the squared
least-squares residual within `π / M + π ^ 2 / M ^ 2 + (1 / 2) ^ k` with probability at
least `8 / π ^ 2`, under the stated singular-value assumptions. This is a restricted
fit-quality result in the setting of [WiebeBraunLloyd2012]. -/
theorem dataFitActualQualityRestricted : DataFitActualQualityRestricted := by
  unfold DataFitActualQualityRestricted
  exact computed_data_fit_actual_quality

end Qatlib.Concepts.LinearLearning.ConcisePipeline
