/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

theorem dataFitActualQualityRestricted : DataFitActualQualityRestricted := by
  unfold DataFitActualQualityRestricted
  exact computed_data_fit_actual_quality

end Qatlib.Concepts.LinearLearning.ConcisePipeline
