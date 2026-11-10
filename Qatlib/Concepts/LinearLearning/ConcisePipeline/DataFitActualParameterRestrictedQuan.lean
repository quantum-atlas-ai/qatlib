/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

theorem dataFitActualParameterRestricted : DataFitActualParameterRestricted := by
  unfold DataFitActualParameterRestricted
  exact computed_data_fit_actual_parameter

end Qatlib.Concepts.LinearLearning.ConcisePipeline
