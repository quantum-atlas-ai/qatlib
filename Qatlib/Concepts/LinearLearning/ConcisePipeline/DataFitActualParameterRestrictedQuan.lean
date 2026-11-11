/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers

/-!
# Restricted quantum data-fitting parameter preparation

This module proves `dataFitActualParameterRestricted` by instantiating the computed
finite-inverse consumer. Under the projected-unitary encoding and singular-value assumptions,
the result provides a postselected approximate least-squares solution state together with an
exact adjoint-query count, in the data-fitting setting of [WiebeBraunLloyd2012].

## Main statements

* `dataFitActualParameterRestricted`: parameter-state preparation with a dyadic error bound and
  a finite-inverse query ledger.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

/-- For a projected-unitary encoding with a positive singular-value bound, the finite inverse
word produces an approximate least-squares solution state when its dyadic error is below
twice the overlap, and satisfies the stated exact query count. This is a restricted
parameter-preparation result in the setting of [WiebeBraunLloyd2012]. -/
theorem dataFitActualParameterRestricted : DataFitActualParameterRestricted := by
  unfold DataFitActualParameterRestricted
  exact computed_data_fit_actual_parameter

end Qatlib.Concepts.LinearLearning.ConcisePipeline
