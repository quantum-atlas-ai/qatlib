/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Foundations.PureStateMath.MixedState
open Qatlib.Foundations.PureStateMath

open Matrix
open scoped ComplexOrder
open scoped Classical BigOperators

namespace Qatlib.Papers.ClassShadows20.LowerBound

noncomputable def lemma8CodeState (d r : ℕ) (α : ℝ) (P : Operator d) :
    Operator d :=
  ((1 - α) / (d : ℝ)) • 1 + (α / (r : ℝ)) • P
end Qatlib.Papers.ClassShadows20.LowerBound
