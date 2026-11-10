/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators

def payoffObservable {O : Type*} [Fintype O] {D : ℕ}
    (Λ : POVM O (Fin D)) (f : O → ℝ) : Operator D :=
  ∑ o, ((f o : ℝ) : ℂ) • (Λ.mats o).mat

end Qatlib.Concepts.SdpDuality.ConeSeparation
