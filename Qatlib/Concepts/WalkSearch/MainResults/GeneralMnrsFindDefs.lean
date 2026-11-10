/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace GeneralMnrsFindDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

noncomputable def generalFindDecoder {V : ℕ} (S : Finset (GeneralVertex V))
    (u : GeneralVertex V) : Option (GeneralVertex V) :=
  if u ∈ S then some u else none

noncomputable def generalFindSuccess {V : ℕ} (S : Finset (GeneralVertex V))
    (ψ : QState (GeneralVertex V)) : ℝ :=
  ∑ u ∈ S, ‖ψ u‖ ^ 2

end GeneralMnrsFindDefs
end Qatlib.Concepts.WalkSearch.MainResults
