/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace DetectionExecutionDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

noncomputable def generalMarkedReflection {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) : Matrix V V ℂ :=
  Matrix.diagonal (fun u => if u ∈ S then (-1 : ℂ) else 1)

noncomputable def generalCheckWord {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) : List (AdjointStep V) :=
  [AdjointStep.gate (generalMarkedReflection S)]

noncomputable def generalMarkedMass {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (ψ : QState V) : ℝ :=
  ∑ u ∈ S, ‖ψ u‖ ^ 2

end DetectionExecutionDefs
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
