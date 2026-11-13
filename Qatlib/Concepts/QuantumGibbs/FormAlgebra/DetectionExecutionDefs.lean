/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

/-!
# Marked reflections and measurement mass

This module defines a marked-set phase reflection, its singleton adjoint-circuit word, and the
marked-coordinate measurement mass. These finite-dimensional setup and checking objects are used
in the quantum-walk search framework of [MagniezNayakRolandSantha2011].

## Main statements

* `generalMarkedReflection`: The diagonal sign flip on marked coordinates.
* `generalCheckWord`: A single fixed-gate check word.
* `generalMarkedMass`: The sum of squared marked amplitudes.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace DetectionExecutionDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- The diagonal matrix acting by negative one on `S` and by one outside `S`. -/
noncomputable def generalMarkedReflection {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) : Matrix V V ℂ :=
  Matrix.diagonal (fun u => if u ∈ S then (-1 : ℂ) else 1)

/-- The singleton adjoint-circuit word applying `generalMarkedReflection S` as a fixed gate. -/
noncomputable def generalCheckWord {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) : List (AdjointStep V) :=
  [AdjointStep.gate (generalMarkedReflection S)]

/-- The sum of squared amplitude norms over the marked finite set `S`. -/
noncomputable def generalMarkedMass {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (ψ : QState V) : ℝ :=
  ∑ u ∈ S, ‖ψ u‖ ^ 2

end DetectionExecutionDefs
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
