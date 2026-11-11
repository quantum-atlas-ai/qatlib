/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers

/-!
# Interaction picture evolution factorization

This module proves the interaction picture factorization for two constant Hermitian
Hamiltonians. `effectiveInteraction_factorization` expresses evolution under their sum as free
evolution followed by ordered evolution of the conjugated interaction generator, as in
[LowWiebe2018].

## Main statements

* `effectiveInteraction_factorization`: the exact factorization of evolution under `A + B`.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.EffCosts
open Matrix
set_option warningAsError false

/-- For Hermitian `A` and `B`, evolution under `A + B` equals evolution under `A` multiplied by
the ordered interaction picture evolution from zero to `t`. See [Low and Wiebe, Equation
(18)][LowWiebe2018]. -/
theorem effectiveInteraction_factorization (ns : ℕ)
    (A B : Matrix (Reg ns) (Reg ns) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    HamiltonianEvolution (A+B) t = HamiltonianEvolution A t *
      orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 t := by
  have hh := ordered_interaction_picture_identity (Reg ns) A (fun _ => B)
    hA continuous_const (fun _ => hB) t
  simpa only [orderedEvolution_constant_hamiltonian,sub_zero] using! hh

end Qatlib.Concepts.InteractionEvo.EffCosts
