/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.EffCosts
open Matrix
set_option warningAsError false

theorem effectiveInteraction_factorization (ns : ℕ)
    (A B : Matrix (Reg ns) (Reg ns) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    HamiltonianEvolution (A+B) t = HamiltonianEvolution A t *
      orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 t := by
  have hh := ordered_interaction_picture_identity (Reg ns) A (fun _ => B)
    hA continuous_const (fun _ => hB) t
  simpa only [orderedEvolution_constant_hamiltonian,sub_zero] using! hh

end Qatlib.Concepts.InteractionEvo.EffCosts
