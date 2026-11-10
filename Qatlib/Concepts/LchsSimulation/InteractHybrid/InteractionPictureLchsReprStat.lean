/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InteractHybrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def InteractionPictureLchsRepresentation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ),
    L.IsHermitian → Continuous H → (∀ u, (H u).IsHermitian) →
    orderedEvolution (fun u => Complex.I • (H u + k • L)) 0 t =
      HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t

end Qatlib.Concepts.LchsSimulation.InteractHybrid
