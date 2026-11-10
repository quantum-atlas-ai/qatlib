/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonAuxiliary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

def Lemma5DysonTruncationConsumer : Prop :=
  ‖truncatedDysonGridSum interactionPictureField (2 / 5) 38 3 -
      orderedEvolution
        (fun u => Complex.I • interactionPictureField u) 0 (2 / 5)‖ ≤ (1 : ℝ) / 8

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
