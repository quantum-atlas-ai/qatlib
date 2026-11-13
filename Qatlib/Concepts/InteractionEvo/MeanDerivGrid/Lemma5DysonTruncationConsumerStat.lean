/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonAuxiliary

/-!
# Statement of the two-level Dyson error bound

`Lemma5DysonTruncationConsumer` records the concrete Dyson approximation target for
`interactionPictureField`. The statement compares its order-3 grid sum on 38 points with the
ordered evolution up to time 2/5. These estimates support the interaction-picture simulation
analysis of [LowWiebe2018].

## Main statements

* `Lemma5DysonTruncationConsumer`: the operator-norm error target of 1/8.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the order-3 Dyson grid approximation with 38 points for
`interactionPictureField` at time 2/5 has operator-norm error at most 1/8. -/
def Lemma5DysonTruncationConsumer : Prop :=
  ‖truncatedDysonGridSum interactionPictureField (2 / 5) 38 3 -
      orderedEvolution
        (fun u => Complex.I • interactionPictureField u) 0 (2 / 5)‖ ≤ (1 : ℝ) / 8

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
