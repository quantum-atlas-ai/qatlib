/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid

/-!
# Auxiliary Dyson sums and a two-level field

This module defines `truncatedDysonGridSum` by summing reverse-ordered increment products over
sublists through a specified degree. It also defines the two-level field
`interactionPictureField` with a linearly varying diagonal term and a fixed off-diagonal term.
These definitions supply concrete objects for the Dyson grid setting of [LowWiebe2018].

## Main statements

* `truncatedDysonGridSum`: the strict-sublist truncation of the sampled Euler product.
* `interactionPictureField`: the field `(1 + u / 4) Z + (3 / 20) X`.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

/-- Sum the products of all reverse-ordered sampled Euler increment sublists of lengths zero
through `K`. -/
noncomputable def truncatedDysonGridSum {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1),
    ((((List.ofFn (fun j : Fin M =>
      -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M))))).reverse.sublistsLen k).map
        List.prod).sum
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018

/-- The two by two field `(1 + u / 4) Z + (3 / 20) X`, with diagonal Pauli Z and off-diagonal
Pauli X matrices. -/
noncomputable def interactionPictureField (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 + u / 4) • Matrix.diagonal ![1, -1] + (3 / 20 : ℝ) • Matrix.of ![![0, 1], ![1, 0]]
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
