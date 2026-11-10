/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder


namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

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

noncomputable def interactionPictureField (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 + u / 4) • Matrix.diagonal ![1, -1] + (3 / 20 : ℝ) • Matrix.of ![![0, 1], ![1, 0]]
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
