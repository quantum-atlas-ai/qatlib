/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.CoherentSim.TimeDependent

noncomputable def gridIncrements {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (τ : ℝ) (M : ℕ) : List (Matrix I I ℂ) :=
  (List.ofFn (fun j : Fin M => -((τ / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (τ * (j : ℝ) / M)))).reverse

noncomputable def equation28Segment {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (τ : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1), (((gridIncrements H τ M).sublistsLen k).map List.prod).sum
end Qatlib.Concepts.CoherentSim.TimeDependent
