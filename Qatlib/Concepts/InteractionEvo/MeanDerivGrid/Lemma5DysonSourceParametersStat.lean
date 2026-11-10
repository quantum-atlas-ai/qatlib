/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

def Lemma5DysonSourceParameters : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (K M : ℕ),
    Continuous H → Continuous Hd →
    (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    0 < t → 0 < M → 0 < ε →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Λ * t ≤ Real.log 2 →
    (16 : ℝ) * t ^ 2 * ((1 / t) * ∫ u in (0 : ℝ)..t, ‖Hd u‖ + Λ ^ 2) / ε ≤ M →
    (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε / 2 →
    ‖truncatedDysonGridSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ ε

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
