/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

open Matrix
open scoped Matrix.Norms.L2Operator

def HermitianEvolutionLipschitz : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H H' : Matrix I I ℂ),
    H.IsHermitian → H'.IsHermitian → ∀ t : ℝ,
      ‖Qatlib.Foundations.PureStateMath.HamiltonianEvolution H t -
        Qatlib.Foundations.PureStateMath.HamiltonianEvolution H' t‖ ≤ |t| * ‖H - H'‖

end Qatlib.Concepts.QsvtCore.HamiltonianSim
