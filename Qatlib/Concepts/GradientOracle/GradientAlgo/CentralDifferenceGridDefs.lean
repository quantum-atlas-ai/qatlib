/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.GradientAlgo
noncomputable section

noncomputable def gridCenter (M : ℕ) (R : ℝ) (z : Fin M) : ℝ :=
  R * ((2 * (z : ℝ) + 1) / (2 * M) - 1 / 2)
end
noncomputable section

noncomputable def gridPoint (d M : ℕ) (R : ℝ) (z : Fin d → Fin M) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j : Fin d => gridCenter M R (z j))
end
end Qatlib.Concepts.GradientOracle.GradientAlgo
