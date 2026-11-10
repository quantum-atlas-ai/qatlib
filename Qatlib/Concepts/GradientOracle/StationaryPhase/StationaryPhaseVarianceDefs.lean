/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

open MeasureTheory

namespace Qatlib.Concepts.GradientOracle.StationaryPhase

noncomputable def stationaryPhaseCube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (-1 / 2) (1 / 2 : ℝ))
end Qatlib.Concepts.GradientOracle.StationaryPhase
