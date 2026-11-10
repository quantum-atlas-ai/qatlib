/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Operations
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Ampl
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

noncomputable def bhmtPhaseState (M : ℕ) (ω : ℝ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun y : Fin M =>
    ((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * ω * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
noncomputable def bhmtPhaseDistance (ω₀ ω₁ : ℝ) : ℝ :=
  sInf (Set.range (fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|))

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
