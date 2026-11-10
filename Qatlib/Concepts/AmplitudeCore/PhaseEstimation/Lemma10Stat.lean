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
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma10Defs

open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma10Spec
def expected : Prop :=
  (∀ (M : ℕ) (ω₀ ω₁ : ℝ),
  0 < M →
  0 ≤ ω₀ → ω₀ < 1 →
  0 ≤ ω₁ → ω₁ < 1 →
  let Δ : ℝ := bhmtPhaseDistance ω₀ ω₁;
  (Δ = 0 →
    ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 = 1) ∧
  (Δ ≠ 0 →
    ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 =
      Real.sin ((M : ℝ) * Δ * Real.pi) ^ 2 /
        ((M : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2)))
end Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma10Spec
