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

/-!
# Fourier phase states and circular distance

`bhmtPhaseState` defines the finite uniform phase state, and `bhmtPhaseDistance` measures phase
displacement modulo integers. These are the state and distance used in the phase state overlap
formula. See [BrassardEtAl2002] for background.

## Main statements

* `bhmtPhaseState`: The length `M` phase state with coordinate `exp (2 * π * I * ω * y) / sqrt
  M`. See [BrassardEtAl2002].
* `bhmtPhaseDistance`: The circular distance between two real phases, defined as the infimum of
  their absolute differences after integer shifts. See [BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

/-- The length `M` phase state with coordinate `exp (2 * π * I * ω * y) / sqrt M`. See
[BrassardEtAl2002]. -/
noncomputable def bhmtPhaseState (M : ℕ) (ω : ℝ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun y : Fin M =>
    ((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * ω * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
/-- The circular distance between two real phases, defined as the infimum of their absolute
differences after integer shifts. See [BrassardEtAl2002]. -/
noncomputable def bhmtPhaseDistance (ω₀ ω₁ : ℝ) : ℝ :=
  sInf (Set.range (fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|))

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
