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

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

open scoped BigOperators Classical

noncomputable def bhmt11PhaseState (M : ℕ) (ω : ℝ) (y : Fin M) : ℂ :=
  (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
    Complex.exp (((2 * Real.pi * ω * (y.val : ℝ)) : ℂ) * Complex.I)
noncomputable def bhmt11QFT (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun y x =>
    (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
      Complex.exp (((2 * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
        (M : ℝ)) : ℂ) * Complex.I)
noncomputable def bhmt11OutcomeMass (M : ℕ) (ω : ℝ) (x : Fin M) : ℝ :=
  ‖((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M ω)) x‖ ^ 2
noncomputable def bhmt11CircleDist (u v : ℝ) : ℝ :=
  sInf (Set.range (fun z : ℤ => |(z : ℝ) + v - u|))
noncomputable def bhmt11WindowMass (M : ℕ) (ω r : ℝ) : ℝ :=
  ∑ x : Fin M,
    if bhmt11CircleDist ((x.val : ℝ) / (M : ℝ)) ω ≤ r
    then bhmt11OutcomeMass M ω x else 0

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
