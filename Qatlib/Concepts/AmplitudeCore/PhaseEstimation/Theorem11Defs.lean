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

/-!
# Finite phase estimation outcome masses

`bhmt11PhaseState` and `bhmt11QFT` define the finite phase vector and Fourier matrix.
`bhmt11OutcomeMass` is the squared amplitude after inverse Fourier transformation, and
`bhmt11WindowMass` sums those masses in a circular phase window. See [BrassardEtAl2002] for
background.

## Main statements

* `bhmt11OutcomeMass`: The squared norm of outcome `x` after applying the conjugate transpose
  Fourier matrix to the phase vector.
* `bhmt11WindowMass`: The sum of phase estimation outcome masses whose grid phases have circular
  distance at most `r` from `ω`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

open scoped BigOperators Classical

/-- The finite phase vector with coordinate `exp (2 * π * I * ω * y) / sqrt M`. See
[BrassardEtAl2002]. -/
noncomputable def bhmt11PhaseState (M : ℕ) (ω : ℝ) (y : Fin M) : ℂ :=
  (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
    Complex.exp (((2 * Real.pi * ω * (y.val : ℝ)) : ℂ) * Complex.I)
/-- The length `M` Fourier matrix with positive phase convention and normalization `1 / sqrt M`. -/
noncomputable def bhmt11QFT (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun y x =>
    (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
      Complex.exp (((2 * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
        (M : ℝ)) : ℂ) * Complex.I)
/-- The squared norm of outcome `x` after applying the conjugate transpose Fourier matrix to the
phase vector. -/
noncomputable def bhmt11OutcomeMass (M : ℕ) (ω : ℝ) (x : Fin M) : ℝ :=
  ‖((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M ω)) x‖ ^ 2
/-- The distance between two phases modulo integers, defined by an infimum of shifted absolute
differences. See [BrassardEtAl2002]. -/
noncomputable def bhmt11CircleDist (u v : ℝ) : ℝ :=
  sInf (Set.range (fun z : ℤ => |(z : ℝ) + v - u|))
/-- The sum of phase estimation outcome masses whose grid phases have circular distance at most
`r` from `ω`. -/
noncomputable def bhmt11WindowMass (M : ℕ) (ω r : ℝ) : ℝ :=
  ∑ x : Fin M,
    if bhmt11CircleDist ((x.val : ℝ) / (M : ℝ)) ω ≤ r
    then bhmt11OutcomeMass M ω x else 0

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
