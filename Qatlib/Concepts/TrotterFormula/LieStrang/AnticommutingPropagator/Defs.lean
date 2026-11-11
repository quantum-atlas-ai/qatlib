/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rescaled propagators from two matrix generators

This module defines the shifted generator `iω P + a Q`, its affine rescaled step, and the three
coefficients and matrix terms representing that step as a linear combination. The definitions
use elementary matrix linear combinations as in [Bhatia1997] and impose no Hermiticity,
involution, or unitarity hypotheses.

## Main statements

* `shiftedGenerator`: the matrix combination `iω P + a Q`.
* `rescaledStep`: the affine matrix `c • 1 + s • shiftedGenerator P Q a ω`.
* `rescaledCoefficients`: the coefficients for the matrix terms `1`, `P`, and `Q`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The shifted matrix generator `iω P + a Q` with real parameters `a` and `ω`. -/
def shiftedGenerator (P Q : Matrix I I ℂ) (a ω : ℝ) : Matrix I I ℂ :=
  (Complex.I * (ω : ℂ)) • P + (a : ℂ) • Q

/-- The affine propagator expression `c • 1 + s • shiftedGenerator P Q a ω`. -/
def rescaledStep (P Q : Matrix I I ℂ) (a ω c s : ℝ) : Matrix I I ℂ :=
  (c : ℂ) • 1 + (s : ℂ) • shiftedGenerator P Q a ω

/-- The three complex coefficients `c`, `iωs`, and `as` of the rescaled step. -/
def rescaledCoefficients (a ω c s : ℝ) : Fin 3 → ℂ :=
  ![(c : ℂ), Complex.I * (ω : ℂ) * (s : ℂ), (a : ℂ) * (s : ℂ)]

/-- The three matrix terms `1`, `P`, and `Q` used in the rescaled-step linear combination. -/
def rescaledUnitaries (P Q : Matrix I I ℂ) : Fin 3 → Matrix I I ℂ := ![1, P, Q]

end Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
