/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.Encoding.EncodingReadout

/-!
# Rotation conventions for transcorrelated readout

This module defines the paper convention `paperRotation P θ = exp (i θ P)` and relates it to
`standardRotation` at angle `-2 * θ`. It proves the derivative in the paper convention and the
corresponding factor of negative two between the derivative-state prefactors. See
[McArdleTew2020].

## Main statements

* `paperRotation_eq_standard`: the two conventions agree after rescaling the angle.
* `paperRotation_hasDerivAt`: the derivative is `Complex.I • (P * paperRotation P θ)`.
* `paper_derivative_scale`: the derivative-state factor changes by negative two.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TranscorrChem20.MainResults.Encoding
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The matrix rotation `exp (θ • (Complex.I • P))` in the paper's angle convention. -/
def paperRotation (P : Matrix I I ℂ) (θ : ℝ) : Matrix I I ℂ :=
  exp (θ • ((Complex.I : ℂ) • P))

/-- The paper rotation at angle `θ` equals the standard rotation at angle `-2 * θ`. See
[McArdleTew2020]. -/
theorem paperRotation_eq_standard (P : Matrix I I ℂ) (θ : ℝ) :
    paperRotation P θ = standardRotation P (-2*θ) := by
  unfold paperRotation standardRotation
  congr 1
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  ring

/-- The derivative of the paper rotation at `θ` is `Complex.I • (P * paperRotation P θ)`. -/
theorem paperRotation_hasDerivAt (P : Matrix I I ℂ) (θ : ℝ) :
    HasDerivAt (paperRotation P) ((Complex.I : ℂ) • (P * paperRotation P θ)) θ := by
  simpa only [paperRotation, Matrix.smul_mul] using!
    hasDerivAt_exp_smul_const' ((Complex.I : ℂ) • P) θ

omit [DecidableEq I] in

/-- The derivative-state prefactor `Complex.I` equals negative two times the standard prefactor
`-Complex.I / 2` on `U *ᵥ (P *ᵥ ψ)`. See [McArdleTew2020]. -/
theorem paper_derivative_scale (P U : Matrix I I ℂ) (ψ : QState I) :
    (Complex.I : ℂ) • (U *ᵥ (P *ᵥ ψ)) =
      (-2 : ℂ) • ((-Complex.I/2 : ℂ) • (U *ᵥ (P *ᵥ ψ))) := by
  rw [smul_smul]
  congr 1
  ring

end Qatlib.Papers.TranscorrChem20.MainResults.Encoding
