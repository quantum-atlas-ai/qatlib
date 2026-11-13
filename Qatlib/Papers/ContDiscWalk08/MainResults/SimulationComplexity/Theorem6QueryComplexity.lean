/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs

/-!
# Entrywise absolute values for query simulation

The matrix `elementwiseAbs` replaces each complex entry by its norm, viewed as a complex number.
The module records its real, nonnegative entries and preservation of entry norms, supplying
elementary data for the query-simulation discussion of [Childs2010].

## Main statements

* `elementwiseAbs_apply`: the entrywise formula.
* `elementwiseAbs_conj`: each entry is fixed by conjugation.
* `norm_elementwiseAbs`: entry norms are unchanged.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Defines the complex matrix obtained by replacing every entry of `H` by its norm. -/
def elementwiseAbs (H : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => (‖H i j‖ : ℂ)

/-- An entry of `elementwiseAbs H` is the complex coercion of the norm of the corresponding
entry of `H`. -/
theorem elementwiseAbs_apply (H : Matrix I I ℂ) (i j : I) :
    elementwiseAbs H i j = ((‖H i j‖ : ℝ) : ℂ) := rfl

/-- Every entry of `elementwiseAbs H` has zero imaginary part. -/
theorem elementwiseAbs_im (H : Matrix I I ℂ) (i j : I) :
    (elementwiseAbs H i j).im = 0 := by
  rw [elementwiseAbs]; exact Complex.ofReal_im _

/-- Every entry of `elementwiseAbs H` has nonnegative real part. -/
theorem elementwiseAbs_re_nonneg (H : Matrix I I ℂ) (i j : I) :
    0 ≤ (elementwiseAbs H i j).re := by
  rw [elementwiseAbs]; exact_mod_cast norm_nonneg (H i j)

/-- Every entry of `elementwiseAbs H` is fixed by complex conjugation. -/
theorem elementwiseAbs_conj (H : Matrix I I ℂ) (i j : I) :
    star (elementwiseAbs H i j) = elementwiseAbs H i j := by
  rw [elementwiseAbs]; exact Complex.conj_ofReal _

/-- Taking entrywise absolute values preserves the norm of each matrix entry. -/
theorem norm_elementwiseAbs (H : Matrix I I ℂ) (i j : I) :
    ‖elementwiseAbs H i j‖ = ‖H i j‖ := by
  rw [elementwiseAbs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
