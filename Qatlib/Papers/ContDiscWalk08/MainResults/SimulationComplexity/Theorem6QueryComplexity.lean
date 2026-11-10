/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

def elementwiseAbs (H : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => (‖H i j‖ : ℂ)

theorem elementwiseAbs_apply (H : Matrix I I ℂ) (i j : I) :
    elementwiseAbs H i j = ((‖H i j‖ : ℝ) : ℂ) := rfl

theorem elementwiseAbs_im (H : Matrix I I ℂ) (i j : I) :
    (elementwiseAbs H i j).im = 0 := by
  rw [elementwiseAbs]; exact Complex.ofReal_im _

theorem elementwiseAbs_re_nonneg (H : Matrix I I ℂ) (i j : I) :
    0 ≤ (elementwiseAbs H i j).re := by
  rw [elementwiseAbs]; exact_mod_cast norm_nonneg (H i j)

theorem elementwiseAbs_conj (H : Matrix I I ℂ) (i j : I) :
    star (elementwiseAbs H i j) = elementwiseAbs H i j := by
  rw [elementwiseAbs]; exact Complex.conj_ofReal _

theorem norm_elementwiseAbs (H : Matrix I I ℂ) (i j : I) :
    ‖elementwiseAbs H i j‖ = ‖H i j‖ := by
  rw [elementwiseAbs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
