/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.Encoding.EncodingReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TranscorrChem20.MainResults.Encoding
variable {I : Type*} [Fintype I] [DecidableEq I]

def paperRotation (P : Matrix I I ℂ) (θ : ℝ) : Matrix I I ℂ :=
  exp (θ • ((Complex.I : ℂ) • P))

theorem paperRotation_eq_standard (P : Matrix I I ℂ) (θ : ℝ) :
    paperRotation P θ = standardRotation P (-2*θ) := by
  unfold paperRotation standardRotation
  congr 1
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  ring

theorem paperRotation_hasDerivAt (P : Matrix I I ℂ) (θ : ℝ) :
    HasDerivAt (paperRotation P) ((Complex.I : ℂ) • (P * paperRotation P θ)) θ := by
  simpa only [paperRotation, Matrix.smul_mul] using!
    hasDerivAt_exp_smul_const' ((Complex.I : ℂ) • P) θ

omit [DecidableEq I] in

theorem paper_derivative_scale (P U : Matrix I I ℂ) (ψ : QState I) :
    (Complex.I : ℂ) • (U *ᵥ (P *ᵥ ψ)) =
      (-2 : ℂ) • ((-Complex.I/2 : ℂ) • (U *ᵥ (P *ᵥ ψ))) := by
  rw [smul_smul]
  congr 1
  ring

end Qatlib.Papers.TranscorrChem20.MainResults.Encoding
