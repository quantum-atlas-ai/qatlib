/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PhaseGeometry.AngleEncoding

namespace Qatlib.Papers.QFinanceMC18.MeanCircuit
set_option autoImplicit false
open Qatlib.Foundations.PhaseGeometry.AngleEncoding

theorem corrected_decoder_bounds {θhat θ ε : ℝ}
    (hθ : 0 ≤ θ) (hclose : |θhat-θ| ≤ ε) (h0 : 0 ≤ θhat)
    (hguard : θhat ≤ Real.pi - 2*ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |phaseMean θhat-phaseMean θ| ≤
      (1/2)*|Real.cos ((θhat+ε)/2)-Real.cos (θhat/2)| ∧
    |phaseMean θhat-phaseMean θ| ≤ |θhat-θ|/4 :=
  ⟨phaseMean_error_restricted hθ hclose h0 hguard hε0 hε1, phaseMean_lipschitz θhat θ⟩

theorem discounted_decoder_error (scale discount θhat θ : ℝ) :
    |discount * scale * phaseMean θhat - discount * scale * phaseMean θ| ≤
      |discount * scale| * (|θhat-θ|/4) := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (phaseMean_lipschitz θhat θ) (abs_nonneg _)

end Qatlib.Papers.QFinanceMC18.MeanCircuit
