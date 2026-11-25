/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MatProdVerify04.MainResults.HadamardTest

@[expose] public section

/-!
# Overlap readout of the first Hadamard outcome

Claim 1 in Section 2.3 reduces the readout to two branch vectors.
Normalization of the joint state gives the first outcome formula
even when the branch vectors have different norms.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabStateGen03.MainResults

open Qatlib.Papers.MatProdVerify04.MainResults

/-- The squared norm of the zero outcome is determined by the real overlap of the branch vectors. -/
theorem overlap_prob {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v w : H) (hn : ‖(Real.sqrt 2)⁻¹ • v‖ ^ 2 + ‖(Real.sqrt 2)⁻¹ • w‖ ^ 2 = 1) :
    ‖(hadamardFirstQubit ((Real.sqrt 2)⁻¹ • v) ((Real.sqrt 2)⁻¹ • w)).1‖ ^ 2 =
      (1 / 2) * (1 + (inner ℂ v w).re) := by
  have hscale : ‖(Real.sqrt 2)⁻¹‖ ^ 2 = (1 : ℝ) / 2 := by
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [norm_smul, mul_pow, hscale] at hn
  rw [hadamard_test_reflects, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ)]
  norm_num [RCLike.re_to_complex]
  linarith

end Qatlib.Papers.AdiabStateGen03.MainResults
