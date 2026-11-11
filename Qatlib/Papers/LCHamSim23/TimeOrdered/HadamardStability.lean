/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 8: the approximation error of the block-encoded test

The paper's Lemma 8 (`arXiv:2303.01029v2`, supplementary Eq. (S34)) estimates
`⟨u₀|U_k†(t) O U_{k′}(t)|u₀⟩` from a `(α_O, 0)`-block-encoding of `O` and
circuits `Ũ_k` that approximate `U_k` to error `ε_HS`. Its own contribution,
on top of the cited Hadamard-test lemma (Lemma 7), is the operator estimate

`‖Ũ_k† O Ũ_{k′} - U_k† O U_{k′}‖ ≤ 2‖O‖ε_HS`,

so that `ε_HS = ε/(4‖O‖)` leaves `ε/2` for this part of the error.

This file formalizes that estimate and its `ε/2` specialization. The
amplitude-estimation query count of Lemma 7 and the sampling step of Theorem 9
are prior-work interfaces and are not restated here.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LCHamSim23.TimeOrdered

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Lemma 8 (Eq. (S34)): replacing both propagators by `ε_HS`-approximations
moves the conjugated observable by at most `2‖O‖ε_HS` in operator norm.

The unitarity of `U` and of `W'` is kept for statement fidelity but is not used:
the estimate only needs the approximating propagators to be unitary. -/
theorem hadamard_encoded_observable_error (O U U' W W' : Matrix I I ℂ) (ε : ℝ)
    (_hU : U ∈ Matrix.unitaryGroup I ℂ) (hU' : U' ∈ Matrix.unitaryGroup I ℂ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (_hW' : W' ∈ Matrix.unitaryGroup I ℂ)
    (hUε : ‖U' - U‖ ≤ ε) (hWε : ‖W' - W‖ ≤ ε) :
    ‖U'ᴴ * O * W' - Uᴴ * O * W‖ ≤ 2 * ‖O‖ * ε := by
  have hsplit : U'ᴴ * O * W' - Uᴴ * O * W =
      U'ᴴ * O * (W' - W) + (U'ᴴ - Uᴴ) * O * W := by
    noncomm_ring
  have hU' : ‖U'ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact unitary_norm_le_one hU'
  have hW : ‖W‖ ≤ 1 := unitary_norm_le_one hW
  have hdiff : ‖U'ᴴ - Uᴴ‖ ≤ ε := by
    rw [show U'ᴴ - Uᴴ = (U' - U)ᴴ by rw [Matrix.conjTranspose_sub],
      Matrix.l2_opNorm_conjTranspose]
    exact hUε
  have hleft : ‖U'ᴴ * O * (W' - W)‖ ≤ ‖O‖ * ε := by
    calc ‖U'ᴴ * O * (W' - W)‖ ≤ ‖U'ᴴ * O‖ * ‖W' - W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U'ᴴ‖ * ‖O‖) * ε :=
        mul_le_mul (Matrix.l2_opNorm_mul _ _) hWε (norm_nonneg _) (by positivity)
      _ ≤ (1 * ‖O‖) * ε := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hU' (norm_nonneg O)) ?_
        exact le_trans (by positivity) hWε
      _ = ‖O‖ * ε := by ring
  have hright : ‖(U'ᴴ - Uᴴ) * O * W‖ ≤ ε * ‖O‖ := by
    calc ‖(U'ᴴ - Uᴴ) * O * W‖ ≤ ‖(U'ᴴ - Uᴴ) * O‖ * ‖W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U'ᴴ - Uᴴ‖ * ‖O‖) * 1 :=
        mul_le_mul (Matrix.l2_opNorm_mul _ _) hW (norm_nonneg _) (by positivity)
      _ ≤ (ε * ‖O‖) * 1 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg O)) zero_le_one
      _ = ε * ‖O‖ := by ring
  calc
    ‖U'ᴴ * O * W' - Uᴴ * O * W‖
        = ‖U'ᴴ * O * (W' - W) + (U'ᴴ - Uᴴ) * O * W‖ := by rw [hsplit]
    _ ≤ ‖U'ᴴ * O * (W' - W)‖ + ‖(U'ᴴ - Uᴴ) * O * W‖ := norm_add_le _ _
    _ ≤ ‖O‖ * ε + ε * ‖O‖ := add_le_add hleft hright
    _ = 2 * ‖O‖ * ε := by ring

/-- Lemma 8, precision choice: `ε_HS = ε/(4‖O‖)` bounds this error by `ε/2`. -/
theorem hadamard_encoded_observable_error_le_half (O U U' W W' : Matrix I I ℂ) (ε : ℝ)
    (hO : 0 < ‖O‖)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hU' : U' ∈ Matrix.unitaryGroup I ℂ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hW' : W' ∈ Matrix.unitaryGroup I ℂ)
    (hUε : ‖U' - U‖ ≤ ε / (4 * ‖O‖)) (hWε : ‖W' - W‖ ≤ ε / (4 * ‖O‖)) :
    ‖U'ᴴ * O * W' - Uᴴ * O * W‖ ≤ ε / 2 := by
  have h := hadamard_encoded_observable_error O U U' W W' (ε / (4 * ‖O‖))
    hU hU' hW hW' hUε hWε
  refine h.trans_eq ?_
  have hO' : ‖O‖ ≠ 0 := ne_of_gt hO
  field_simp
  ring

end Qatlib.Papers.LCHamSim23.TimeOrdered
