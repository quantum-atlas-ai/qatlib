/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Small-action perturbation (Lemma 4.5)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 4.5, page 21.

The private block of a local transducer is a compression of the full transducer
by the projection `P` onto the private subspace: `S_11 = P S P`.  The reference
transducer has private block `S_11^{(0)} = P S^{(0)} P`.  The paper bounds the
difference of private blocks by the difference of the full transducers,

`‖S_11 - S_11^{(0)}‖ ≤ ‖S - S^{(0)}‖`,

before converting the right-hand side into the small-action scale `√s`.  The
compression inequality is the content we formalize: for a contraction `P`, the
sandwich by `P` is a contraction on the space of bounded operators with its
operator norm.  Since `P` is an orthogonal projection (a self-adjoint
contraction), `‖P‖ ≤ 1`, and submultiplicativity of the operator norm gives the
claim.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.SmallAction

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Lemma 4.5, compression inequality.**  A contraction projection `P`
compresses the operator-norm difference: `‖P S P - P S₀ P‖ ≤ ‖S - S₀‖`. -/
theorem private_block_lipschitz (P : E →L[ℂ] E) (hP : ‖P‖ ≤ 1)
    (S S0 : E →L[ℂ] E) :
    ‖P.comp (S.comp P) - P.comp (S0.comp P)‖ ≤ ‖S - S0‖ := by
  have hsub : P.comp (S.comp P) - P.comp (S0.comp P)
      = P.comp ((S - S0).comp P) := by
    ext x
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  rw [hsub]
  have h1 : ‖P.comp ((S - S0).comp P)‖ ≤ ‖P‖ * ‖(S - S0).comp P‖ :=
    ContinuousLinearMap.opNorm_comp_le (h := P) ((S - S0).comp P)
  have h2 : ‖(S - S0).comp P‖ ≤ ‖S - S0‖ * ‖P‖ :=
    ContinuousLinearMap.opNorm_comp_le (h := S - S0) P
  have hP0 : (0 : ℝ) ≤ ‖P‖ := norm_nonneg P
  have hd0 : (0 : ℝ) ≤ ‖S - S0‖ := norm_nonneg (S - S0)
  have hstep : ‖P‖ * ‖(S - S0).comp P‖ ≤ ‖P‖ * (‖S - S0‖ * ‖P‖) :=
    mul_le_mul_of_nonneg_left h2 hP0
  have hsq : ‖P‖ * ‖P‖ ≤ (1 : ℝ) := by
    calc ‖P‖ * ‖P‖ ≤ 1 * ‖P‖ := mul_le_mul_of_nonneg_right hP hP0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = 1 := by ring
  have hfinal : ‖P‖ * (‖S - S0‖ * ‖P‖) ≤ ‖S - S0‖ := by
    calc ‖P‖ * (‖S - S0‖ * ‖P‖) = ‖S - S0‖ * (‖P‖ * ‖P‖) := by ring
      _ ≤ ‖S - S0‖ * 1 := mul_le_mul_of_nonneg_left hsq hd0
      _ = ‖S - S0‖ := mul_one _
  exact le_trans h1 (le_trans hstep hfinal)

/-- The private block is exactly the compressed operator. -/
def privateBlock (P S : E →L[ℂ] E) : E →L[ℂ] E := P.comp (S.comp P)

/-- **Lemma 4.5, difference form.**  The private-block difference is the
compressed difference of the full transducers. -/
theorem privateBlock_sub (P S S0 : E →L[ℂ] E) :
    privateBlock P S - privateBlock P S0 = P.comp ((S - S0).comp P) := by
  unfold privateBlock
  ext x
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]

end Qatlib.Papers.ShallowLind26.ShallowSim.SmallAction
