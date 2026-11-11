/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactionMech16.MainResults.Source.Lemma4EvoErrorToGenerator

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5: a Hermitian generator for an approximate unitary family

Source: arXiv:1605.03590v2, Appendix D, Lemma 5 (p.15).

The paper states: for Hermitian `H` and a unitary family `U(t)` with
`‖e^{-iHt} - U(t)‖₂ ≤ ε t`, for every `t` there is a Hermitian `H̃(t)` with
`U(t) = e^{-iH̃(t)t}` and `‖H - H̃(t)‖₂ ≤ ε`.  The proof takes the principal
matrix logarithm of `U(t)` and appeals to the sharpness of
`‖e^{-iHt} - e^{-iKt}‖ ≤ ‖H - K‖ t` as `t → 0`.

This file formalizes the quantitative part of that argument in the form in
which it is rigorous: if a *single* Hermitian `K` generates the whole family,
`U(t) = e^{-iKt}` for every `t ≥ 0`, then the approximation hypothesis forces
`‖H - K‖₂ ≤ ε`.  The conclusion is immediate from Lemma 4 with the constant
function `γ = ε`.

Boundary / paper gap: the existence of a Hermitian logarithm for an arbitrary
unitary matrix (the principal-logarithm step) is not available in Mathlib, and
the paper's pointwise choice `K = K(t)` does not literally satisfy the uniform
hypothesis of Lemma 4 because `K(t)` may depend on `t`.  The module documents
this restriction instead of asserting the pointwise existence claim.  The
`t = 0` case of the paper's statement is also degenerate: at `t = 0` the
generator is unconstrained (`e^{0} = 1`), so the bound `‖H - K‖ ≤ ε` cannot
hold without an extra hypothesis.

Fixed source: arXiv:1605.03590v2 (2016), Lemma 5, p.15.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- arXiv:1605.03590v2, Lemma 5 (p.15), uniform-generator form: if a Hermitian
`K` generates the unitary family `U(t) = e^{-iKt}` for all `t ≥ 0` and
`‖e^{-iHt} - U(t)‖ ≤ ε t`, then `‖H - K‖ ≤ ε`. -/
theorem lemma5_hermitian_log_generator
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H K : Matrix I I ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (U : ℝ → Matrix I I ℂ)
    (hU : ∀ t : ℝ, 0 ≤ t → U t = matrixExpEvo K t)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖matrixExpEvo H t - U t‖ ≤ ε * t) :
    ‖H - K‖ ≤ ε := by
  have hb : ∀ t : ℝ, 0 ≤ t → ‖matrixExpEvo H t - matrixExpEvo K t‖ ≤ t * ε := by
    intro t ht
    calc
      ‖matrixExpEvo H t - matrixExpEvo K t‖ = ‖matrixExpEvo H t - U t‖ := by
        rw [hU t ht]
      _ ≤ ε * t := hbound t ht
      _ = t * ε := by ring
  have hgap := lemma4_evo_error_to_generator_gap H K hH hK (fun _ => ε)
    monotoneOn_const continuousOn_const hb 0 le_rfl
  simpa using hgap

end Qatlib.Papers.ReactionMech16.MainResults.Source
