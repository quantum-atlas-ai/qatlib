/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c002 — Proposition 16, Eq. (32)

Shao--Liu, arXiv:2010.15027v2, Proposition 16, p. 9.

Let `x̃` be the superposition (15) of exact ODE solutions and `|C⟩` the state
returned by the quantum linear solver for the discretised system (26).  The
proposition claims

`‖ |x̃⟩ - (U_p F ⊗ I)|C⟩ ‖ ≤ 2ε`,   (32)

because the two errors entering the comparison — the finite-difference error of
the ODE discretisation and the linear-solver error — are each bounded by `ε`.

The formal content is the triangle inequality: on any normed space, two
`ε`-close approximation steps compose to a `2ε`-close approximation.  The
quantum-state normalisation and the isometry `U_p F ⊗ I` are carried by the
ambient normed space; the proposition's two analytic estimates are the explicit
hypotheses `hdiscretisation` and `hsolver`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **Proposition 16, Eq. (32).**  Two approximation errors of size `ε` add up
to at most `2ε` in the ambient norm. -/
theorem prop16_error_bound {E : Type*} [NormedAddCommGroup E]
    (xTilde xExact xC : E) (ε : ℝ) (hε : 0 ≤ ε)
    (hdiscretisation : ‖xTilde - xExact‖ ≤ ε)
    (hsolver : ‖xExact - xC‖ ≤ ε) :
    ‖xTilde - xC‖ ≤ 2 * ε := by
  have hsub : xTilde - xC = (xTilde - xExact) + (xExact - xC) := by abel
  rw [hsub]
  have htri := norm_add_le (xTilde - xExact) (xExact - xC)
  linarith

/-- The additive two-parameter form of Eq. (32): an `ε₁` discretisation error
and an `ε₂` solver error give `ε₁ + ε₂` total error. -/
theorem prop16_error_bound_additive {E : Type*} [NormedAddCommGroup E]
    (xTilde xExact xC : E) (ε₁ ε₂ : ℝ)
    (hdiscretisation : ‖xTilde - xExact‖ ≤ ε₁)
    (hsolver : ‖xExact - xC‖ ≤ ε₂) :
    ‖xTilde - xC‖ ≤ ε₁ + ε₂ := by
  have hsub : xTilde - xC = (xTilde - xExact) + (xExact - xC) := by abel
  rw [hsub]
  have htri := norm_add_le (xTilde - xExact) (xExact - xC)
  linarith

end Qatlib.Papers.GenEigenODE20.MainResults
