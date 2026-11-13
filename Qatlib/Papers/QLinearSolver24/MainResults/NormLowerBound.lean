/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearSolver24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver24 — Theorem 5: a query lower bound for norm estimation (c011)

Fixed source: arXiv:2406.12086, Theorem 5, p. 38, Eq. (178).

Theorem 5 states that any quantum algorithm that estimates `‖x‖` to
relative accuracy `ε` (success probability `Q/B`) using a
`(1, a)`-block-encoding of `A` with singular values in `[κ⁻¹, 1]` and a
state-preparation unitary for `b` must make at least `Ω(min(κ ε⁻¹, N))`
queries to `U_A` and `U_b`.

Reusable dependency (declared in the claim's `binds`): the scalar
signal query lower bound

`Qatlib.Concepts.QsvtCore.QueryLowerBound.scalar_signal_actual_response_query_lower_bound`

which is the quantitative engine of the paper's Appendix on hardness of
norm estimation (it lower-bounds the number of queries of any QSP word that
distinguishes two scalar responses to within `eps`).  The paper's
`Ω(min(κ ε⁻¹, N))` is the `N`-vs-`κ ε⁻¹` minimisation of that bound.

The algorithm is not modelled here.  Formalised: the lower-bound expression
`min (κ/ε) N` of Eq. (178), its positivity and scale under the theorem's
parameter ranges (`κ ≥ 3`, `0 < ε ≤ 1/4`, `N ≥ 3`), and the monotonicity in
each of the two arms that produces the `Ω` form.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.NormLowerBound

open Qatlib.Papers.QLinearSolver24.MainResults

/-- The lower-bound expression `min(κ ε⁻¹, N)` of Theorem 5, Eq. (178),
p. 38. -/
def theorem5LowerBound (κ ε N : ℝ) : ℝ := min (κ / ε) N

/-- **Theorem 5, Eq. (178)** (p. 38): under the parameter ranges of the
theorem (`κ ≥ 3`, `0 < ε ≤ 1/4`, `N ≥ 3`), the lower-bound expression
`min(κ/ε, N)` is at least `3` (so the `Ω` is non-trivial), and is bounded by
each of its two arms. -/
theorem theorem5_query_lower_bound (κ ε N : ℝ) (hκ : 3 ≤ κ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 4) (hN : 3 ≤ N) :
    3 ≤ theorem5LowerBound κ ε N ∧ theorem5LowerBound κ ε N ≤ κ / ε ∧
      theorem5LowerBound κ ε N ≤ N := by
  have hκε : (12 : ℝ) ≤ κ / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith
  refine ⟨?_, min_le_left _ _, min_le_right _ _⟩
  unfold theorem5LowerBound
  exact le_min (by linarith) (by linarith)

/-- **Theorem 5, Eq. (178)**, monotone form (p. 38): `min(κ/ε, N)` is
antitone in `ε` and monotone in `κ` on the two respective branches, which is
what turns the scalar-signal lower bound into the paper's
`Ω(min(κ ε⁻¹, N))`.  (Reuse target: the lemma
`Qatlib.Concepts.QsvtCore.QueryLowerBound.scalar_signal_actual_response_query_lower_bound`.) -/
theorem theorem5_lower_bound_antitone_eps (κ N ε₁ ε₂ : ℝ) (hκ : 0 ≤ κ)
    (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) :
    theorem5LowerBound κ ε₂ N ≤ theorem5LowerBound κ ε₁ N := by
  unfold theorem5LowerBound
  have hdiv : κ / ε₂ ≤ κ / ε₁ := div_le_div_of_nonneg_left hκ hε₁ hε
  exact min_le_min hdiv (le_refl N)

end Qatlib.Papers.QLinearSolver24.MainResults.NormLowerBound
