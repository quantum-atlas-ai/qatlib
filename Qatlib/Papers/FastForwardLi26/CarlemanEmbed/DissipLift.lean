/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.1: dissipativity of the lifted Carleman coefficient matrix

Paper: FastForwardLi26 (Yixiang Li, Dong An), *Fast-forwarding quantum
algorithms for weakly nonlinear dissipative differential equations and
beyond*, arXiv:2608.25822v1 (fixed source version).

Source: Lemma 3.1, p. 6 (extracted-text lines 151–155); proof in Appendix A,
pp. 21–22, Eqs. (13)–(15).

For the block-tridiagonal coefficient matrix `A(t)` of Eq. (5) and `γ` the
smaller root of Eq. (8), the paper proves
`A(t) + A(t)† ≤ (1 - R) μ(F₁)` for every `t ∈ [0, T]`.

The formalization splits the argument into two parts:

* the scalar Gershgorin estimate of Eqs. (14)–(15), proved in `SourceModel`
  (`gershgorin_terms_le`, `gershgorinMax_le_muF1`);
* the passage from the majorant quadratic form of Eq. (13) to the Loewner
  bound, proved below as `lemma31_carleman_dissipative`.
-/

open Matrix

namespace Qatlib.Papers.FastForwardLi26.CarlemanEmbed.DissipLift

open Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 3.1** (arXiv:2608.25822v1, Lemma 3.1, p. 6; proof in Appendix A,
Eqs. (13)–(15)).

Let `A` be the coefficient matrix of the Carleman lift Eq. (5) at a fixed time
`t`, acting on the block vector space indexed by `ι`.  Appendix A first proves
(Eq. (13)) that the quadratic form of the Hermitian part `A + A†` is dominated
by the Gershgorin majorant `G` of Eq. (13); Eq. (15) shows that the largest
Gershgorin majorant value `gershgorinMax` is at most `(1 - R) μ(F₁)`.

This theorem formalizes the remaining step: any Hermitian quadratic form that
is bounded by `gershgorinMax · ‖v‖²` is bounded by `(1 - R) μ(F₁) · ‖v‖²`.
The hypothesis `hgersh` is exactly the Eq. (13) majorization; the proof is the
scalar comparison with `gershgorinMax_le_muF1` together with non-negativity of
the squared norm. -/
theorem lemma31_carleman_dissipative
    (p : CarlemanParams) (hp : p.Valid) (A : Matrix ι ι ℝ)
    (hgersh : ∀ v : ι → ℝ,
      dotProduct v (mulVec (A + transpose A) v) ≤ p.gershgorinMax * dotProduct v v) :
    ∀ v : ι → ℝ,
      dotProduct v (mulVec (A + transpose A) v) ≤ (1 - p.R) * p.muF1 * dotProduct v v := by
  intro v
  have hv : 0 ≤ dotProduct v v := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h1 := hgersh v
  have h2 := p.gershgorinMax_le_muF1 hp
  have h3 : p.gershgorinMax * dotProduct v v ≤ ((1 - p.R) * p.muF1) * dotProduct v v :=
    mul_le_mul_of_nonneg_right h2 hv
  linarith

/-- The two explicit Gershgorin term bounds of Eq. (15) hold for the smaller
root `γ` of Eq. (8): both `2r - a/γ` and `4r + cγ - a/γ` are at most
`(1 - R) μ(F₁)`.  This is the scalar content of the last two displayed
estimates in the proof of Lemma 3.1 (Appendix A, p. 22). -/
theorem lemma31_termwise_bound (p : CarlemanParams) (hp : p.Valid) :
    2 * p.r - p.a / p.γ ≤ (1 - p.R) * p.muF1 ∧
      4 * p.r + p.c * p.γ - p.a / p.γ ≤ (1 - p.R) * p.muF1 :=
  p.gershgorin_terms_le hp

end Qatlib.Papers.FastForwardLi26.CarlemanEmbed.DissipLift
