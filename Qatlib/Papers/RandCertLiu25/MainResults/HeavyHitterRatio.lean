/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11: the yes/no gap ratio of heavy-hitter expectations

Formalises Lemma 11 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 11,
Eqs. I.20, I.25--I.26, p. 5.

The paper defines, for `τ ∈ [0,1]`, the yes-case and no-case expectations

  `μ1(τ) = E_{C∼D^k, s∼p_C}[Y_τ(C,s)]`,
  `μ0(τ) = E_{C∼D^k, s∼U^k}[Y_τ(C,s)]`,

where `Y_τ` is the indicator that the output has a heavy-hitter component above
`τ/2^{B/2}` with at least one matching coordinate.  Lemma 10 and a union bound
give (Eq. I.25)

  `μ1(τ) ≥ (bk/N)·(p(τ)+q-1) - O(1/N²)`,

while the uniform no-case gives exactly (Eq. I.26)

  `μ0(τ) = (k/N)·p(τ)`.

Dividing yields the displayed Eq. I.20

  `μ1(τ)/μ0(τ) ≥ b·(p(τ)+q-1)/p(τ)`.

We prove the exact algebraic content of that division, in both the idealised
form (I.20, with the lower bound taken literally) and the form with the
explicit `O(1/N²)` error term retained.  The paper suppresses the error when
writing I.20; the second theorem records the honest error propagation.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.HeavyHitterRatio

/-- **Lemma 11** (Eq. I.20), idealised division: if the no-case expectation is
exactly `(k/N)·p` and the yes-case expectation dominates
`(bk/N)·(p+q-1)`, then the ratio of expectations is at least
`b·(p+q-1)/p`. -/
theorem lemma11_gap_ratio (b k N p q mu1 mu0 : ℝ)
    (hb : 0 < b) (hk : 0 < k) (hN : 0 < N) (hp : 0 < p)
    (hpq : 0 ≤ p + q - 1)
    (hmu0 : mu0 = (k / N) * p)
    (hmu1 : (b * k / N) * (p + q - 1) ≤ mu1) :
    b * ((p + q - 1) / p) ≤ mu1 / mu0 := by
  have hden : 0 < (k / N) * p := by positivity
  rw [hmu0]
  have hA : b * ((p + q - 1) / p) * ((k / N) * p) = (b * k / N) * (p + q - 1) := by
    field_simp
  rw [le_div_iff₀ hden, hA]
  exact hmu1

/-- **Lemma 11 with the `O(1/N²)` error retained.**  If
`μ1(τ) ≥ (bk/N)(p+q-1) - err`, then
`μ1/μ0 ≥ b(p+q-1)/p - err·N/(k·p)`. -/
theorem lemma11_gap_ratio_with_error (b k N p q mu1 mu0 err : ℝ)
    (hb : 0 < b) (hk : 0 < k) (hN : 0 < N) (hp : 0 < p)
    (hmu0 : mu0 = (k / N) * p)
    (hmu1 : (b * k / N) * (p + q - 1) - err ≤ mu1) :
    b * ((p + q - 1) / p) - err * N / (k * p) ≤ mu1 / mu0 := by
  have hden : 0 < (k / N) * p := by positivity
  have hkpos : 0 < k * p := by positivity
  rw [hmu0]
  have hA : b * ((p + q - 1) / p) * ((k / N) * p) = (b * k / N) * (p + q - 1) := by
    field_simp
  have hB : err * N / (k * p) * ((k / N) * p) = err := by
    field_simp
  have hsub : (b * ((p + q - 1) / p) - err * N / (k * p)) * ((k / N) * p) =
      (b * k / N) * (p + q - 1) - err := by
    rw [sub_mul, hA, hB]
  rw [le_div_iff₀ hden, hsub]
  exact hmu1

end Qatlib.Papers.RandCertLiu25.MainResults.HeavyHitterRatio
