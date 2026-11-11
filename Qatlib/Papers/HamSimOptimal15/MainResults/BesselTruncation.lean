/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel

set_option backward.isDefEq.respectTransparency false

/-!
# BesselTruncation — Lemmas 8 and 11 of arXiv:1501.01715v3

Paper: Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal
dependence on all parameters*, arXiv:1501.01715v3 (2015-12-07).

* Lemma 8, p.10, eq.(43): with the coefficients `a_m` of eq.(42), for `|z| ≤ k`,
  `‖V_k − V_∞‖ = O((‖H‖/Xd)(z/2)^{k+1}/k!)`.  Its proof (Appendix, eq.(84)–(88))
  rests on the pointwise Bessel bound `|J_m(z)| ≤ (|z|/2)^{|m|}/|m|!` (eq.(84)) and the
  geometric tail estimate (85).  The repository already has `abs_lcBesselJ_le`
  (`|lcBesselJ k τ| ≤ (τ/2)^k/k!`) for the power-series Bessel function `lcBesselJ`.
* Lemma 11, p.12, eq.(51): `S(z) := ∑_{m∈ℤ} |J_m(z)|` is `O(√|z|)`.

The operator-level statements `V_k`/`V_∞` of Lemma 8 need the Szegedy quantum-walk
operator `U` and its eigenvalues `μ±` of eq.(7), which the repository does not provide;
the analytic core that the paper actually estimates (eq.(85)) is stated below.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamSimOptimal15.MainResults

open Qatlib.Concepts.QsvtCore.PhaseExistence

/-- **Lemma 8, analytic core, arXiv:1501.01715v3 p.10, eq.(84)–(85)**: for `0 ≤ z ≤ k`
the tail of the Bessel series beyond order `k` is bounded by
`2·(|z|/2)^{k+1}/(k+1)!`, which is the estimate the paper combines with Stirling's
formula to obtain eq.(43).

(`|J_m(−z)| = |J_m(z)|` extends the statement to negative `z`; this is not needed for
the `|z| ≤ k` use in Theorem 3, where `z = −1/2`.)

Registered as a proposition, not proved.  Current Lean gap: `lcBesselJ` is the power
series of eq.(84)'s right side, so `abs_lcBesselJ_le` gives the pointwise bound, but the
file has no summability/geometric-series package for `∑' m, (z/2)^m/m!` at `z/2 < 1`;
in particular there is no lemma `∑'_{m ≥ k+1} (z/2)^m/m! ≤ 2 (z/2)^{k+1}/(k+1)!` for
`z ≤ k`.

Candidate reusable dependencies: `abs_lcBesselJ_le` (this file's import),
`Real.summable_pow_div_factorial`, `tsum_geometric_of_norm_lt_one`,
`Real.exp_eq_tsum`.

Suggested follow-up tactic: bound each term with `abs_lcBesselJ_le`, rewrite
`∑'_{m≥k+1} (z/2)^m/m! = (z/2)^{k+1}/(k+1)! * ∑'_{j} (z/2)^j * ((k+1)!/(k+1+j)!)`,
then `∑'_{j} (1/2)^j = 2` by `tsum_geometric_of_norm_lt_one` with ratio `1/2`. -/
def lemma8_bessel_tail (k : ℕ) (z : ℝ) : Prop :=
  0 ≤ z → z ≤ (k : ℝ) →
    (∑' m : ℕ, |lcBesselJ (m + k + 1) z|) ≤
      2 * ((z / 2) ^ (k + 1) / ((k + 1).factorial : ℝ))

/-- **Lemma 11, arXiv:1501.01715v3 p.12, eq.(51)**: the absolute Bessel sum
`S(z) = ∑_{m∈ℤ} |J_m(z)|` is `O(√z)` as `z → ∞`.

Registered as a proposition, not proved.  Current Lean gap: the repository has the
pointwise bound `abs_lcBesselJ_le`, but not the identity `∑_m J_m(z)^2 = 1` (the
paper's Appendix proof of Lemma 11 uses the recurrence
`J_{m-1}(z) + J_{m+1}(z) = (2m/z)J_m(z)` together with that normalisation to split
the sum into a `√z`-sized central band and a geometrically decaying tail).  No
`∑_m (lcBesselJ m z)^2 = 1` statement exists.

Candidate reusable dependencies: `abs_lcBesselJ_le`,
`lcBesselJacobiAnger` (Jacobi–Anger identity for `lcBesselJ`).

Suggested follow-up tactic: prove `∑' m : ℤ, (lcBesselJ m.natAbs z)^2 = 1` from
`lcBesselJacobiAnger` at `μ = 1`, then use the recurrence to show that at most
`O(√z)` orders exceed `1/√z`, and bound the remaining tail by
`∑_{|m| > √z} |J_m| ≤ √(∑ J_m²) * √(#tail)` via Cauchy–Schwarz. -/
def lemma11_bessel_sum_isBigO : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
    (∑' m : ℤ, |lcBesselJ m.natAbs z|) ≤ C * Real.sqrt z

end Qatlib.Papers.HamSimOptimal15.MainResults
