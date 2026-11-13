/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PathIntegralVariance — vanishing PIMC variance on disconnected complexes and complete graphs

Source: *Analyzing Prospects for Quantum Advantage in Topological Data Analysis*,
McArdle–Gilyén–Turaev (arXiv:2209.13581).

Propositions 12 (`c021`) and 13 (`c022`), Appendix G §4: the path-integral
Monte-Carlo (PIMC) estimator of the Betti number has **zero variance** when the
underlying complex is disconnected (Prop. 12) and when it is the complete graph
(Prop. 13). In both cases the mechanism is that the PIMC path weights are all
equal, so the empirical variance collapses to `0`. We model the estimator's
variance as the population variance of the finite set of path contributions and
prove that constant contributions give zero variance; the geometric input
"disconnected / complete ⟹ constant path weights" is the paper's argument and is
recorded as the hypothesis `hconst` (modeling gap: the PIMC path measure itself is
not constructed here).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoAdvantage22.MainResults.Variance

open Finset

/-- The mean of a finite multiset of real path weights. -/
def pimcMean (weights : Finset ℝ) : ℝ := weights.sum (fun x => x) / (weights.card : ℝ)

/-- The (population) variance of a finite multiset of real path weights. -/
def pimcVariance (weights : Finset ℝ) : ℝ :=
  weights.sum (fun x => (x - pimcMean weights) ^ 2) / (weights.card : ℝ)

/-- **Variance of a constant family (paper mechanism behind Props. 12–13).**
If every PIMC path contribution equals the same value `c`, the population variance
is zero. -/
theorem pimcVariance_eq_zero_of_const (weights : Finset ℝ) (c : ℝ)
    (h : ∀ x ∈ weights, x = c) (hne : weights.Nonempty) :
    pimcVariance weights = 0 := by
  have hcard : (weights.card : ℝ) ≠ 0 := by
    have hpos : 0 < weights.card := Finset.card_pos.mpr hne
    exact_mod_cast hpos.ne'
  have hmean : pimcMean weights = c := by
    unfold pimcMean
    have hsum_eq : weights.sum (fun x => x) = weights.sum (fun _ => c) :=
      Finset.sum_congr rfl (fun x hx => h x hx)
    rw [hsum_eq]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm, mul_div_cancel_right₀ c hcard]
  have hsum : weights.sum (fun x => (x - pimcMean weights) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [h x hx, hmean]
    ring
  unfold pimcVariance
  rw [hsum, zero_div]

/-- **Proposition 12 (arXiv:2209.13581, Appendix G §4).** If the complex is
disconnected, the PIMC path weights are constant, hence the estimator variance is
zero.

Fixed arXiv:2209.13581. Modeling gap: the PIMC path measure is not constructed;
the geometric fact "disconnected ⟹ all path weights equal" is taken as the
hypothesis `hconst`. A full geometric account requires a path measure on
spanning-tree weightings and a proof of constancy of the weights. -/
theorem proposition12_variance_zero_disconnected (weights : Finset ℝ) (c : ℝ)
    (hne : weights.Nonempty) (hconst : ∀ x ∈ weights, x = c) :
    pimcVariance weights = 0 :=
  pimcVariance_eq_zero_of_const weights c hconst hne

/-- **Proposition 13 (arXiv:2209.13581, Appendix G §4).** For the complete graph
`K_N`, the PIMC path weights are constant, hence the estimator variance is zero.

Fixed arXiv:2209.13581. Same modeling gap as Prop. 12: the completeness argument
yielding constant path weights is the hypothesis `hconst`. Edge-transitivity and
regularity of the complete graph are relevant to the geometric constancy argument. -/
theorem proposition13_variance_zero_complete (weights : Finset ℝ) (c : ℝ)
    (hne : weights.Nonempty) (hconst : ∀ x ∈ weights, x = c) :
    pimcVariance weights = 0 :=
  pimcVariance_eq_zero_of_const weights c hconst hne

end Qatlib.Papers.TopoAdvantage22.MainResults.Variance
