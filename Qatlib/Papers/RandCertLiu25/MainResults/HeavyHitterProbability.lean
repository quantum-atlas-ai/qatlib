/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9: heavy hitters must occur with probability `(b(1-q)+ε)/(b-1)`

Formalises Lemma 9 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 9 and
Eqs. I.10--I.11, p. 4.

The paper defines, for `τ ∈ (0,1]`, the heavy-hitter probability

  `p(τ) = Pr_{C ∼ D^k, z ∼ A(C)} [ Pr[A(C) = z] ≥ τ / 2^{B/2} ]`,    (I.10)

and `p = p(1)`.  With the von Neumann entropy condition of Theorem 8,
Eq. I.8, Markov's inequality gives (Eq. I.11)

  `Pr[log(1 / Pr[A(C)=z]) ≥ B/2] ≤ H(Z|C) / (B/2) < (bq-1-ε)/(b-1)`,

hence `p > 1 - (bq-1-ε)/(b-1) = (b(1-q)+ε)/(b-1)`.

We model the algorithmic score `log (1 / Pr[A(C)=z])` as a nonnegative
real function on a finite outcome distribution `P` (`FinDist`), prove Markov's
inequality from scratch, and derive the displayed lower bound.  The
score-to-heavy-hitter identification is the definition (I.10); the strict
entropy bound (I.8) enters as the hypothesis on the expectation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.HeavyHitterProbability

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The mass of the event `c ≤ f x` under a finite distribution.  This is the
event probability used by Lemma 9; it is `∑_{x : c ≤ f x} P.prob x`. -/
def eventMass {X : Type*} [Fintype X] [DecidableEq X] (P : FinDist X)
    (f : X → ℝ) (c : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => c ≤ f x), P.prob x

/-- **Markov's inequality** for a nonnegative score on a finite distribution:
`c * Pr[c ≤ f] ≤ E[f]`.  This is the step leading to Eq. I.11. -/
theorem markov_mass_le {X : Type*} [Fintype X] [DecidableEq X] (P : FinDist X)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (c : ℝ) (hc : 0 < c) :
    c * eventMass P f c ≤ P.expect f := by
  classical
  rw [eventMass, Finset.mul_sum, FinDist.expect]
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => c ≤ f x), c * P.prob x ≤
      ∑ x ∈ Finset.univ.filter (fun x => c ≤ f x), P.prob x * f x := by
    apply Finset.sum_le_sum
    intro x hx
    have hc_le : c ≤ f x := (Finset.mem_filter.mp hx).2
    have hp : 0 ≤ P.prob x := P.nonneg x
    nlinarith
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => c ≤ f x), P.prob x * f x ≤
      ∑ x, P.prob x * f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x _ _
    exact mul_nonneg (P.nonneg x) (hf x)
  linarith

/-- **Lemma 9** (Eq. I.11).  If the entropy of the device's output obeys the
strict bound (I.8), then the probability that the output is a heavy hitter
(i.e. `score < B/2`) exceeds `(b(1-q)+ε)/(b-1)`. -/
theorem lemma9_heavy_hitter_probability {X : Type*} [Fintype X] [DecidableEq X]
    (P : FinDist X) (score : X → ℝ) (hscore : ∀ x, 0 ≤ score x)
    (B b q ε : ℝ) (hB : 0 < B) (hb : 1 < b)
    (hEnt : P.expect score < (B / 2) * (b * q - 1 - ε) / (b - 1)) :
    (b * (1 - q) + ε) / (b - 1) < 1 - eventMass P score (B / 2) := by
  classical
  have hmark := markov_mass_le P score hscore (B / 2) (by linarith)
  -- Rewrite the Markov bound into `tail ≤ 2 E / B`.
  have htail : eventMass P score (B / 2) ≤ P.expect score / (B / 2) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hbound : P.expect score / (B / 2) < (b * q - 1 - ε) / (b - 1) := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < B / 2)]
    calc P.expect score < (B / 2) * (b * q - 1 - ε) / (b - 1) := hEnt
      _ = ((b * q - 1 - ε) / (b - 1)) * (B / 2) := by ring
  have harith : (b * (1 - q) + ε) / (b - 1) = 1 - (b * q - 1 - ε) / (b - 1) := by
    have hbne : b - 1 ≠ 0 := by linarith
    field_simp
    ring_nf
  rw [harith]
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.HeavyHitterProbability
