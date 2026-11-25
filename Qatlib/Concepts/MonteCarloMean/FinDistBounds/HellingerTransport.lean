/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence

@[expose] public section

/-!
# Two-sided Hellinger--total-variation comparison

The shared finite-law library proves only one comparison between the total variation distance and
the squared Hellinger expression `hellingerSq p q = ∑ x, (√(p x) - √(q x))²`: the inequality
`tv² ≤ hellingerSq` in
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv_sq_le_hellinger`,
which gives the upper side `tv ≤ √ hellingerSq`. This module supplies the missing lower side
`hellingerSq ≤ 2 tv` and packages the two directions against the shared
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist`.

The lower side is the pointwise estimate `(√a - √b)² ≤ |a - b|` summed coordinatewise. It does
not need strictly positive masses, unlike the KL comparisons in the shared finite-law module.

Boundary: only finite distributions are covered, and no sharpness or equality analysis is
included. The statement is the finite-mass specialization used by paper-layer lower bounds.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence

variable {X : Type} [Fintype X] [DecidableEq X]

/-- For nonnegative reals, the squared difference of the square roots is at most the absolute
difference: writing both sides through `√a · √b` reduces the claim to `min a b ≤ √(a b)`. -/
theorem sq_sqrt_sub_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have haa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hbb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hkey : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
    nlinarith [hsa, hsb]
  rcases le_total a b with hab | hba
  · have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
    have hmul : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * Real.sqrt b :=
      mul_le_mul_of_nonneg_left hsab haa
    rw [abs_of_nonpos (by linarith), hkey]
    nlinarith [hmul, hsa]
  · have hsba : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
    have hmul : Real.sqrt b * Real.sqrt b ≤ Real.sqrt b * Real.sqrt a :=
      mul_le_mul_of_nonneg_left hsba hbb
    rw [abs_of_nonneg (by linarith), hkey]
    nlinarith [hmul, hsb]

/-- The squared Hellinger expression is at most twice the total variation distance. -/
theorem hellingerSq_le_two_mul_tvDist (p q : FinDist X) :
    hellingerSq p q ≤ 2 * tvDist p q := by
  have h : hellingerSq p q ≤ ∑ x, |p.prob x - q.prob x| :=
    Finset.sum_le_sum fun x _ =>
      sq_sqrt_sub_le_abs_sub (p.nonneg x) (q.nonneg x)
  unfold tvDist
  linarith

/-- Half of the squared Hellinger expression is at most the total variation distance. -/
theorem half_hellingerSq_le_tvDist (p q : FinDist X) :
    (1 / 2) * hellingerSq p q ≤ tvDist p q := by
  have h := hellingerSq_le_two_mul_tvDist p q
  linarith

/-- The total variation expression of the finite-information module agrees with `tvDist`. -/
theorem tv_eq_tvDist (p q : FinDist X) : tv p q = tvDist p q := by
  unfold tv tvDist
  ring

/-- The total variation distance is at most the square root of the squared Hellinger
expression; this is the upper side already contained in `tv_sq_le_hellinger`. -/
theorem tvDist_le_sqrt_hellingerSq (p q : FinDist X) :
    tvDist p q ≤ Real.sqrt (hellingerSq p q) := by
  have hsq : tvDist p q ^ 2 ≤ hellingerSq p q := by
    have h := tv_sq_le_hellinger p q
    rw [tv_eq_tvDist] at h
    exact h
  have htv : 0 ≤ tvDist p q := by
    unfold tvDist
    positivity
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq htv] at hs

/-- Two-sided comparison: `hellingerSq / 2 ≤ tvDist ≤ √ hellingerSq`. -/
theorem hellingerSq_tvDist_two_sided (p q : FinDist X) :
    (1 / 2) * hellingerSq p q ≤ tvDist p q ∧
      tvDist p q ≤ Real.sqrt (hellingerSq p q) :=
  ⟨half_hellingerSq_le_tvDist p q, tvDist_le_sqrt_hellingerSq p q⟩

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
