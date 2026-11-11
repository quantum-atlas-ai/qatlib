/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
# The two-weight partial symmetric function

This module defines the partial symmetric Boolean function and polynomial approximation model
used in [NayakWu1998]. The function is one at weight `ℓ`, zero at weight `ℓ'`, and undefined at
other weights; approximation also requires a bounded range on the entire Boolean cube.

The parameters `deltaL` and `mSelect` describe the distance between the promised weights and the
weight farther from the midpoint. They determine the two-term expression `lowerBound`, while
`BigOmega` and `BigO` record eventual positive-multiple comparisons for sequences.

## Main statements

* `partialSymmetric` and `ApproximatesWithin`: define the promise function and its approximation
  requirements.
- `deltaL`, `mSelect`, and `lowerBound`: encode the parameters of the degree and query bounds.
- `BigOmega` and `BigO`: express asymptotic lower and upper comparisons.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMedianStats98.MainResults.Model

open MvPolynomial

/-- The Hamming weight of a Boolean input, defined as the number of coordinates equal to `true`. -/
def weight {n : ℕ} (X : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => X i = true)).card

/-- The partial Boolean function returning `true` at weight `ℓ`, `false` at weight `ℓ'`, and no
value at other weights. The `ℓ` branch has priority if the two weights coincide. -/
def partialSymmetric (n ℓ ℓ' : ℕ) (X : Fin n → Bool) : Option Bool :=
  if weight X = ℓ then some true
  else if weight X = ℓ' then some false
  else none

/-- Evaluates a real multivariate polynomial on a Boolean input by sending `true` to one and
`false` to zero. -/
noncomputable def evalBool {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (X : Fin n → Bool) : ℝ :=
  p.eval (fun i => if X i then (1 : ℝ) else 0)

/-- A polynomial approximates the two-weight promise within `c` when it lies in `[-c, 1 + c]` on
the entire Boolean cube, is within `c` of one at weight `ℓ`, and is within `c` of zero at
weight `ℓ'`. -/
noncomputable def ApproximatesWithin {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (ℓ ℓ' : ℕ) (c : ℝ) : Prop :=
  (∀ X : Fin n → Bool, evalBool p X ∈ Set.Icc (-c) (1 + c)) ∧
  (∀ X : Fin n → Bool, weight X = ℓ → |evalBool p X - 1| ≤ c) ∧
  (∀ X : Fin n → Bool, weight X = ℓ' → |evalBool p X| ≤ c)

/-- The distance between the two natural-number weights, viewed as a real number. -/
def deltaL (ℓ ℓ' : ℕ) : ℝ := (Nat.dist ℓ ℓ' : ℝ)

/-- Selects the promised weight farther from `n/2`, viewed as a real number, choosing `ℓ` in a
tie. -/
noncomputable def mSelect (n ℓ ℓ' : ℕ) : ℝ :=
  if |(n : ℝ) / 2 - (ℓ : ℝ)| ≥ |(n : ℝ) / 2 - (ℓ' : ℝ)| then (ℓ : ℝ) else (ℓ' : ℝ)

/-- The expression `sqrt(n / Δ) + sqrt(m*(n-m)) / Δ`, where `Δ = deltaL ℓ ℓ'` and `m = mSelect n
ℓ ℓ'`, appearing in the degree and query bounds of [NayakWu1998]. -/
noncomputable def lowerBound (n ℓ ℓ' : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / deltaL ℓ ℓ') +
    Real.sqrt (mSelect n ℓ ℓ' * ((n : ℝ) - mSelect n ℓ ℓ')) / deltaL ℓ ℓ'

/-- An eventual lower comparison of real sequences: some positive constant multiple of `g n` is
at most `f n` for all sufficiently large `n`. -/
def BigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * g n ≤ f n

/-- An eventual upper comparison of real sequences: `f n` is at most some positive constant
multiple of `g n` for all sufficiently large `n`. -/
def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ c * g n

end Qatlib.Papers.QMedianStats98.MainResults.Model
