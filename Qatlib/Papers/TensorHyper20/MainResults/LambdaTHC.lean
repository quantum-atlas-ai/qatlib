/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.TensorHyper20.MainResults.Definitions

/-!
# Coefficient mass for tensor hypercontraction

Defines the two-body coefficient mass `lambdaZeta` and total tensor hypercontraction coefficient
mass `lambdaTHC` used in [LeeEtAl2021]. The total is the absolute one-body coefficient sum plus
one half of the absolute `ζ` coefficient sum.

The comparison theorems bound `lambdaTHC` by a multiple of `lambdaZeta` whenever the one-body
contribution satisfies the corresponding hypothesis.

## Main statements

* `lambdaTHC_eq`: expands the total coefficient mass.
* `lambdaTHC_asymptotic`: bounds the total using a bound on the one-body contribution.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC

open scoped BigOperators

/-- One half of the sum of the absolute values of all entries of `ζ`. -/
noncomputable def lambdaZeta {M : ℕ} (ζ : Fin M → Fin M → ℝ) : ℝ :=
  (1 / 2) * ∑ μ, ∑ ν, |ζ μ ν|

/-- The sum of the absolute one-body coefficients plus the two-body coefficient mass
`lambdaZeta`. -/
noncomputable def lambdaTHC {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ) : ℝ :=
  ∑ ℓ, |t ℓ| + lambdaZeta ζ

/-- Expands `lambdaTHC` as the absolute one-body sum plus one half of the absolute `ζ` entry
sum. -/
theorem lambdaTHC_eq {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ) :
    lambdaTHC t ζ = ∑ ℓ, |t ℓ| + (1 / 2) * ∑ μ, ∑ ν, |ζ μ ν| := rfl

/-- The two-body coefficient mass `lambdaZeta` is nonnegative. -/
theorem lambdaZeta_nonneg {M : ℕ} (ζ : Fin M → Fin M → ℝ) : 0 ≤ lambdaZeta ζ := by
  unfold lambdaZeta
  positivity

/-- If the absolute one-body sum is at most `lambdaZeta`, then the total coefficient mass is at
most twice `lambdaZeta`. -/
theorem lambdaTHC_le_two_lambdaZeta {K M : ℕ} (t : Fin K → ℝ)
    (ζ : Fin M → Fin M → ℝ) (h : ∑ ℓ, |t ℓ| ≤ lambdaZeta ζ) :
    lambdaTHC t ζ ≤ 2 * lambdaZeta ζ := by
  unfold lambdaTHC
  linarith

/-- If the absolute one-body sum is at most `c * lambdaZeta`, then `lambdaTHC` is at most `(c +
1) * lambdaZeta`. -/
theorem lambdaTHC_asymptotic {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ)
    (c : ℝ) (h : ∑ ℓ, |t ℓ| ≤ c * lambdaZeta ζ) :
    lambdaTHC t ζ ≤ (c + 1) * lambdaZeta ζ := by
  unfold lambdaTHC
  have hz := lambdaZeta_nonneg ζ
  linarith

end Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC
