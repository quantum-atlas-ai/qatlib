/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.SubGaussian

/-!
# Specification of tensor grid concentration

`TensorChebyshevGridBound` specifies a cardinality bound for degree-`k` tensor polynomials whose
coefficients have absolute value at most one. The grid is finite, nonempty, symmetric, and
contained in `[-1/2, 1/2]`, as in the concentration argument supporting
[GilyenArunachalamWiebe2019].

## Main statements

* `TensorChebyshevGridBound`: a second-moment threshold gives a tail fraction at most
  `r^(-2*k)`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

namespace Qatlib.Concepts.GradientOracle.GradientAlgo

/-- The proposition that a degree-`k` tensor polynomial with coefficients bounded by one reaches
the specified threshold on at most `|S|^d/r^(2*k)` points of a nonempty symmetric grid in
`[-1/2, 1/2]`. -/
def TensorChebyshevGridBound : Prop :=
  ∀ (d k : ℕ), 0 < d → 0 < k → ∀ r : ℝ, 1 < r →
    ∀ S : Finset ℝ, (∀ v ∈ S, |v| ≤ 1 / 2) → (∀ v ∈ S, -v ∈ S) → S.Nonempty →
    ∀ H : (Fin k → Fin d) → ℝ, (∀ α, |H α| ≤ 1) →
    ((Finset.univ.filter (fun y : Fin d → S =>
        Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k
          ≤ |∑ α : Fin k → Fin d, H α * ∏ i : Fin k, (y (α i) : ℝ)|)).card : ℝ)
      ≤ (((S.card : ℕ) ^ d : ℕ) : ℝ) / r ^ (2 * k)

end Qatlib.Concepts.GradientOracle.GradientAlgo
