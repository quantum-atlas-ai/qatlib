/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessOpti
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceCoeffLOneBoundOpti
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferencePowerSumBoundOpti
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOneDimErrorOpti
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceDirectionalErrorOpti

set_option backward.isDefEq.respectTransparency false

/-!
# GradientAlgo — degree-`2m` central difference: Definition 7, Lemma 22, Lemma 34, Corollary 35

Fixed source: arXiv:1711.00465v3, *Optimizing quantum optimization algorithms
via faster quantum gradient computation*.

* Definition 7 (§2, p.12): `a_ℓ^(2m) = (−1)^(|ℓ|−1)/ℓ · C(m,|ℓ|)/C(m+|ℓ|,|ℓ|)`,
  `a_0 = 0`, and `f_(2m)(x) = Σ_{ℓ=−m}^m a_ℓ^(2m) f(ℓ x)`; the exactness of the
  scheme on all monomials of degree `≤ 2m` is the algebraic input to Lemma 22.
* Lemma 22 Eq. (23) (§5.3, p.27): the one-dimensional remainder
  `e^{−m/2} ‖f^{(2m+1)}‖_∞ |δ|^{2m+1}`.
* Lemma 22 Eq. (24) (§5.3, p.27): the `ℓ¹` bound `Σ_{ℓ=0}^m |a_ℓ^(2m)| ≤ ln m + 1`.
* Lemma 34 Eq. (46) (App. A, p.48): `Σ_{ℓ=−m}^m |a_ℓ^(2m) ℓ^(k+1)| ≤
  6 e^{−7m/6} m^{k+3/2}` for `k ≥ 2m`.
* Corollary 35 (App. A, p.51): the directional remainder in `d` dimensions.

All five are bridges to the Frozen v2.0.2 concept theorems
`centralDifferenceExactness`, `centralDifferenceOneDimError`,
`centralDifferenceCoeffLOneBound`, `centralDifferencePowerSumBound`,
`centralDifferenceDirectionalError`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.GradientOracle.CentralDiff
open Qatlib.Concepts.GradientOracle.DifferenceError
open scoped BigOperators

namespace Qatlib.Papers.QGradient17.GradientAlgo.CentralDifference

/-- Definition 7 of arXiv:1711.00465v3 (§2, p.12): the degree-`2m` central
difference coefficient, with the explicit signed binomial quotient of the paper
(`a_0 = 0`). -/
theorem source_definition_seven_coeff (m : ℕ) (ℓ : ℤ) :
    centralDiffCoeff m ℓ =
      if ℓ = 0 then 0 else
        (-1 : ℝ) ^ (ℓ.natAbs - 1) / (ℓ : ℝ)
          * ((Nat.choose m ℓ.natAbs : ℕ) : ℝ)
          / ((Nat.choose (m + ℓ.natAbs) ℓ.natAbs : ℕ) : ℝ) := by
  unfold centralDiffCoeff
  split_ifs <;> rfl

/-- Definition 7 of arXiv:1711.00465v3 (§2, p.12): the degree-`2m` scheme is
exact on every monomial of degree `≤ 2m`, i.e. `Σ_ℓ a_ℓ^(2m) ℓ^j = δ_{j,1}`.
Reuses `centralDifferenceExactness`. -/
theorem source_definition_seven_exactness
    (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ 2 * m) :
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ j) = if j = 1 then 1 else 0 :=
  centralDifferenceExactness m hm j hj

/-- Lemma 22 Eq. (23) of arXiv:1711.00465v3 (§5.3, p.27): for a
`(2m+1)`-times differentiable `f : ℝ → ℝ` whose `(2m+1)`-st derivative is
bounded by `B` on `[−mδ, mδ]`, the central difference scheme at step `δ`
reproduces `f'(0)·δ` within `e^{−m/2} B |δ|^{2m+1}`.  Reuses
`centralDifferenceOneDimError`. -/
theorem source_lemma_twentytwo_error
    (m : ℕ) (hm : 0 < m) (δ B : ℝ) (hδ : 0 ≤ δ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (2 * m + 1) f)
    (hB : ∀ ξ ∈ Set.Icc (-(m : ℝ) * δ) ((m : ℝ) * δ),
      |iteratedDeriv (2 * m + 1) f ξ| ≤ B) :
    |(deriv f 0) * δ -
        ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
          centralDiffCoeff m ℓ * f ((ℓ : ℝ) * δ)|
      ≤ Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) * B * |δ| ^ (2 * m + 1) :=
  centralDifferenceOneDimError m hm δ B hδ f hf hB

/-- Lemma 22 Eq. (24) of arXiv:1711.00465v3 (§5.3, p.27): the `ℓ¹` mass of the
one-sided central difference coefficients obeys `Σ_{ℓ=0}^m |a_ℓ^(2m)| ≤ ln m + 1`.
Reuses `centralDifferenceCoeffLOneBound`. -/
theorem source_lemma_twentytwo_lone (m : ℕ) (hm : 0 < m) :
    ∑ ℓ ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + 1), |centralDiffCoeff m ℓ|
      ≤ Real.log m + 1 :=
  centralDifferenceCoeffLOneBound m hm

/-- Lemma 34 Eq. (46) of arXiv:1711.00465v3 (App. A, p.48): for `m ≥ 1` and
`k ≥ 2m`, the coefficient-weighted power sums decay exponentially in `m`,
`Σ_{ℓ=−m}^m |a_ℓ^(2m) ℓ^(k+1)| ≤ 6 e^{−7m/6} m^{k+3/2}`.  Reuses
`centralDifferencePowerSumBound`. -/
theorem source_lemma_thirtyfour
    (m k : ℕ) (hm : 0 < m) (hk : 2 * m ≤ k) :
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      |centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ (k + 1))|
      ≤ 6 * Real.exp (-(7 / 6 : ℝ) * (m : ℝ)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) :=
  centralDifferencePowerSumBound m k hm hk

/-- Lemma 34 Eq. (46) of arXiv:1711.00465v3 (App. A, p.48), stated in the
paper's own variables `m ∈ ℕ⁺`, `k ≥ 2m` and with the absolute value pulled
inside the coefficient-weighted monomial; this is the identical statement of
`source_lemma_thirtyfour`. -/
theorem source_lemma_thirtyfour_eq46
    (m k : ℕ) (hm : 0 < m) (hk : 2 * m ≤ k) :
    ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      |centralDiffCoeff m ℓ * ((ℓ : ℝ) ^ (k + 1))|
      ≤ 6 * Real.exp (-(7 / 6 : ℝ) * (m : ℝ)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) :=
  centralDifferencePowerSumBound m k hm hk

/-- Corollary 35 of arXiv:1711.00465v3 (App. A, p.51): with `r = x/‖x‖`, if the
`(2m+1)`-st directional derivative of `f` along `r` is bounded by `B` on the
segment `{τx : τ ∈ [−m,m]}`, then
`|f_(2m)(x) − ∇f(0)·x| ≤ B e^{−m/2} ‖x‖^{2m+1}`.  Reuses
`centralDifferenceDirectionalError`. -/
theorem source_corollary_thirtyfive
    (d m : ℕ) (hm : 0 < m) (B : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ (2 * m + 1) f)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0)
    (hB : ∀ τ ∈ Set.Icc (-(m : ℝ)) (m : ℝ),
      |iteratedFDeriv ℝ (2 * m + 1) f (τ • x)
        (fun _ : Fin (2 * m + 1) => (‖x‖⁻¹ : ℝ) • x)| ≤ B) :
    |centralDiffApply m f x - (fderiv ℝ f 0) x|
      ≤ B * Real.exp (-(1 / 2 : ℝ) * (m : ℝ)) * ‖x‖ ^ (2 * m + 1) :=
  centralDifferenceDirectionalError d m hm B f hf x hx hB

end Qatlib.Papers.QGradient17.GradientAlgo.CentralDifference
