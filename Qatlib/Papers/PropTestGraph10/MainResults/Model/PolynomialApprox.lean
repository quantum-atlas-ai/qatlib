/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: bivariate polynomials and `δ`-good pairs

Fixed source: arXiv:1012.3174v3. This module transcribes the two auxiliary notions
used by Lemma 3 (p. 5) and Lemma 4 (p. 5):

* `PolyDeg f D` says that `f : ℕ → ℕ → ℝ` is given by a bivariate polynomial in
  `(M,l)` of total degree at most `D`.  The paper's "polynomials of degree
  `O(T log T)`" is expressed by extracting a `D` together with a bound
  `D ≤ C·T·log T`.
* `DenomProductForm g T` says that `g` is a product of the factors
  `M - (2k-1)l`, `k = 1,…,T`, with the factor `M - (2k-1)l` occurring at most
  `2T/k` times — exactly the denominator shape asserted in Lemma 3 (p. 5).  The
  exponent is stored as `e (k-1)` for `k = 1,…,T`.
* `IsDeltaGood a N δ M l` is the paper's `δ`-good condition (p. 5):
  `M ∈ [aN - δ^{3/2}, aN + δ^{3/2}]`, `l ≤ δ`, and `l ∣ M`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- `f : ℕ → ℕ → ℝ` is given by a bivariate polynomial in `(M,l)` of total
degree at most `D`. This is the paper's notion of a polynomial "in `M` and `l`"
(Lemma 3, p. 5), together with its total degree. -/
def PolyDeg (f : ℕ → ℕ → ℝ) (D : ℕ) : Prop :=
  ∃ coeff : ℕ → ℕ → ℝ,
    (∀ i j : ℕ, D < i + j → coeff i j = 0) ∧
    ∀ M l : ℕ,
      f M l = ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        coeff i j * (M : ℝ) ^ i * (l : ℝ) ^ j

/-- `g : ℕ → ℕ → ℝ` has the denominator shape produced by Lemma 3 (p. 5): it is
the product of the factors `M - (2k-1)l` for `k = 1,…,T`, where the factor
`M - (2k-1)l` occurs `e (k-1)` times and `e (k-1) ≤ 2T/k`. -/
def DenomProductForm (g : ℕ → ℕ → ℝ) (T : ℕ) : Prop :=
  ∃ e : ℕ → ℕ,
    (∀ r : ℕ, T ≤ r → e r = 0) ∧
    (∀ r : ℕ, r < T → e r ≤ 2 * T / (r + 1)) ∧
    ∀ M l : ℕ,
      g M l = ∏ r ∈ Finset.range T,
        ((M : ℝ) - (2 * ((r : ℝ) + 1) - 1) * (l : ℝ)) ^ e r

/-- The paper's `δ`-good pairs `(M,l)` (p. 5): `M ∈ [aN - δ^{3/2}, aN + δ^{3/2}]`,
`l ≤ δ`, and `l` divides `M`. -/
def IsDeltaGood (a N : ℕ) (δ : ℝ) (M l : ℕ) : Prop :=
  |(M : ℝ) - (a : ℝ) * (N : ℝ)| ≤ δ ^ (3 / 2 : ℝ) ∧ (l : ℝ) ≤ δ ∧ l ∣ M

end Qatlib.Papers.PropTestGraph10.MainResults.Model
