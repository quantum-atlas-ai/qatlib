/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: acceptance-probability polynomials

Fixed source: arXiv:1012.3174v3. This module transcribes the object studied in
Lemma 15 (p. 16): the polynomial `P_A` describing the acceptance probability of a
quantum algorithm as a function of the graph oracle.  Because the acceptance
probability of a quantum algorithm is a multilinear polynomial in the Boolean
input values (each variable `x_v` appears with exponent at most one), and because
it is a probability it takes values in `[0,1]` on the Boolean cube, the paper's
`P_A` is exactly a structure of this kind.

An `AcceptancePolynomial σ` bundles such a polynomial over a variable type `σ`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- The acceptance-probability polynomial `P_A` of a quantum algorithm (p. 16):
a multilinear polynomial over `σ` whose value on every Boolean point of the cube
lies in `[0,1]`. -/
structure AcceptancePolynomial (σ : Type*) [Fintype σ] [DecidableEq σ] where
  /-- The acceptance polynomial. -/
  poly : MvPolynomial σ ℝ
  /-- Multilinearity: every nonzero coefficient has exponent at most one in each
  variable. -/
  multilinear : ∀ e : σ →₀ ℕ, poly.coeff e ≠ 0 → ∀ i : σ, e i ≤ 1
  /-- On the Boolean cube the polynomial is nonnegative (a probability). -/
  nonneg : ∀ x : σ → ℝ, (∀ i, x i = 0 ∨ x i = 1) → 0 ≤ MvPolynomial.eval x poly
  /-- On the Boolean cube the polynomial is at most one (a probability). -/
  le_one : ∀ x : σ → ℝ, (∀ i, x i = 0 ∨ x i = 1) → MvPolynomial.eval x poly ≤ 1

end Qatlib.Papers.PropTestGraph10.MainResults.Model
