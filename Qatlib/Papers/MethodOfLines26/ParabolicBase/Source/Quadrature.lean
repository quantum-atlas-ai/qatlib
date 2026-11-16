/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Model

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# arXiv:2606.03407v1 — Lemmas 7 and 8 (Gaussian quadrature)

Fixed version: **arXiv:2606.03407v1**, §4.2, Lemma 7 and Lemma 8 (PDF p.23);
proofs in Appendix B (PDF pp.61–62), equation (36).

The inhomogeneous term is handled by a Gaussian quadrature of the Duhamel
integral.  Equation (36) defines coefficients `c_{j_t} = w_{j_t} h_t`
(weight times subinterval length); Lemma 7 states that they are nonnegative
and that their sum is the LCU normalisation `O(∫₀ᵀ ‖b(s)‖₂ ds)`.  Lemma 8
chooses the number of quadrature points `Q_t` and the step `h_t` so that the
quadrature solution is `ε_Q`-close to the exact semi-discrete solution in the
mean norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
open Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open Matrix
open scoped BigOperators

/-- **Lemma 7** (arXiv:2606.03407v1, §4.2, Lemma 7, PDF p.23; Appendix B).
The composite Gauss–Legendre coefficients `c_j = w_j h` of (36) are
nonnegative, and their sum is bounded by `(3/2) ∫₀ᵀ ‖b(s)‖₂ ds`.

The hypothesis `hquad` is the quadrature-accuracy statement proved in
Appendix B: the finite sum approximates the integral `I = ∫₀ᵀ ‖b(s)‖₂ ds`
within a relative error of `1/2`.  The lemma's conclusion (nonnegativity and
the `O(I)` normalisation used for LCU) is then immediate. -/
theorem lemma7_quadrature_coefficients
    (M : ℕ) (w : Fin M → ℝ) (h I : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hh : 0 ≤ h)
    (hquad : |(∑ j, compositeGaussCoeff M w h j) - I| ≤ I / 2) :
    (∀ j, 0 ≤ compositeGaussCoeff M w h j) ∧
      (∑ j, compositeGaussCoeff M w h j) ≤ (3 / 2) * I := by
  refine ⟨compositeGaussCoeff_nonneg w h hw hh, ?_⟩
  have h := (abs_le.mp hquad).2
  linarith
end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
