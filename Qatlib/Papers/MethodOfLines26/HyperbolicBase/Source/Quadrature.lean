/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source.Model
public import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Quadrature

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# arXiv:2606.03407v1 — Lemmas 16 and 17 (hyperbolic quadrature)

Fixed version: **arXiv:2606.03407v1**, §5.4, Lemma 16 and Lemma 17
(PDF p.40), equation (69).  The proofs are the same as Lemma 7 and Lemma 8.

* **Lemma 16**: the quadrature coefficients `c_{j_t} = w_{j_t} h_t` are
  nonnegative and their sum is `O(∫₀ᵀ ‖B(s)‖₂ ds)`.
* **Lemma 17**: with `Q_t ≥ ln(4 T cond(P) Ξ / ε_Q)/ln 4` and
  `h_t ≤ 4Q_t/(e(‖H‖₂ + Ξ))`, the quadrature solution satisfies
  `‖v(T) − v_Q(T)‖⋆ ≤ ε_Q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
open Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source

open Matrix
open scoped BigOperators
open Qatlib.Papers.MethodOfLines26.ParabolicBase.Source Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

/-- **Lemma 16** (arXiv:2606.03407v1, §5.4, Lemma 16, PDF p.40).  The
composite Gauss–Legendre coefficients of (69) are nonnegative and their sum
is at most `(3/2) ∫₀ᵀ ‖B(s)‖₂ ds`.

As for Lemma 7, `hquad` is the quadrature-accuracy statement of the proof
(Appendix B, reused verbatim), relating the finite sum to the integral `I`. -/
theorem lemma16_quadrature_coefficients
    (M : ℕ) (w : Fin M → ℝ) (h I : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hh : 0 ≤ h)
    (hquad : |(∑ j, compositeGaussCoeff M w h j) - I| ≤ I / 2) :
    (∀ j, 0 ≤ compositeGaussCoeff M w h j) ∧
      (∑ j, compositeGaussCoeff M w h j) ≤ (3 / 2) * I :=
  lemma7_quadrature_coefficients M w h I hw hh hquad
end Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
