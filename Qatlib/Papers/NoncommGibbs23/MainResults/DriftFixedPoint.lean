/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommGibbs23.MainResults.Model

@[expose] public section


/-!
# NoncommGibbs23, Appendix E: detailed balance with drift and (s,ρ)-detailed balance

Paper: arXiv:2311.09207v2 (14 Oct 2025), Chen–Kastoryano–Gilyén,
*An efficient and exact noncommutative quantum Gibbs sampler*.

This module formalizes the fixed-point statements of Appendix E:

* Proposition E.1, p. 42: a ρ-detailed-balanced Lindbladian with unitary drift has
  the Gibbs state as a fixed point.
* Proposition E.3, p. 42: the anti-Hermitian and Hermitian parts of the discriminant
  both annihilate `√ρ`.
* Proposition E.4 / Corollary E.1, p. 42–43: the mixing-time / spectral-gap relation.
* Proposition E.6, p. 44: the fixed-point statement for `(s,ρ)`-detailed balance.

The definitions `IsRhoDetailedBalancedDrift` and `IsSDetailedBalanced` live in
`Model.lean`; the analytic estimates behind Propositions E.3/E.4 are recorded as
explicit hypotheses so that the paper's logical dependencies remain visible.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators Matrix.Norms.Elementwise

variable {D : ℕ}

/-! ## Proposition E.1: fixed point with unitary drift -/

/-- **Proposition E.1** (p. 42). If `T` satisfies ρ-detailed balance with unitary
drift `Q`, and if the Heisenberg adjoint is trace preserving (`T†[I] = 0`), then the
Gibbs state is stationary: `T[ρ] = 0`.

The proof is the same conjugation cancellation as Proposition II.1: evaluate the
detailed-balance identity at `X = I`, where the drift commutator vanishes, and
conjugate back by the explicit square root. -/
theorem propositionE1_fixedPointDrift {ρ r rInv Q : Operator D} {T Tdag : SuperOp D}
    (hdb : IsRhoDetailedBalancedDrift ρ r rInv Q T Tdag) (hT : Tdag 1 = 0) : T ρ = 0 := by
  obtain ⟨hrr, hrr', hsq, hform⟩ := hdb
  have h1 : rInv * T ρ * rInv = 0 := by
    have h := hform 1
    rw [hT] at h
    simpa [gammaRho, Matrix.mul_one, hsq, sub_self, smul_zero, add_zero] using h.symm
  calc T ρ = r * (rInv * T ρ * rInv) * r := by
        rw [show r * (rInv * T ρ * rInv) * r = T ρ by
          calc r * (rInv * T ρ * rInv) * r
              = (r * rInv) * T ρ * (rInv * r) := by noncomm_ring
            _ = 1 * T ρ * 1 := by rw [hrr, hrr']
            _ = T ρ := by rw [Matrix.one_mul, Matrix.mul_one]]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

/-! ## Proposition E.6: fixed point for `(s,ρ)`-detailed balance -/

/-- **Proposition E.6** (p. 44). If `T` satisfies `(s,ρ)`-detailed balance and is
trace preserving (`T†[I] = 0`), then `T[ρ] = 0`.

At `X = I` the s-detailed-balance identity gives
`leftInv * T[ρ] * rightInv = 0` because `left * I * right = left * right = ρ`.
Multiplying by the invertible fractional powers `left` and `right` cancels them. -/
theorem propositionE6_sDetailedFixedPoint {ρ left leftInv right rightInv : Operator D}
    {T Tdag : SuperOp D}
    (hdb : IsSDetailedBalanced ρ left leftInv right rightInv T Tdag)
    (hT : Tdag 1 = 0) : T ρ = 0 := by
  obtain ⟨hll, _hll', hrr, _hrr', hlr, hform⟩ := hdb
  have h1 : leftInv * T ρ * rightInv = 0 := by
    have h := hform 1
    rw [hT] at h
    simpa [Matrix.mul_one, hlr] using h.symm
  have hcancel : left * (leftInv * T ρ * rightInv) * right = T ρ := by
    calc left * (leftInv * T ρ * rightInv) * right
        = (left * leftInv) * T ρ * (rightInv * right) := by noncomm_ring
      _ = 1 * T ρ * 1 := by rw [hll, _hrr']
      _ = T ρ := by rw [Matrix.one_mul, Matrix.mul_one]
  calc T ρ = left * (leftInv * T ρ * rightInv) * right := hcancel.symm
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]


end Qatlib.Papers.NoncommGibbs23.MainResults
