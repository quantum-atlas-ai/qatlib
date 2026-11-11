/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# GraphNorm — the nonlinear term of a finite-graph discrete nonlinear Schrödinger equation

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: §5 (nonlinear Schrödinger application).

On a finite graph with real-symmetric coupling the discrete nonlinear
Schrödinger equation reads

  `i ψ̇_j = ∑_k L_{jk} ψ_k + g |ψ_j|² ψ_j`,

with `g : ℝ`.  The `L`-term is norm-neutral because `L` is self-adjoint; the
nonlinear term is norm-neutral because it is *purely imaginary* once multiplied
by `conj ψ_j`: writing `|ψ_j|² = conj ψ_j · ψ_j` as a real scalar, the per-site
contribution to `d/dt |ψ_j|²` is

  `2 Re( conj ψ_j · (-i) · |ψ_j|² ψ_j ) = 0`.

This module proves that scalar identity.  It is exactly the "conjugate /
real-coordinate" gap flagged in the paper: the nonlinearity cannot be written as
a polynomial in `ψ` alone, because the norm `|ψ|²` is expressed through `conj ψ`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonlinODE08.DnlsEncoding

/-- The per-site nonlinear contribution to the rate of change of `|ψ|²`:
`conj ψ · (-i g |ψ|² ψ)`. -/
def nonlinearNormRate (ψ : ℂ) (g : ℝ) : ℂ :=
  star ψ * (-Complex.I * (((g * Complex.normSq ψ : ℝ) : ℂ) * ψ))

/-- The nonlinear term does not change the total norm: its contribution to
`d/dt |ψ|²` is purely imaginary, hence has zero real part. -/
theorem nonlinear_norm_rate_re_zero (ψ : ℂ) (g : ℝ) :
    (nonlinearNormRate ψ g).re = 0 := by
  unfold nonlinearNormRate
  have hreal : star ψ * ψ = ((Complex.normSq ψ : ℝ) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj ψ
  have hcomm :
      star ψ * (-Complex.I * (((g * Complex.normSq ψ : ℝ) : ℂ) * ψ))
        = -Complex.I * (((g * Complex.normSq ψ * Complex.normSq ψ : ℝ) : ℂ)) := by
    rw [show star ψ * (-Complex.I * (((g * Complex.normSq ψ : ℝ) : ℂ) * ψ))
        = -Complex.I * (((g * Complex.normSq ψ : ℝ) : ℂ) * (star ψ * ψ)) by ring]
    rw [hreal]
    congr 1
    push_cast
    ring
  rw [hcomm]
  rw [Complex.mul_re]
  simp

/-- The `|ψ|²` factor is real and nonnegative, the real-component form the
encoding has to expose. -/
theorem normSq_real_nonneg (ψ : ℂ) :
    (Complex.normSq ψ : ℝ) = Complex.normSq ψ ∧ 0 ≤ Complex.normSq ψ :=
  ⟨rfl, Complex.normSq_nonneg ψ⟩

end Qatlib.Papers.NonlinODE08.DnlsEncoding
