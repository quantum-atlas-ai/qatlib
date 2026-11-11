/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 (Möbius transformation linearises the matrix Riccati equation)

Source: arXiv:2404.07303, §2.6, Proposition 1, equations (2.60)–(2.68), page 12.

The source considers the linear initial value problem
`ẋ = A x + b` with `x = (u, v)ᵀ`,
`A = [[F₁, F₀], [F₂, F₃]]`, `b = (e, f)ᵀ`, and `e = F₁ w`, `f = F₂ w`
for a time-independent `w`, with `u(0) = y₀`, `v(0) = I`.  It claims that
`y = (u + w) v⁻¹` satisfies the matrix Riccati equation.

**Sign note (source discrepancy, reported not silently fixed).**  The printed
Riccati equation (2.60)/(3.15)/(2.68) is `ẏ = F₀ + F₁ y + y F₂ y + y F₃`, but the
source's own Grassmannian derivation (2.59) and its displayed line (2.67)–(2.68)
carry a minus sign,
`ẏ = F₀ + F₁ y − y F₂ y − y F₃`.  Concretely, expanding (2.67)
`(F₁u + F₀v + e)v⁻¹ + (u + w)v⁻¹(F₂u + F₃v + f)v⁻¹`
with `e = F₁w`, `f = F₂w` gives `F₀ + F₁y − yF₂y − yF₃`; the `−` in (2.67) becomes `+`
in (2.68) on *both* the `yF₂y` and the `yF₃` term.  We formalise the identity exactly
as the proof establishes it (`riccatiRHSMinus`), and we record the exact relation
between the printed and derived right-hand sides (`proposition1_printed_vs_derived`)
rather than asserting the printed equation, which is false in general.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

/-- **Proposition 1 (§2.6, (2.60)–(2.68)).**  If `u, v` satisfy the linear system
`u̇ = F₁ u + F₀ v + F₁ w`, `v̇ = F₂ u + F₃ v + F₂ w` (i.e. (2.65)–(2.66) with
`e = F₁ w`, `f = F₂ w`), then `y = (u + w) v⁻¹` has derivative
`u̇ v⁻¹ − (u + w) v⁻¹ v̇ v⁻¹ = F₀ + F₁ y − y F₂ y − y F₃`, i.e. it solves the
Riccati equation in the sign convention of (2.59) and of the source proof (2.67). -/
theorem proposition1_mobius
    (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ)
    (u : Matrix N M ℂ) (v : Matrix M M ℂ) (w : Matrix N M ℂ)
    (du : Matrix N M ℂ) (dv : Matrix M M ℂ)
    (hv : IsUnit v.det)
    (hu : du = F₁ * u + F₀ * v + F₁ * w)
    (hdv : dv = F₂ * u + F₃ * v + F₂ * w) :
    du * v⁻¹ - (u + w) * v⁻¹ * dv * v⁻¹ =
      riccatiRHSMinus F₁ F₀ F₂ F₃ ((u + w) * v⁻¹) := by
  subst hu
  subst hdv
  have hv1 : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v hv
  unfold riccatiRHSMinus
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hv1, Matrix.mul_one]
  abel

/-- **Proposition 1, relation between printed (2.68) and derived (2.67) right-hand
sides.**  The printed right-hand side exceeds the actual derivative by
`2 (y F₂ y + y F₃)`, where `y = (u + w) v⁻¹`.  Consequently the printed equation
holds exactly when `y F₂ y + y F₃ = 0`; in particular it holds with the printed signs
when `F₂ = 0` **and** `F₃ = 0`. -/
theorem proposition1_printed_vs_derived
    (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ)
    (y : Matrix N M ℂ) :
    riccatiRHS F₁ F₀ F₂ F₃ y =
      riccatiRHSMinus F₁ F₀ F₂ F₃ y + (y * F₂ * y + y * F₃) + (y * F₂ * y + y * F₃) := by
  unfold riccatiRHS riccatiRHSMinus
  abel

/-- **Proposition 1, printed form in the degenerate case `F₂ = F₃ = 0`.**  Then
`F₀ + F₁ y + y F₂ y + y F₃ = F₀ + F₁ y − y F₂ y − y F₃`, so the printed equation
(2.60)/(2.68) coincides with the derived one. -/
theorem proposition1_printed_collapse
    (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (y : Matrix N M ℂ) :
    riccatiRHS F₁ F₀ 0 0 y = riccatiRHSMinus F₁ F₀ 0 0 y := by
  unfold riccatiRHS riccatiRHSMinus
  simp [Matrix.mul_zero, Matrix.zero_mul]

/-- **Proposition 1, initial condition.**  `y(0) = u(0) v(0)⁻¹ = y₀ + w` when
`u(0) = y₀` and `v(0) = I`, matching `y = (u + w) v⁻¹` at the start of the proof. -/
theorem proposition1_initial (u₀ : Matrix N M ℂ) (v₀ : Matrix M M ℂ) (w : Matrix N M ℂ)
    (hv₀ : v₀ = 1) :
    (u₀ + w) * v₀⁻¹ = u₀ + w := by
  subst hv₀
  simp

end Qatlib.Papers.QuadHamilton24.MainResults
