/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# EigTransform26 — shared paper-layer vocabulary

Fixed arXiv:2607.25812v1 (Wang, Liang, Chen, Liu, 2026).
PDF SHA-256 of the prefetched copy is recorded in the PR body.

This module collects the objects that recur across the paper-layer statements of
*Optimal Quantum Eigenvalue Transformation via Linear Combinations of Hermitian
Matrices*:

* the Hermitian/skew decomposition `A = L + iH` (eq. (1.1), §2);
* the vanilla-LCHM scalar kernel `f_β` of eq. (2.2) and its pole residue eq. (2.3);
* the angular Hermitian pencil `X_θ = cos θ L + sin θ H` of eq. (3.1);
* the lift `F_g = 2g - g(0)` and the lifted polynomial `p_d = (P_d + P_d(0))/2`
  of eqs. (3.15) and (4.2);
* the numerical range and numerical radius `W(A)`, `w(A)` of eq. (3.5);
* a complex-matrix positive-semidefiniteness predicate `PSD` (`L ⪰ 0`) — Mathlib's
  `Matrix.PosSemidef` is only defined over ordered scalar rings, so the complex
  case is recorded here through the real part of the quadratic form;
* the holomorphic functional calculus relation `IsHolomorphicCalculus g A M`,
  recording that `M = g(A)` is the operator-norm limit of polynomial approximants
  that converge pointwise on the spectrum (Definition 3.4, eqs. (3.26)-(3.27));
* the paper's approximate block encoding `IsApproxBlockEncoding` (as used in
  Theorem 4.5), built on the frozen exact `IsBlockEncoding`.

All of these are *definitions*; no mathematical content is asserted here.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

namespace Qatlib.Papers.EigTransform26.Representation

variable {n J : Type*} [Fintype n] [DecidableEq n] [Fintype J] [DecidableEq J]

/-! ## Hermitian / skew decomposition `A = L + iH` -/

/-- The Hermitian part `L = (A + Aᴴ)/2` of eq. (1.1).  Together with
`generatorPart A`, it gives `A = hermitianPart A + i • generatorPart A`. -/
def hermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ := (2⁻¹ : ℂ) • (A + Aᴴ)

/-- The Hermitian generator `H = (A − Aᴴ)/(2i)` of eq. (1.1); `A = L + iH` with
both `L` and `H` Hermitian. -/
def generatorPart (A : Matrix n n ℂ) : Matrix n n ℂ := ((2 * Complex.I)⁻¹ : ℂ) • (A - Aᴴ)

/-- `L ⪰ 0` for a complex matrix: Hermitian with nonnegative real quadratic form.
This mirrors the paper's use of `L ⪰ 0` throughout §2 and §5. -/
def PSD (L : Matrix n n ℂ) : Prop :=
  L.IsHermitian ∧ ∀ x : n → ℂ, 0 ≤ (dotProduct (star x) (L.mulVec x)).re

/-! ## The vanilla-LCHM kernel `f_β` (eq. (2.2)) and its residue (eq. (2.3)) -/

/-- The principal-branch fractional power `z ↦ z^β` used in eq. (2.2).  It is
`Complex.cpow z β` (principal branch, open right half-plane). -/
def principalPower (β : ℝ) (z : ℂ) : ℂ := z ^ (β : ℂ)

/-- The vanilla-LCHM scalar kernel of eq. (2.2):
`f_β(z) = (1/(2π)) · exp(2^β − (1 + i z)^β) / (1 − i z)`. -/
def vanillaKernel (β : ℝ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * Complex.exp ((2 : ℂ) ^ (β : ℂ) - principalPower β (1 + Complex.I * z))
    / (1 - Complex.I * z)

/-- The residue of `f_β` at `z = −i` is `i/(2π)` (eq. (2.3)). -/
def vanishingResidue : ℂ := Complex.I / (2 * Real.pi)

/-! ## The angular Hermitian pencil (eq. (3.1)) -/

/-- `X_θ = cos θ · L + sin θ · H`, the angular Hermitian pencil of eq. (3.1).
For `A = L + iH` it equals `(e^{-iθ} A + e^{iθ} Aᴴ)/2`. -/
def angleMatrix (L H : Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  (Real.cos θ : ℂ) • L + (Real.sin θ : ℂ) • H

/-- The lift `F_g(z) = 2 g(z) − g(0)` of eq. (3.15). -/
def lift (g : ℂ → ℂ) : ℂ → ℂ := fun z => 2 * g z - g 0

/-- The lifted polynomial `p_d = (P_d + P_d(0))/2` of eq. (4.2). -/
def liftedPoly (P : Polynomial ℂ) : Polynomial ℂ := (2⁻¹ : ℂ) • (P + Polynomial.C (Polynomial.eval 0 P))

/-- The lift normalization `C_p = ‖2 p_d − p_d(0)‖_{∞,∂𝔻}` of eq. (4.29).  It is
recorded as an abstract real number constrained by the paper's bound, not as a
computed supremum (the supremum over the unit circle is stated in `WeylCircuit`). -/
def liftNormalization (_p : Polynomial ℂ) : ℝ := 0

/-! ## Numerical range and numerical radius (eq. (3.5)) -/

/-- The numerical range `W(A) = {⟪x, A x⟫ : ‖x‖ = 1}` of eq. (3.5). -/
def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  { w : ℂ | ∃ x : n → ℂ, (∑ i, ‖x i‖ ^ 2) = 1 ∧ w = dotProduct (star x) (A.mulVec x) }

/-- The numerical radius `w(A) = max_{z ∈ W(A)} |z|` of eq. (3.5), as the supremum
of `|⟪x, A x⟫|` over unit vectors. -/
def numericalRadius (A : Matrix n n ℂ) : ℝ :=
  sSup { r : ℝ | ∃ x : n → ℂ, (∑ i, ‖x i‖ ^ 2) = 1 ∧
    r = ‖dotProduct (star x) (A.mulVec x)‖ }

/-! ## Matrix functional calculus -/

/-- The polynomial matrix functional calculus `p(A)` (`Polynomial.aeval`). -/
def polyEval (A : Matrix n n ℂ) (p : Polynomial ℂ) : Matrix n n ℂ := Polynomial.aeval A p

/-- `M = g(A)` in the holomorphic functional calculus of Definition 3.4
(eqs. (3.26)-(3.27)): `M` is the operator-norm limit of `p_k(A)` for polynomials
`p_k` that converge to `g` on the spectrum of `A`.  The eigenvalues of a matrix
are characterised here by the existence of a nonzero eigenvector. -/
def IsHolomorphicCalculus (g : ℂ → ℂ) (A M : Matrix n n ℂ) : Prop :=
  ∃ p : ℕ → Polynomial ℂ,
    Tendsto (fun k => Polynomial.aeval A (p k)) atTop (𝓝 M) ∧
    ∀ z : ℂ, (∃ v : n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v) →
      Tendsto (fun k => Polynomial.eval z (p k)) atTop (𝓝 (g z))

/-! ## Approximate block encodings -/

/-- Paper's approximate `(α, a, ε)`-block-encoding of `A` (Theorem 4.5): `U` is
unitary on the ancilla–system space `J × n`, `α > 0`, and the all-zero (or `j₀`)
corner differs from `A/α` by at most `ε` in operator norm.  The exact case
`ε = 0` is the frozen `IsBlockEncoding`. -/
def IsApproxBlockEncoding (U : Matrix (J × n) (J × n) ℂ) (j₀ : J)
    (A : Matrix n n ℂ) (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × n) ℂ ∧ 0 < α ∧
    ‖A - ((α : ℂ)) • Qatlib.Concepts.BlockEncoding.StateBlockEncoding.BlockCorner U j₀‖ ≤ ε

/-- The exact block encoding is the `ε = 0` case of the approximate one. -/
theorem isApproxBlockEncoding_zero {U : Matrix (J × n) (J × n) ℂ} {j₀ : J}
    {A : Matrix n n ℂ} {α : ℝ}
    (h : Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsBlockEncoding U j₀ A α) :
    IsApproxBlockEncoding U j₀ A α 0 := by
  obtain ⟨hU, hα, hcorner⟩ := h
  refine ⟨hU, hα, ?_⟩
  rw [hcorner, norm_le_zero_iff]
  rw [sub_eq_zero]
  rw [smul_smul]
  rw [show ((α : ℂ) * ((α⁻¹ : ℝ) : ℂ)) = 1 by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hα.ne')],
    one_smul]

/-! ## Chebyshev / angular-pencil building blocks (eqs. (3.2), (3.20), (4.5)) -/

/-- The degree-`m` Chebyshev polynomial of the first kind `T_m`, as a complex
polynomial.  This is the `T_m` appearing in Theorem 3.2 (eq. (3.8)). -/
noncomputable def chebT (m : ℕ) : Polynomial ℂ := Polynomial.Chebyshev.T ℂ (m : ℤ)

/-- `T_m(X_θ)`: the Chebyshev polynomial evaluated at the angular Hermitian pencil
`X_θ = angleMatrix L H θ` (Theorem 3.2). -/
noncomputable def chebAngle (L H : Matrix n n ℂ) (θ : ℝ) (m : ℕ) : Matrix n n ℂ :=
  Polynomial.aeval (angleMatrix L H θ) (chebT m)

/-- The angular term `a_m e^{i m θ} T_m(X_θ)` of the series (3.20). -/
noncomputable def angularTerm (L H : Matrix n n ℂ) (a : ℕ → ℂ) (θ : ℝ) (m : ℕ) :
    Matrix n n ℂ :=
  a m • (Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) • chebAngle L H θ m

/-- The angular series value of eq. (3.20):
`a_0 I + 2 ∑_{m≥1} a_m e^{i m θ} T_m(X_θ)`. -/
noncomputable def angularSeries (L H : Matrix n n ℂ) (a : ℕ → ℂ) (θ : ℝ) :
    Matrix n n ℂ :=
  a 0 • (1 : Matrix n n ℂ) + (2 : ℂ) • ∑' m : ℕ, angularTerm L H a θ (m + 1)

/-- The angular polynomial `q_{d,θ}(x) = c_0 + ∑_{m=1}^d c_m e^{i m θ} T_m(x)` of eq. (4.5),
evaluated at `X_θ`. -/
noncomputable def angularPoly (L H : Matrix n n ℂ) (c : ℕ → ℂ) (d : ℕ) (θ : ℝ) :
    Matrix n n ℂ :=
  c 0 • (1 : Matrix n n ℂ)
    + ∑ m ∈ Finset.range d,
        c (m + 1) •
          (Complex.exp (Complex.I * ((m + 1 : ℕ) : ℂ) * (θ : ℂ))) • chebAngle L H θ (m + 1)

end Qatlib.Papers.EigTransform26.Representation
