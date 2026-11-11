/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared analytic model for Quantum Hamiltonian Descent

Fixed source: Jiaqi Leng, Ethan Hickman, Joseph Li, Xiaodi Wu,
*Quantum Hamiltonian Descent*, arXiv:2303.01471v1 (2 March 2023).

This module collects the few modelling objects that every claim file of
`QHamDescent23.MainResults` shares:

* `Ket` / `bracket`: complex amplitude vectors and the Dirac bracket used in
  (B.2), (B.3), (F.31);
* `qhdHamiltonian`: the two-parameter QHD Hamiltonian
  `H(t) = e^{φ t} K + e^{χ t} F` of (A.23) / (A.27), written for a fixed
  kinetic operator `K` and potential operator `F` on a complex vector space;
* `Schrodinger`: the Schrödinger equation `i d/dt |Ψ_t⟩ = H(t)|Ψ_t⟩` of
  (A.22), (B.1);
* `IdealScaling`: the ideal scaling condition (A.25).

The bounded-operator formulation is the natural exact statement for the
time-dilation and Ehrenfest lemmas; the unbounded Laplacian/potential pair is
kept abstract (`K`, `F` are continuous linear maps), which is the standard
finite-energy (`C_c^∞`-core) reading of the paper and does not weaken any of
the statements recorded in this block.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix

namespace Qatlib.Papers.QHamDescent23.MainResults

/-! ## Amplitude vectors and the Dirac bracket -/

/-- Complex amplitude vector indexed by a finite orthonormal basis. -/
abbrev Ket (ι : Type*) := ι → ℂ

/-- Dirac bracket `⟨x|y⟩ = Σ_i conj(x_i) y_i`, conjugate-linear in the first
slot, as in (B.2) and (F.30)–(F.31). -/
def bracket {ι : Type*} [Fintype ι] (x y : Ket ι) : ℂ :=
  ∑ i, star (x i) * y i

/-- The Dirac bracket vanishes when the left vector is zero. -/
@[simp] theorem bracket_zero_left {ι : Type*} [Fintype ι] (y : Ket ι) :
    bracket (0 : Ket ι) y = 0 := by
  simp [bracket]

/-- The Dirac bracket vanishes when the right vector is zero. -/
@[simp] theorem bracket_zero_right {ι : Type*} [Fintype ι] (x : Ket ι) :
    bracket x (0 : Ket ι) = 0 := by
  simp [bracket]

/-- Additivity of the Dirac bracket in its right argument. -/
theorem bracket_add_right {ι : Type*} [Fintype ι] (x y z : Ket ι) :
    bracket x (y + z) = bracket x y + bracket x z := by
  simp [bracket, mul_add, Finset.sum_add_distrib]

/-- The Dirac bracket is additive in its right argument under subtraction. -/
theorem bracket_sub_right {ι : Type*} [Fintype ι] (x y z : Ket ι) :
    bracket x (y - z) = bracket x y - bracket x z := by
  simp [bracket, mul_sub, Finset.sum_sub_distrib]

/-- Scalar pull-out in the right argument of the Dirac bracket. -/
theorem bracket_smul_right {ι : Type*} [Fintype ι] (c : ℂ) (x y : Ket ι) :
    bracket x (c • y) = c * bracket x y := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Scalar pull-out in the left argument of the Dirac bracket, with the scalar
conjugated. -/
theorem bracket_smul_left {ι : Type*} [Fintype ι] (c : ℂ) (x y : Ket ι) :
    bracket (c • x) y = star c * bracket x y := by
  simp only [bracket, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The Dirac bracket is the dot product of the conjugated left vector with
the right vector: `⟨x|y⟩ = (star x) ⬝ᵥ y`. -/
theorem bracket_eq_dotProduct {ι : Type*} [Fintype ι] (x y : Ket ι) :
    bracket x y = star x ⬝ᵥ y := rfl

/-- Left slot of the bracket against a matrix-vector product: moving `A` to
the right slot produces the conjugate transpose `Aᴴ`. -/
theorem bracket_mulVec_left {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : Ket ι) :
    bracket (A *ᵥ x) y = bracket x (Aᴴ *ᵥ y) := by
  rw [bracket_eq_dotProduct, bracket_eq_dotProduct, Matrix.star_mulVec]
  exact (Matrix.dotProduct_mulVec (star x) Aᴴ y).symm

/-- A Hermitian matrix is self-adjoint for the bracket. -/
theorem bracket_mulVec_left_of_isHermitian {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x y : Ket ι) :
    bracket (A *ᵥ x) y = bracket x (A *ᵥ y) := by
  rw [bracket_mulVec_left, hA.eq]

/-! ## QHD Hamiltonian and the Schrödinger equation -/

/-- Two-parameter QHD Hamiltonian `H(t) = e^{φ_t} K + e^{χ_t} F` of (A.23),
with `a = e^φ`, `b = e^χ` given directly. -/
def qhdHamiltonian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : ℝ → ℝ) (K F : E →L[ℂ] E) : ℝ → E →L[ℂ] E :=
  fun t => (a t : ℂ) • K + (b t : ℂ) • F

/-- Pointwise evaluation form of the two-parameter QHD Hamiltonian. -/
theorem qhdHamiltonian_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : ℝ → ℝ) (K F : E →L[ℂ] E) (t : ℝ) (x : E) :
    qhdHamiltonian a b K F t x = (a t : ℂ) • K x + (b t : ℂ) • F x := by
  simp [qhdHamiltonian]

/-- Schrödinger equation `i d/dt |Ψ_t⟩ = H(t)|Ψ_t⟩` (A.22), written in the
equivalent form `d/dt |Ψ_t⟩ = -i H(t)|Ψ_t⟩`. -/
def Schrodinger {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : ℝ → E →L[ℂ] E) (Ψ : ℝ → E) : Prop :=
  ∀ t, HasDerivAt Ψ ((-Complex.I) • H t (Ψ t)) t

/-- Ideal scaling condition (A.25): `β̇_t ≤ e^{α_t}` and `γ̇_t = e^{α_t}`,
with the derivative functions supplied explicitly. -/
def IdealScaling (α : ℝ → ℝ) (_β _γ : ℝ → ℝ) (β' γ' : ℝ → ℝ) : Prop :=
  ∀ t, β' t ≤ Real.exp (α t) ∧ γ' t = Real.exp (α t)


/-- Born-rule expectation `E[f]_{Ψ} = Σ_i |Ψ_i|² f_i` of the loss (B.3) in a
finite orthonormal basis. -/
def Expectation {ι : Type*} [Fintype ι] (f : ι → ℝ) (ψ : Ket ι) : ℝ :=
  ∑ i, Complex.normSq (ψ i) * f i

/-- Three-parameter QHD Hamiltonian (A.24):
`H(t) = e^{α_t − γ_t} K + e^{α_t + β_t + γ_t} F`, with the kinetic and
potential operators supplied as matrices. -/
def qhd3 {ι : Type*} [Fintype ι] (α β γ : ℝ → ℝ)
    (K F : Matrix ι ι ℂ) : ℝ → Matrix ι ι ℂ :=
  fun t => (Real.exp (α t - γ t) : ℂ) • K
    + (Real.exp (α t + β t + γ t) : ℂ) • F

/-- The quantum Lyapunov function of (B.6):
`W(t) = ⟨Ĵ²/2⟩_t + e^{β_t} ⟨f⟩_t` with `Ĵ = e^{−γ_t} p̂ + x̂`, written for
matrix position `X`, momentum `P` and multiplication-by-`f` operator `F`. -/
def lyapunovW {ι : Type*} [Fintype ι] (P X F : Matrix ι ι ℂ) (β γ : ℝ → ℝ)
    (Ψ : ℝ → Ket ι) (t : ℝ) : ℝ :=
  let J : Matrix ι ι ℂ := (Real.exp (-(γ t)) : ℂ) • P + X
  (bracket (Ψ t) ((J * J) *ᵥ Ψ t)).re / 2
    + Real.exp (β t) * (bracket (Ψ t) (F *ᵥ Ψ t)).re

end Qatlib.Papers.QHamDescent23.MainResults
