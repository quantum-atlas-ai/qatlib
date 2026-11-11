/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# GenEigenODE20 source model

Shao--Liu, *Solving generalized eigenvalue problems by ordinary differential
equations on a quantum computer*, fixed arXiv:2010.15027v2 (2021-10-19).

This module records the objects that the paper's Theorem 20, Propositions
16--19, Corollaries 21--27 and Theorem 28 refer to:

* the generalized eigenvalue instance `A x = λ B x`, its generalized
  eigenvector matrix `E` and real diagonal `Λ` (Problem 1, text p. 2 and
  Proposition 2, p. 6);
* the paper's approximate `(α,q,δ)`-block-encoding convention (Definition 4,
  Eq. (11), p. 7) in terms of the frozen `IsBlockEncoding` corner;
* the Fourier discretisation matrices `F`, `D`, `M` of Eqs. (21)--(27)
  (pp. 10--11);
* the paper's cost expressions of Eqs. (43), (47)--(50), (54), (55).

The definitions are deliberately explicit finite matrices: no numerical
linear-algebra solver, no asymptotic `O`-calculus and no quantum-algorithm
semantics is hidden in them.  Circuit-level realisations are stated by the
claim theorems and are not asserted by this model file.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

open Matrix
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A generalized eigenvalue instance in the sense of Problem 1 (p. 2):
`A x = λ B x`, with `B` invertible, a generalized eigenvector matrix `E`
whose columns are the `|E_j⟩`, and real eigenvalues `λ_j`.  The relation
`A * E = B * E * diagonal λ` is exactly `AE = BEΛ` (Proposition 2, p. 6). -/
structure GEPInstance (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The left-hand matrix `A`. -/
  A : Matrix n n ℂ
  /-- The right-hand matrix `B`. -/
  B : Matrix n n ℂ
  /-- A two-sided inverse of `B`, i.e. the paper's `B⁻¹`. -/
  Binv : Matrix n n ℂ
  /-- The matrix of generalized eigenvectors `E`. -/
  E : Matrix n n ℂ
  /-- The real generalized eigenvalues `λ_j`. -/
  lam : n → ℝ
  /-- `B` is invertible. -/
  B_unit : IsUnit B
  /-- `E` is invertible (the eigenvectors form a basis). -/
  E_unit : IsUnit E
  /-- `B⁻¹ B = 1`. -/
  Binv_mul_B : Binv * B = 1
  /-- `A E = B E Λ`: the generalized eigenpair relation of Proposition 2. -/
  eigen_relation : A * E = B * E * diagonal (fun j => (lam j : ℂ))

/-- The paper's condition number `κ_E` of the generalized eigenvector matrix
(p. 16, Theorem 20). -/
noncomputable def GEPInstance.condE (inst : GEPInstance n) : ℝ :=
  ‖inst.E‖ * ‖inst.E⁻¹‖

/-- `B⁻¹ A`, the matrix whose spectrum is the generalized spectrum. -/
noncomputable def GEPInstance.BinvA (inst : GEPInstance n) : Matrix n n ℂ := inst.Binv * inst.A

/-- The diagonal matrix `Λ` of the real eigenvalues. -/
def GEPInstance.Lambda (inst : GEPInstance n) : Matrix n n ℂ :=
  diagonal (fun j => (inst.lam j : ℂ))

/-- The Fourier entry `F_{kl} = p^{-1/2} exp(2πi kl / p)` of Eq. (23). -/
noncomputable def fourierEntry (p : ℕ) (k l : Fin p) : ℂ :=
  ((Real.sqrt (p : ℝ))⁻¹ : ℂ) *
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((k : ℂ) * (l : ℂ)) / (p : ℂ))

/-- The linear system matrix `I ⊗ A - τ⁻¹ D ⊗ B` of Eq. (27), written entrywise
on the block index `Fin p` (the paper's `p` frequency samples).  `τ⁻¹D` has
diagonal entries `τ⁻¹ (k - (p-1)/2)` (Eqs. (22)--(23), p. 11). -/
noncomputable def blockN (A B : Matrix n n ℂ) (p : ℕ) [NeZero p] (τ : ℝ) :
    Matrix (Fin p × n) (Fin p × n) ℂ :=
  Matrix.of fun r c =>
    if r.1 = c.1 then
      A r.2 c.2 - ((τ⁻¹ : ℝ) : ℂ) * ((r.1 : ℂ) - (((p : ℝ) - 1) / 2 : ℂ)) * B r.2 c.2
    else 0

/-- The coefficient matrix `M` of the discretised ODE, Eq. (27), p. 11.  The
first block row is `⟨0| Fᵀ ⊗ I`; the remaining rows are
`(F₀ᵀ ⊗ I)(I ⊗ A - τ⁻¹ D ⊗ B)`. -/
noncomputable def blockM (A B : Matrix n n ℂ) (p : ℕ) [NeZero p] (τ : ℝ) :
    Matrix (Fin p × n) (Fin p × n) ℂ :=
  Matrix.of fun r c =>
    if r.1 = 0 then
      if c.1 = 0 then
        (if r.2 = c.2 then ((Real.sqrt (p : ℝ))⁻¹ : ℂ) else 0)
      else 0
    else
      if c.1 = 0 then 0
      else
        fourierEntry p c.1 r.1 *
          (A r.2 c.2 - ((τ⁻¹ : ℝ) : ℂ) *
            ((c.1 : ℂ) - (((p : ℝ) - 1) / 2 : ℂ)) * B r.2 c.2)

/-- The paper's `(α,q,δ)`-block-encoding convention (Definition 4, Eq. (11),
p. 7): the all-zero ancilla corner of a unitary `U` approximates `A/α` to
spectral error `δ`.  The frozen `BlockCorner` supplies the corner. -/
structure Encoded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (q : ℕ) (α δ : ℝ) where
  /-- The encoding unitary on `q` clean ancillas plus the system. -/
  U : Matrix (Fin (2 ^ q) × ι) (Fin (2 ^ q) × ι) ℂ
  /-- The encoding is unitary. -/
  unitary : U ∈ Matrix.unitaryGroup (Fin (2 ^ q) × ι) ℂ
  /-- The scale is positive. -/
  alpha_pos : 0 < α
  /-- The reported error is nonnegative. -/
  delta_nonneg : 0 ≤ δ
  /-- `‖A - α · corner(U,0)‖ ≤ δ`, Eq. (11) with the paper's ancilla corner. -/
  error_le : ‖A - ((α : ℝ) : ℂ) •
      BlockCorner U ⟨0, Nat.two_pow_pos q⟩‖ ≤ δ

/-- An encoding whose synthesis is charged a real time cost `T`. -/
structure CostedEncoded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (q : ℕ) (α δ T : ℝ) extends Encoded A q α δ where
  /-- The synthesis time. -/
  cost : ℝ
  /-- Synthesis cost is nonnegative. -/
  cost_nonneg : 0 ≤ cost
  /-- The synthesis time is at most the stated budget. -/
  cost_le : cost ≤ T

/-- Theorem 20's displayed complexity, Eq. (43), p. 17. -/
noncomputable def thm20Complexity (κE ε αA αB ρ Tin TA TB BinvNorm : ℝ) : ℝ :=
  κE / ε * ((αA + ρ * αB) * (Tin + TA + TB)) * BinvNorm

/-- Corollary 21's displayed complexity, Eq. (47), p. 18. -/
noncomputable def sparseGEPComplexity (κE ε sA sB Amax Bmax ρ Tin BinvNorm : ℝ) : ℝ :=
  κE / ε * ((sA * Amax + ρ * sB * Bmax) * Tin) * BinvNorm

/-- Corollary 22's displayed complexity, Eq. (48), p. 18. -/
noncomputable def standardEigenComplexity (αA κE Tin TA ε : ℝ) : ℝ :=
  αA * κE * (Tin + TA) / ε

/-- Corollary 23's displayed complexity, Eq. (49), p. 18. -/
noncomputable def inverseEigenComplexity (αA ρ0 κE Tin TA ε : ℝ) : ℝ :=
  αA * ρ0 * κE * (Tin + TA) / ε

/-- Theorem 24's displayed complexity, Eq. (50), p. 19.  The fractional power
`κ_B^{3/2}` is written as `κ_B * sqrt κ_B`. -/
noncomputable def hermitianComplexity (κB αA αB Tin TA TB Bnorm ε : ℝ) : ℝ :=
  Real.sqrt κB * Tin +
    (αA * (κB * Real.sqrt κB)) / (Bnorm * ε) *
      (TA + αB * κB * TB / Bnorm)

/-- Corollary 25's displayed complexity, Eq. (54), p. 21.  The fractional power
`κ_B^{5/2}` is written as `κ_B^2 * sqrt κ_B`. -/
noncomputable def sparseHermitianComplexity
    (κB sA sB Amax Bmax Tin Bnorm ε : ℝ) : ℝ :=
  Real.sqrt κB * Tin +
    (κB ^ 2 * Real.sqrt κB) * sA * sB * Amax * Bmax / (ε * Bnorm ^ 2)

/-- Corollary 27's product-encoding scale `2‖A₁‖‖A₂‖` (p. 21). -/
def productScale (A1norm A2norm : ℝ) : ℝ := 2 * A1norm * A2norm

/-- Corollary 27's product-encoding error `√2(‖A₁‖ε₂ + ‖A₂‖ε₁)` (p. 21). -/
noncomputable def productError (A1norm A2norm ε1 ε2 : ℝ) : ℝ :=
  Real.sqrt 2 * (A1norm * ε2 + A2norm * ε1)

/-- Corollary 27's product-encoding ancilla count `q₁ + q₂ + 2` (p. 21). -/
def productQubits (q1 q2 : ℕ) : ℕ := q1 + q2 + 2

/-- Corollary 27's synthesis time
`O(α₁(q₁+T₁)‖A₁‖⁻¹ + α₂(q₂+T₂)‖A₂‖⁻¹)` (p. 21). -/
noncomputable def productCost (α1 q1 T1 A1norm α2 q2 T2 A2norm : ℝ) : ℝ :=
  α1 * (q1 + T1) / A1norm + α2 * (q2 + T2) / A2norm

end Qatlib.Papers.GenEigenODE20.MainResults
