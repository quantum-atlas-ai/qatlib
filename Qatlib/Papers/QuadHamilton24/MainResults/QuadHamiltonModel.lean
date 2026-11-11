/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.Exponential

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

/-- The 2×2 block matrix `A = [[F₁, F₀], [F₂, F₃]]` of (2.61) on the block index `N ⊕ M`. -/
def blockA (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ) :
    Matrix (N ⊕ M) (N ⊕ M) ℂ :=
  fromBlocks F₁ F₀ F₂ F₃

/-- The matrix Riccati right-hand side `F₀ + F₁ y + y F₂ y + y F₃` of (3.15)/(3.16). -/
def riccatiRHS (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) (y : Matrix N M ℂ) : Matrix N M ℂ :=
  F₀ + F₁ * y + y * F₂ * y + y * F₃

/-- The sign that the source's derivation (2.59) and the proof of Proposition 1 actually
produce: `F₀ + F₁ y − y F₂ y − y F₃`.  See `Proposition1SignNote`. -/
def riccatiRHSMinus (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) (y : Matrix N M ℂ) : Matrix N M ℂ :=
  F₀ + F₁ * y - y * F₂ * y - y * F₃

/-- `C(A) = sup_{t∈[0,T]} ‖exp(At)‖` of (3.18).  For nonempty finite index types
the supremum is over the compact interval `[0,T]`. -/
def Csup {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (T : ℝ) : ℝ :=
  sSup ((fun t : ℝ => ‖NormedSpace.exp (t • A)‖) '' Set.Icc 0 T)

/-- `C_d` of (3.21). -/
def Cd {I : Type*} [Fintype I] [DecidableEq I] (F : Matrix I I ℂ) (T : ℝ) : ℝ :=
  sSup ((fun t : ℝ => ‖NormedSpace.exp (t • F)‖) '' Set.Icc 0 T)

/-- The Lyapunov exponent `κ_L = T ‖A‖ C(A)` of (4.2). -/
def kappaL {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (T : ℝ) : ℝ :=
  T * ‖A‖ * Csup A T

/-- The growth ratio `g = max_{t∈[0,T]} ‖x(t)‖ / ‖x(T)‖` of (4.6), as data
`g` together with its defining property. -/
def gRatio (x : ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup ((fun t : ℝ => x t) '' Set.Icc 0 T) / x T

end Qatlib.Papers.QuadHamilton24.MainResults

/-! ## Cost-model vocabulary shared by the algorithmic claims -/

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

section CostModel

/-- `IsPolyBound x φ` reads the paper's `poly(x₁,…,xₙ)` as an upper bound: `φ` is at
most a constant times a product of positive powers of `(1 + |x_i|)`.  This is the
standard reading of a polynomial overhead in the cost bounds. -/
def IsPolyBound {n : ℕ} (x : Fin n → ℝ) (φ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, φ ≤ C * (∏ i : Fin n, (1 + |x i|)) ^ d

/-- The mechanical-system matrix `A = [[0, I], [-M⁻¹V, -M⁻¹R]]` of (4.15)/(4.22). -/
def quadraticA (MinvV MinvR : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  fromBlocks 0 1 (-MinvV) (-MinvR)

/-- The transformed matrix `Ã = [[0, √M⁻¹√V], [-√M⁻¹√V, -√M⁻¹√R√M⁻¹]]` of (4.60),
represented through its four blocks (the square roots are data). -/
def tildeA (B C D : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  fromBlocks 0 B C D

/-- The block `J = [[0, I], [-I, 0]]` of (4.109). -/
def Jblock : Matrix (N ⊕ N) (N ⊕ N) ℂ := fromBlocks 0 1 (-1) 0

/-- The block-diagonal `Q = diag(V, I)` of (4.108). -/
def Qblock (V : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ := fromBlocks V 0 0 1

end CostModel

end Qatlib.Papers.QuadHamilton24.MainResults
