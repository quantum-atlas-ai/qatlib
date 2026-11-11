/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-!
# Finite-dimensional adiabatic definitions

This module defines finite complex vectors, Hermitian Hamiltonians, ground energies, spectral
gaps, and ground vectors for the adiabatic computation model of [AharonovEtAl2007Adiabatic]. It
also supplies basis compression, density matrices, trace distance, partial trace, and polynomial
cost predicates used by later constructions.

## Main statements

* `Hamiltonian`: a finite Hermitian matrix.
* `IsGroundVector`: a normalized vector minimizing the Rayleigh expression.
* `traceDistance` and `partialTrace`: finite-dimensional state comparison and reduction.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- Complex-valued vectors indexed by `ι`. -/
abbrev Vector (ι : Type) := ι → ℂ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sum of the squared complex norms of the coordinates of a vector. -/
def normSq (ψ : Vector ι) : ℝ := ∑ i, Complex.normSq (ψ i)

/-- The condition that a vector has squared norm one. -/
def IsNormalized (ψ : Vector ι) : Prop := normSq ψ = 1

/-- The Euclidean distance defined as the square root of `normSq (ψ - φ)`. -/
def l2Dist (ψ φ : Vector ι) : ℝ := Real.sqrt (normSq (ψ - φ))

/-- The real part of the quadratic expression `ψᴴ H ψ`, without normalization by the squared
norm of `ψ`. -/
def rayleigh (H : Matrix ι ι ℂ) (ψ : Vector ι) : ℝ := ((star ψ) ⬝ᵥ (H *ᵥ ψ)).re

/-- The coordinate vector equal to one at `a` and zero elsewhere. -/
def basisKet (a : ι) : Vector ι := fun i => if i = a then 1 else 0

/-- The outer product `ψ ψᴴ`, with entries `ψ i * star (ψ j)`. -/
def ketDensity (ψ : Vector ι) : Matrix ι ι ℂ := fun i j => ψ i * star (ψ j)

/-- A finite complex matrix together with a proof that it is Hermitian. -/
structure Hamiltonian (ι : Type) [Fintype ι] [DecidableEq ι] where

  mat : Matrix ι ι ℂ

  herm : mat.IsHermitian

namespace Hamiltonian

/-- The Hamiltonian obtained by adding the matrices of two Hamiltonians. -/
def add (H₁ H₂ : Hamiltonian ι) : Hamiltonian ι :=
  ⟨H₁.mat + H₂.mat, H₁.herm.add H₂.herm⟩

/-- The Hamiltonian obtained by multiplying a Hermitian matrix by a real scalar. -/
def realSmul (c : ℝ) (H : Hamiltonian ι) : Hamiltonian ι :=
  ⟨(c : ℂ) • H.mat,
    H.herm.smul (by
      rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])⟩

/-- The affine Hamiltonian path `(1 - s) H₀ + s H₁`. -/
def path (H₀ H₁ : Hamiltonian ι) (s : ℝ) : Hamiltonian ι :=
  add (realSmul (1 - s) H₀) (realSmul s H₁)

end Hamiltonian

/-- The real eigenvalues of a Hamiltonian in the order supplied by `eigenvalues₀`. -/
def eigvals (H : Hamiltonian ι) : Fin (Fintype.card ι) → ℝ := H.herm.eigenvalues₀

/-- The lowest eigenvalue of a Hamiltonian on a nonempty finite basis, taken at the last index
of `eigvals`. -/
def groundEnergy (H : Hamiltonian ι) (h : 0 < Fintype.card ι) : ℝ :=
  eigvals H ⟨Fintype.card ι - 1, by omega⟩

/-- The second-lowest eigenvalue, counting multiplicity, on a basis of cardinality at least two. -/
def secondLowestEnergy (H : Hamiltonian ι) (h : 2 ≤ Fintype.card ι) : ℝ :=
  eigvals H ⟨Fintype.card ι - 2, by omega⟩

/-- The difference between the second-lowest eigenvalue and the ground energy. -/
def spectralGap (H : Hamiltonian ι) (h : 2 ≤ Fintype.card ι) : ℝ :=
  secondLowestEnergy H h - groundEnergy H (by omega)

/-- The condition that the basis has at least two elements and the spectral gap is at least `γ`. -/
def GapAtLeast (H : Hamiltonian ι) (γ : ℝ) : Prop :=
  ∃ h : 2 ≤ Fintype.card ι, γ ≤ spectralGap H h

/-- The condition that `ψ` is normalized and minimizes the Rayleigh expression among all
normalized vectors. -/
def IsGroundVector (H : Hamiltonian ι) (ψ : Vector ι) : Prop :=
  IsNormalized ψ ∧ ∀ φ : Vector ι, IsNormalized φ → rayleigh H.mat ψ ≤ rayleigh H.mat φ

/-- The existence of a ground vector such that every ground vector is its scalar multiple by a
complex number of squared norm one. -/
def HasUniqueGroundState (H : Hamiltonian ι) : Prop :=
  ∃ ψ : Vector ι, IsGroundVector H ψ ∧
    ∀ φ : Vector ι, IsGroundVector H φ → ∃ c : ℂ, Complex.normSq c = 1 ∧ φ = c • ψ

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The Hamiltonian with matrix `Vᴴ * H.mat * V`, for an isometric matrix `V`. -/
def restrict (V : Matrix ι σ ℂ) (H : Hamiltonian ι) (hV : Vᴴ * V = 1) :
    Hamiltonian σ :=
  ⟨Vᴴ * H.mat * V, by
    unfold Matrix.IsHermitian
    have h1 : (Vᴴ * H.mat * V)ᴴ = Vᴴ * H.matᴴ * V := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [h1, H.herm.eq, Matrix.mul_assoc]⟩

/-- The diagonal matrix projecting onto the coordinates satisfying the decidable predicate `P`. -/
def basisProj (P : ι → Prop) [DecidablePred P] : Matrix ι ι ℂ :=
  fun i j => if i = j ∧ P i then 1 else 0

/-- The matrix obtained by multiplying `H.mat` on both sides by the coordinate projection
`basisProj P`. -/
def compress (P : ι → Prop) [DecidablePred P] (H : Hamiltonian ι) : Matrix ι ι ℂ :=
  basisProj P * H.mat * basisProj P

/-- Compression of a Hamiltonian by a coordinate projection is Hermitian. -/
theorem compress_isHermitian (P : ι → Prop) [DecidablePred P] (H : Hamiltonian ι) :
    (compress P H).IsHermitian := by
  unfold compress Matrix.IsHermitian
  have hP : (basisProj P)ᴴ = basisProj P := by
    ext i j
    unfold basisProj
    rw [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hP : P i <;> simp [hP]
    · have hji : ¬ (j = i) := fun h => hij h.symm
      simp [hij, hji]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, H.herm.eq]
  rw [Matrix.mul_assoc]

/-- The condition that a matrix is Hermitian, has nonnegative Rayleigh expression on every
vector, and has trace one. -/
def IsDensityMatrix (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.IsHermitian ∧ (∀ ψ : Vector ι, 0 ≤ rayleigh ρ ψ) ∧ Matrix.trace ρ = 1

/-- The sum of the absolute values of the eigenvalues of a Hermitian matrix. -/
def traceNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i : Fin (Fintype.card ι), |hA.eigenvalues₀ i|

/-- Half the trace norm of the Hermitian difference `ρ - σ`. -/
def traceDistance (ρ σ : Matrix ι ι ℂ) (h : (ρ - σ).IsHermitian) : ℝ :=
  (1 / 2) * traceNorm (ρ - σ) h

/-- The condition that the trace distance between `ρ` and `σ` is at most `ε`. -/
def TraceClose (ρ σ : Matrix ι ι ℂ) (h : (ρ - σ).IsHermitian) (ε : ℝ) : Prop :=
  traceDistance ρ σ h ≤ ε

/-- The partial trace over the second factor of a finite product basis, obtained by summing `ρ
(a, b) (a', b)` over `b`. -/
def partialTrace {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ : Matrix (α × β) (α × β) ℂ) :
    Matrix α α ℂ :=
  fun a a' => ∑ b, ρ (a, b) (a', b)

/-- The existence of a positive constant and natural exponents bounding `f L ε` by `C * (L + 1)
^ d * (1/ε) ^ e` for every positive `ε`. -/
def polyBound (f : ℕ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
    ∀ L : ℕ, ∀ ε : ℝ, 0 < ε →
      f L ε ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e

/-- A function on Boolean lists together with a natural-valued cost function on those lists. -/
structure CostDefs where

  run : List Bool → List Bool

  cost : List Bool → ℕ

/-- The condition that `M.cost x` is bounded by `C * (x.length + 1) ^ d` for fixed natural
numbers `C` and `d`. -/
def CostDefs.IsPolyTime (M : CostDefs) : Prop :=
  ∃ C : ℕ, ∃ d : ℕ, ∀ x : List Bool, M.cost x ≤ C * (x.length + 1) ^ d

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
