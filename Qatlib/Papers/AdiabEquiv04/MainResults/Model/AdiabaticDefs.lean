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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

abbrev Vector (ι : Type) := ι → ℂ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def normSq (ψ : Vector ι) : ℝ := ∑ i, Complex.normSq (ψ i)

def IsNormalized (ψ : Vector ι) : Prop := normSq ψ = 1

def l2Dist (ψ φ : Vector ι) : ℝ := Real.sqrt (normSq (ψ - φ))

def rayleigh (H : Matrix ι ι ℂ) (ψ : Vector ι) : ℝ := ((star ψ) ⬝ᵥ (H *ᵥ ψ)).re

def basisKet (a : ι) : Vector ι := fun i => if i = a then 1 else 0

def ketDensity (ψ : Vector ι) : Matrix ι ι ℂ := fun i j => ψ i * star (ψ j)

structure Hamiltonian (ι : Type) [Fintype ι] [DecidableEq ι] where

  mat : Matrix ι ι ℂ

  herm : mat.IsHermitian

namespace Hamiltonian

def add (H₁ H₂ : Hamiltonian ι) : Hamiltonian ι :=
  ⟨H₁.mat + H₂.mat, H₁.herm.add H₂.herm⟩

def realSmul (c : ℝ) (H : Hamiltonian ι) : Hamiltonian ι :=
  ⟨(c : ℂ) • H.mat,
    H.herm.smul (by
      rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])⟩

def path (H₀ H₁ : Hamiltonian ι) (s : ℝ) : Hamiltonian ι :=
  add (realSmul (1 - s) H₀) (realSmul s H₁)

end Hamiltonian

def eigvals (H : Hamiltonian ι) : Fin (Fintype.card ι) → ℝ := H.herm.eigenvalues₀

def groundEnergy (H : Hamiltonian ι) (h : 0 < Fintype.card ι) : ℝ :=
  eigvals H ⟨Fintype.card ι - 1, by omega⟩

def secondLowestEnergy (H : Hamiltonian ι) (h : 2 ≤ Fintype.card ι) : ℝ :=
  eigvals H ⟨Fintype.card ι - 2, by omega⟩

def spectralGap (H : Hamiltonian ι) (h : 2 ≤ Fintype.card ι) : ℝ :=
  secondLowestEnergy H h - groundEnergy H (by omega)

def GapAtLeast (H : Hamiltonian ι) (γ : ℝ) : Prop :=
  ∃ h : 2 ≤ Fintype.card ι, γ ≤ spectralGap H h

def IsGroundVector (H : Hamiltonian ι) (ψ : Vector ι) : Prop :=
  IsNormalized ψ ∧ ∀ φ : Vector ι, IsNormalized φ → rayleigh H.mat ψ ≤ rayleigh H.mat φ

def HasUniqueGroundState (H : Hamiltonian ι) : Prop :=
  ∃ ψ : Vector ι, IsGroundVector H ψ ∧
    ∀ φ : Vector ι, IsGroundVector H φ → ∃ c : ℂ, Complex.normSq c = 1 ∧ φ = c • ψ

variable {σ : Type} [Fintype σ] [DecidableEq σ]

def restrict (V : Matrix ι σ ℂ) (H : Hamiltonian ι) (hV : Vᴴ * V = 1) :
    Hamiltonian σ :=
  ⟨Vᴴ * H.mat * V, by
    unfold Matrix.IsHermitian
    have h1 : (Vᴴ * H.mat * V)ᴴ = Vᴴ * H.matᴴ * V := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [h1, H.herm.eq, Matrix.mul_assoc]⟩

def basisProj (P : ι → Prop) [DecidablePred P] : Matrix ι ι ℂ :=
  fun i j => if i = j ∧ P i then 1 else 0

def compress (P : ι → Prop) [DecidablePred P] (H : Hamiltonian ι) : Matrix ι ι ℂ :=
  basisProj P * H.mat * basisProj P

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

def IsDensityMatrix (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.IsHermitian ∧ (∀ ψ : Vector ι, 0 ≤ rayleigh ρ ψ) ∧ Matrix.trace ρ = 1

def traceNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i : Fin (Fintype.card ι), |hA.eigenvalues₀ i|

def traceDistance (ρ σ : Matrix ι ι ℂ) (h : (ρ - σ).IsHermitian) : ℝ :=
  (1 / 2) * traceNorm (ρ - σ) h

def TraceClose (ρ σ : Matrix ι ι ℂ) (h : (ρ - σ).IsHermitian) (ε : ℝ) : Prop :=
  traceDistance ρ σ h ≤ ε

def partialTrace {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ : Matrix (α × β) (α × β) ℂ) :
    Matrix α α ℂ :=
  fun a a' => ∑ b, ρ (a, b) (a', b)

def polyBound (f : ℕ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
    ∀ L : ℕ, ∀ ε : ℝ, 0 < ε →
      f L ε ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e

structure CostDefs where

  run : List Bool → List Bool

  cost : List Bool → ℕ

def CostDefs.IsPolyTime (M : CostDefs) : Prop :=
  ∃ C : ℕ, ∃ d : ℕ, ∀ x : List Bool, M.cost x ≤ C * (x.length + 1) ^ d

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
