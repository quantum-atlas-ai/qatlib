/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — paper-local transport model (Block `MainResults`)

Fixed paper version: arXiv:2505.00370 (statement lines of `2505.00370.txt`
quoted in the docstrings below). This module introduces the model in which the
paper-layer statements about Section 5 are expressed.

The paper studies the warped-phase transport equation (2.4), p. 7:

  ∂_t w = −H₁ ∂_p w + i H₂ w,      w(0,p) = ψ(p) u_I,

with H₁, H₂ Hermitian.  The proof of Lemma 5.3 (p. 29) conjugates the iH₂ term
away by `v(t,p) = U(t)⁻¹ w(t,p)` and then diagonalizes the (constant) Hermitian
H₁ = Q Λ Q*, reducing (2.4) to decoupled scalar transport equations

  ∂_t z_j = −λ_j ∂_p z_j,      z_j(0,p) = ψ(p) ũ_{I,j},

whose characteristic solution is `z_j(t,p) = ψ(p − λ_j t) ũ_{I,j}`
(compare p. 30; the printed `ψ(p + λ_j t)` has the opposite sign to the
printed equation — the statements of Lemma 5.1 (p. 26) and of the boundary
estimates (5.3)–(5.10) are consistent with `p − λ_j t`, which is what we use).
All paper-layer theorems are stated about the explicit object `charSolution`
below.  `charSolution_isTransportSolution` verifies that this object really
solves the scalar transport equation pointwise, so the model is not vacuous.

Notation used by the paper and below: `‖·‖` is the Euclidean norm on `ℂ`,
`‖u‖² = ∑_j ‖u_j‖²`, `λ⁺ = λ_max⁺(H₁)`, `λ⁻ = λ_max⁻(H₁)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean norm `∑_j ‖u_j‖²` of a complex vector (paper: `‖u‖²`). -/
def vecNormSq (u : ι → ℂ) : ℝ := ∑ j, ‖u j‖ ^ 2

/-- The squared norm of a complex vector is nonnegative. -/
theorem vecNormSq_nonneg (u : ι → ℂ) : 0 ≤ vecNormSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The squared norm of the zero vector is zero. -/
theorem vecNormSq_zero : vecNormSq (fun _ : ι => (0 : ℂ)) = 0 := by
  simp [vecNormSq]

/-- Scaling a vector scales its squared norm by `‖c‖²`. -/
theorem vecNormSq_smul (c : ℂ) (u : ι → ℂ) :
    vecNormSq (fun j => c * u j) = ‖c‖ ^ 2 * vecNormSq u := by
  unfold vecNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, mul_pow]

/-- A uniform componentwise bound `‖u j − v j‖ ≤ C` gives the coarse estimate
`vecNormSq (u − v) ≤ |ι| · C²`. -/
theorem vecNormSq_sub_bound (u v : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j, ‖u j - v j‖ ≤ C) :
    vecNormSq (fun j => u j - v j) ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
  calc vecNormSq (fun j => u j - v j) = ∑ j, ‖u j - v j‖ ^ 2 := rfl
    _ ≤ ∑ _j : ι, C ^ 2 := Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (h j) 2
    _ = (Fintype.card ι : ℝ) * C ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The diagonalized characteristic solution of the warped transport equation:
`charSolution ψ lam u t p j = ψ (p − lam_j t) · u_j`.  This is the solution of
`∂_t z_j = −lam_j ∂_p z_j`, `z_j(0,p) = ψ(p) u_j` (Lemma 5.3 reduction, p. 29). -/
def charSolution (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (t p : ℝ) : ι → ℂ :=
  fun j => ψ (p - lam j * t) * u j

/-- The diagonal evolution `j ↦ e^{lam_j T} u_j`, i.e. `u_f(T)` in the
eigenbasis of H₁ for the homogeneous system. -/
def evolved (lam : ι → ℝ) (u : ι → ℂ) (T : ℝ) : ι → ℂ :=
  fun j => (Real.exp (lam j * T) : ℂ) * u j

/-- The recovery `u_f*(T,p) = e^p w(T,p)` of Theorem 5.1/5.2 (p. 27). -/
def recovery (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (T p : ℝ) : ι → ℂ :=
  fun j => (Real.exp p : ℂ) * charSolution ψ lam u T p j

/-- Tail decay condition (H1) of §4.1 (p. 23): on both far tails the profile is
at most `2ε`.  `lamPos`/`lamNeg` are the paper's `λ_max⁺(H₁)`, `λ_max⁻(H₁)`. -/
def TailDecay (ψ : ℝ → ℂ) (L R lamPos lamNeg T ε : ℝ) : Prop :=
  (∀ p, p ≤ -L + lamNeg * T → ‖ψ p‖ ≤ 2 * ε) ∧
  (∀ p, R - lamPos * T ≤ p → ‖ψ p‖ ≤ 2 * ε)

/-- The solution is genuine: each component of `charSolution` differentiates to
`−lam_j ∂_p` (the scalar transport equation of the Lemma 5.3 reduction). -/
theorem charSolution_isTransportSolution
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (hψ : Differentiable ℝ ψ)
    (t p : ℝ) (j : ι) :
    HasDerivAt (fun s : ℝ => charSolution ψ lam u s p j)
      (deriv ψ (p - lam j * t) * (-(lam j)) * u j) t ∧
    deriv (fun q : ℝ => charSolution ψ lam u t q j) p
      = deriv ψ (p - lam j * t) * u j := by
  constructor
  · have hinner : HasDerivAt (fun s : ℝ => p - lam j * s) (-(lam j)) t := by
      have hmul : HasDerivAt (fun s : ℝ => lam j * s) (lam j) t := by
        simpa using (hasDerivAt_id t).const_mul (lam j)
      have hsub := (hasDerivAt_const (x := t) (c := p)).sub hmul
      convert hsub using 1 <;> simp
    have hcomp : HasDerivAt (fun s : ℝ => ψ (p - lam j * s))
        (deriv ψ (p - lam j * t) * (-(lam j))) t := by
      have hψd : HasDerivAt ψ (deriv ψ (p - lam j * t)) (p - lam j * t) :=
        hψ.differentiableAt.hasDerivAt
      simpa [Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using HasDerivAt.scomp t hψd hinner
    have := hcomp.mul_const (u j)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with s
    simp only [charSolution]
  · have hinner : HasDerivAt (fun q : ℝ => q - lam j * t) 1 p := by
      simpa using (hasDerivAt_id p).sub_const (lam j * t)
    have hcomp : HasDerivAt (fun q : ℝ => ψ (q - lam j * t))
        (deriv ψ (p - lam j * t) * 1) p := by
      have hψd : HasDerivAt ψ (deriv ψ (p - lam j * t)) (p - lam j * t) :=
        hψ.differentiableAt.hasDerivAt
      simpa [Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using HasDerivAt.scomp p hψd hinner
    have hmul : HasDerivAt (fun q : ℝ => charSolution ψ lam u t q j)
        (deriv ψ (p - lam j * t) * u j) p := by
      have h1 : HasDerivAt (fun q : ℝ => ψ (q - lam j * t))
          (deriv ψ (p - lam j * t)) p := by
        simpa using hcomp
      simpa [charSolution] using h1.mul_const (u j)
    rw [hmul.deriv]

end Qatlib.Papers.Schrodinger25.MainResults
