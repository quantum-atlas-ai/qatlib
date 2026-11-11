/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 — the QLA readout model

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015).

This file supplies the finite-dimensional vocabulary shared by the five
source claims: the sparse vector preparation of the section "A procedure
for applying QLA to GPR" (page 3), the Hermitian eigenbasis and spectral
inverse of the matrix `A` (page 3), the post-selected amplitudes of step 4
(pages 3--4), the readout expectation of the operator
`X_A ⊗ I_B ⊗ |1><1|_C ⊗ |1><1|_D` (page 4), and the two GPR estimators
of Eqs. (10)--(11) (page 4).

Everything is finite-dimensional real linear algebra over `Fin n`.  The
vectors are functions `Fin n → ℝ`; `A` is represented through an
orthonormal eigenbasis `μ` and real eigenvalues `lam`, i.e.
`A = ∑ i, lam i • μ i μ iᵀ`, exactly the spectral form used in the source
derivation.  The source's `(K + σ_n² I)` is Hermitian positive definite,
so this representation loses no generality.

The model keeps the source's constants `s_u, s_v` (sparsities of the
prepared vectors) and `c_u, c_v, c` (state-preparation and rotation
normalisations), because the scaling factors in the readout identities are
precisely what c003--c005 assert.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- The real inner product `∑ i, u i * v i` on `Fin n → ℝ`. -/
def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ i, u i * v i

/-- Expansion of a vector in the eigenbasis `μ`: `∑ i, c i • μ i`. -/
def expand {n : ℕ} (μ : Fin n → Fin n → ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  fun a => ∑ i, c i * μ i a

/-- Orthonormality of the finite family `μ`: `⟪μ i, μ j⟫ = δ_{ij}`. -/
def Orthonormal {n : ℕ} (μ : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, dot (μ i) (μ j) = if i = j then (1 : ℝ) else 0

/-- The spectral matrix `A = ∑ i, lam i • μ i μ iᵀ` in the orthonormal
eigenbasis `μ`; this is the source's Hermitian `A` in its eigenbasis. -/
def spectralMatrix {n : ℕ} (μ : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun a b => ∑ i, lam i * μ i a * μ i b

/-- Matrix-vector multiplication for a matrix represented as a function
`Fin n → Fin n → ℝ`. -/
def mulVec {n : ℕ} (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun a => ∑ b, A a b * v b

/-- The spectral inverse `A⁻¹ = ∑ i, (lam i)⁻¹ • μ i μ iᵀ`. -/
def spectralInverse {n : ℕ} (μ : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  spectralMatrix μ (fun i => (lam i)⁻¹)

/-- The quadratic form `uᵀ A⁻¹ v` in eigenbasis coordinates `γ`, `β`:
`∑ i, γ i * (β i * (lam i)⁻¹)`. -/
def quadForm {n : ℕ} (γ β lam : Fin n → ℝ) : ℝ :=
  ∑ i, γ i * (β i * (lam i)⁻¹)

/-- The GPR linear predictor `k_*ᵀ (K + σ_n² I)⁻¹ y` (source Eq. (4)),
written in the eigenbasis of `A = K + σ_n² I`: with `k_* = ∑ γ_i μ_i`
and `y = ∑ β_i μ_i`, this is `⟪k_*, A⁻¹ y⟫`. -/
def gprLinearPredictor {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (γ β lam : Fin n → ℝ) : ℝ :=
  dot (expand μ γ) (mulVec (spectralInverse μ lam) (expand μ β))

/-- The GPR predictive variance `k(x_*,x_*) − k_*ᵀ (K + σ_n² I)⁻¹ k_*`
(source Eq. (5)), in the eigenbasis of `A = K + σ_n² I`. -/
def gprPredictiveVariance {n : ℕ} (kxx : ℝ) (μ : Fin n → Fin n → ℝ)
    (β lam : Fin n → ℝ) : ℝ :=
  kxx - dot (expand μ β) (mulVec (spectralInverse μ lam) (expand μ β))

/-- The `|0⟩_A` branch amplitude of the post-selected state (page 4):
`(c_u / √s_u) · γ_i`. -/
def branchAmplitudeU {n : ℕ} (cu su : ℝ) (γ : Fin n → ℝ) (i : Fin n) : ℝ :=
  cu / Real.sqrt su * γ i

/-- The `|1⟩_A` branch amplitude of the post-selected state (page 4):
`(c_v c / √s_v) · β_i / lam_i`. -/
def branchAmplitudeV {n : ℕ} (cv c sv : ℝ) (β lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  cv * c / Real.sqrt sv * (β i / lam i)

/-- The expectation of `X_A ⊗ I_B ⊗ |1><1|_C ⊗ |1><1|_D` on the
post-selected state, written as on page 4:
`∑ i, (1/4) [ (a_i + b_i)² − (a_i − b_i)² ]`, where `a_i` is the
`|0⟩_A` amplitude and `b_i` the `|1⟩_A` amplitude. -/
def readoutExpectation {n : ℕ} (γ β lam : Fin n → ℝ)
    (cu cv c su sv : ℝ) : ℝ :=
  ∑ i, (1 / 4) *
    ((branchAmplitudeU cu su γ i + branchAmplitudeV cv c sv β lam i) ^ 2 -
      (branchAmplitudeU cu su γ i - branchAmplitudeV cv c sv β lam i) ^ 2)

/-! ## Eigenbasis algebra -/

/-- The spectral matrix acts on an eigenvector by the corresponding
eigenvalue: `A (μ j) = lam j • μ j`. -/
theorem mulVec_spectralMatrix_eigen {n : ℕ} {μ : Fin n → Fin n → ℝ}
    {lam : Fin n → ℝ} (horth : Orthonormal μ) (j : Fin n) :
    mulVec (spectralMatrix μ lam) (μ j) = fun a => lam j * μ j a := by
  funext a
  simp only [mulVec, spectralMatrix, Orthonormal, dot] at horth ⊢
  calc
    ∑ b, (∑ i, lam i * μ i a * μ i b) * μ j b
        = ∑ i, lam i * μ i a * (∑ b, μ i b * μ j b) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
    _ = ∑ i, lam i * μ i a * (if i = j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [horth i j]
    _ = lam j * μ j a := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij
            simp [hij]
          · intro hj
            simp at hj

/-- Matrix-vector multiplication is additive over an eigenbasis
expansion. -/
theorem mulVec_expand {n : ℕ} (A : Fin n → Fin n → ℝ)
    (μ : Fin n → Fin n → ℝ) (β : Fin n → ℝ) :
    mulVec A (expand μ β) = fun a => ∑ j, β j * mulVec A (μ j) a := by
  funext a
  simp only [mulVec, expand]
  calc
    ∑ b, A a b * (∑ j, β j * μ j b)
        = ∑ b, ∑ j, A a b * (β j * μ j b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ b, A a b * (β j * μ j b) := Finset.sum_comm
    _ = ∑ j, β j * (∑ b, A a b * μ j b) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring

/-- The spectral inverse acts on an expanded vector by dividing the
coordinates by the eigenvalues. -/
theorem mulVec_spectralInverse_expand {n : ℕ} {μ : Fin n → Fin n → ℝ}
    {lam : Fin n → ℝ} (horth : Orthonormal μ) (β : Fin n → ℝ) :
    mulVec (spectralInverse μ lam) (expand μ β) =
      fun a => ∑ j, β j * ((lam j)⁻¹ * μ j a) := by
  rw [mulVec_expand]
  funext a
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [spectralInverse]
  rw [mulVec_spectralMatrix_eigen horth j]

/-- The spectral inverse is a right inverse of the spectral matrix on
expanded vectors, for nonzero eigenvalues. -/
theorem spectralMatrix_apply_spectralInverse_expand {n : ℕ}
    {μ : Fin n → Fin n → ℝ} {lam : Fin n → ℝ}
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0) (β : Fin n → ℝ) :
    mulVec (spectralMatrix μ lam)
        (mulVec (spectralInverse μ lam) (expand μ β)) = expand μ β := by
  have hinv : mulVec (spectralInverse μ lam) (expand μ β) =
      expand μ (fun j => β j * (lam j)⁻¹) := by
    rw [mulVec_spectralInverse_expand horth]
    funext a; simp only [expand]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hinv, mulVec_expand]
  funext a
  simp only [expand]
  calc
    ∑ j, (β j * (lam j)⁻¹) * mulVec (spectralMatrix μ lam) (μ j) a
        = ∑ j, (β j * (lam j)⁻¹) * (lam j * μ j a) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mulVec_spectralMatrix_eigen horth j]
    _ = ∑ j, β j * μ j a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have h : (lam j)⁻¹ * lam j = (1 : ℝ) := inv_mul_cancel₀ (hlam j)
          calc
            (β j * (lam j)⁻¹) * (lam j * μ j a)
                = β j * ((lam j)⁻¹ * lam j) * μ j a := by ring
            _ = β j * μ j a := by rw [h]; ring

/-- Expanding an orthonormal family: the inner product of two expansions
is the coordinate inner product. -/
theorem dot_expand_orthonormal {n : ℕ} {μ : Fin n → Fin n → ℝ}
    (horth : Orthonormal μ) (γ β : Fin n → ℝ) :
    dot (expand μ γ) (expand μ β) = ∑ i, γ i * β i := by
  simp only [dot, expand, Orthonormal] at horth ⊢
  calc
    ∑ a, (∑ i, γ i * μ i a) * (∑ j, β j * μ j a)
        = ∑ a, ∑ i, ∑ j, (γ i * μ i a) * (β j * μ j a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ a, (γ i * μ i a) * (β j * μ j a) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, γ i * β j * (∑ a, μ i a * μ j a) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
    _ = ∑ i, ∑ j, γ i * β j * (if i = j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [horth i j]
    _ = ∑ i, γ i * β i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [Ne.symm hji]
          · intro hi
            simp at hi

/-- The source's `uᵀ A⁻¹ v` in the eigenbasis: for `u = ∑ γ_i μ_i` and
`v = ∑ β_i μ_i`, `⟪u, A⁻¹ v⟫ = ∑ i, γ_i β_i / lam_i`. -/
theorem dot_spectralInverse_expand {n : ℕ} {μ : Fin n → Fin n → ℝ}
    {lam : Fin n → ℝ} (horth : Orthonormal μ) (γ β : Fin n → ℝ) :
    dot (expand μ γ) (mulVec (spectralInverse μ lam) (expand μ β)) =
      quadForm γ β lam := by
  rw [mulVec_spectralInverse_expand horth β]
  have hexp : (fun a => ∑ j, β j * ((lam j)⁻¹ * μ j a)) =
      expand μ (fun j => β j * (lam j)⁻¹) := by
    funext a; simp only [expand]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, dot_expand_orthonormal horth]
  simp only [quadForm]

/-! ## The readout expectation identity -/

/-- Page 4 of the source: the expectation of
`X_A ⊗ I_B ⊗ |1><1|_C ⊗ |1><1|_D` on the post-selected state equals
`c · s_u^{-1/2} · s_v^{-1/2} · c_u · c_v · uᵀ A⁻¹ v`, where `u` and `v`
are the eigenbasis expansions with coordinates `γ` and `β`, and `A⁻¹` is
the spectral inverse of `A = ∑ lam_i μ_i μ_iᵀ`. -/
theorem readoutExpectation_eq {n : ℕ} (γ β lam : Fin n → ℝ)
    (cu cv c su sv : ℝ) (hsu : 0 < su) (hsv : 0 < sv) :
    readoutExpectation γ β lam cu cv c su sv
      = c * (Real.sqrt su)⁻¹ * (Real.sqrt sv)⁻¹ * cu * cv * quadForm γ β lam := by
  have hterm : ∀ i : Fin n,
      (1 / 4) *
        ((branchAmplitudeU cu su γ i + branchAmplitudeV cv c sv β lam i) ^ 2 -
          (branchAmplitudeU cu su γ i - branchAmplitudeV cv c sv β lam i) ^ 2)
        = branchAmplitudeU cu su γ i * branchAmplitudeV cv c sv β lam i := by
    intro i; ring
  simp only [readoutExpectation, quadForm]
  simp_rw [hterm]
  simp only [branchAmplitudeU, branchAmplitudeV]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

end Qatlib.Papers.QGaussProc15.MainResults
