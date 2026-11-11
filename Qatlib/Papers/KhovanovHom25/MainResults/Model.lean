/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Paper model for KhovanovHom25

Source: arXiv:2501.12378v2 (23 Jan 2025), *A quantum algorithm for Khovanov homology*.

This file sets up the paper-layer objects used by the claim files:

* a cochain complex of finite-dimensional complex inner-product spaces with
  differential `d`, its adjoint `d†`, and the Hodge Laplacian
  `Δᵢ = dᵢ†dᵢ + dᵢ₋₁dᵢ₋₁†` (eq. (6.1));
* the harmonic subspace `ℋᵢ = ker Δᵢ` (eq. (6.2));
* elementary model objects for Khovanov data: the two-dimensional space
  `V = span(1, X)` and the merge/comultiplication maps of Section 8.2.1.

Cochains are indexed by `ℕ` (degrees `0, 1, 2, …`), matching the bounded
cohomological support of the Khovanov complexes in the paper.  The "lower"
Laplacian summand at degree `0` is set to zero, which is the paper's convention
`d₋₁ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-! ## Cochain complexes and the Hodge Laplacian -/

/-- A cochain complex of finite-dimensional complex inner-product spaces, as in
Section 6.1 of the paper.  The only data beyond the spaces are the differentials
`dᵢ : Cⁱ → Cⁱ⁺¹` and the chain condition `dᵢ₊₁ ∘ dᵢ = 0`. -/
structure CochainComplex where
  /-- The cochain spaces `Cⁱ`, indexed by `ℕ`. -/
  C : ℕ → Type*
  [normed : ∀ i, NormedAddCommGroup (C i)]
  [ip : ∀ i, InnerProductSpace ℂ (C i)]
  [fd : ∀ i, FiniteDimensional ℂ (C i)]
  /-- The differential `dᵢ : Cⁱ → Cⁱ⁺¹`. -/
  d : ∀ i, C i →ₗ[ℂ] C (i + 1)
  /-- The chain condition `dᵢ₊₁ ∘ dᵢ = 0`. -/
  d_comp : ∀ (i : ℕ) (x : C i), d (i + 1) (d i x) = 0

/-- The normed group structure on each cochain space, exposed as a global
instance so that typeclass search can find it from `K.C i`. -/
instance (K : CochainComplex) (i : ℕ) : NormedAddCommGroup (K.C i) := K.normed i

/-- The inner-product structure on each cochain space. -/
instance (K : CochainComplex) (i : ℕ) : InnerProductSpace ℂ (K.C i) := K.ip i

/-- Finite-dimensionality of each cochain space. -/
instance (K : CochainComplex) (i : ℕ) : FiniteDimensional ℂ (K.C i) := K.fd i

namespace CochainComplex

variable (K : CochainComplex)

/-- The adjoint `dᵢ† : Cⁱ⁺¹ → Cⁱ` of the differential, defined through the
inner product as in Section 6.1. -/
def dAdj (i : ℕ) : K.C (i + 1) →ₗ[ℂ] K.C i :=
  (K.d i).adjoint

/-- The `dᵢ†dᵢ` summand of the Laplacian, `Δᵢ`'s term with both indices equal
to `i`. -/
def lapDown (i : ℕ) : K.C i →ₗ[ℂ] K.C i :=
  (K.dAdj i).comp (K.d i)

/-- The `dᵢ₋₁dᵢ₋₁†` summand of the Laplacian: `dᵢ₋₁dᵢ₋₁†` for `i ≥ 1`, and `0`
at degree `0` (the paper's `d₋₁ = 0`). -/
def lapUp : ∀ i : ℕ, K.C i →ₗ[ℂ] K.C i
  | 0 => 0
  | i + 1 => (K.d i).comp (K.dAdj i)

/-- The Hodge Laplacian `Δᵢ = dᵢ†dᵢ + dᵢ₋₁dᵢ₋₁†` of eq. (6.1). -/
def lap (i : ℕ) : K.C i →ₗ[ℂ] K.C i :=
  K.lapDown i + K.lapUp i

/-- The norm of the "upper" differential applied to a cochain, `0` at degree
`0` and `‖dᵢ₋₁† x‖` at degree `i`. -/
def upNorm : ∀ i : ℕ, K.C i → ℝ
  | 0 => fun _ => 0
  | i + 1 => fun x => ‖K.dAdj i x‖

/-- The kernel of the "upper" differential: `⊤` at degree `0` and
`ker dᵢ₋₁†` at degree `i`. -/
def upKer : ∀ i : ℕ, Submodule ℂ (K.C i)
  | 0 => ⊤
  | i + 1 => (K.dAdj i).ker

/-- The harmonic subspace `ℋᵢ = {x | Δᵢ x = 0}` of eq. (6.2). -/
def harmonic (i : ℕ) : Submodule ℂ (K.C i) :=
  (K.lap i).ker

/-- The degree-zero up-Laplacian vanishes (there is no `d₀†` term). -/
@[simp]
theorem lapUp_zero : K.lapUp 0 = 0 := rfl

/-- The up-Laplacian in degree `i+1` is `dᵢ ∘ dᵢ†`. -/
@[simp]
theorem lapUp_succ (i : ℕ) : K.lapUp (i + 1) = (K.d i).comp (K.dAdj i) := rfl

/-- The up-norm vanishes in degree zero. -/
@[simp]
theorem upNorm_zero (x : K.C 0) : K.upNorm 0 x = 0 := rfl

/-- The up-norm in degree `i+1` is the norm of `dᵢ† x`. -/
@[simp]
theorem upNorm_succ (i : ℕ) (x : K.C (i + 1)) : K.upNorm (i + 1) x = ‖K.dAdj i x‖ := rfl

/-- The up-kernel is everything in degree zero. -/
@[simp]
theorem upKer_zero : K.upKer 0 = ⊤ := rfl

/-- The up-kernel in degree `i+1` is `ker dᵢ†`. -/
@[simp]
theorem upKer_succ (i : ℕ) : K.upKer (i + 1) = (K.dAdj i).ker := rfl

/-- Harmonic chains are exactly the Laplacian kernel. -/
theorem mem_harmonic (i : ℕ) (x : K.C i) : x ∈ K.harmonic i ↔ K.lap i x = 0 := Iff.rfl

/-- The up-kernel is the zero set of the up-norm. -/
theorem mem_upKer_iff (i : ℕ) (x : K.C i) : x ∈ K.upKer i ↔ K.upNorm i x = 0 := by
  cases i with
  | zero => simp
  | succ j => simp

/-- The chain condition for the adjoints: `dᵢ† ∘ dᵢ₊₁† = 0`, the adjoint of
`dᵢ₊₁ ∘ dᵢ = 0` (adjoint of `d_comp`). -/
theorem dAdj_comp_dAdj (i : ℕ) : (K.dAdj i).comp (K.dAdj (i + 1)) = 0 := by
  have hd : (K.d (i + 1)).comp (K.d i) = 0 := by
    ext x
    exact K.d_comp i x
  have hadj := LinearMap.adjoint_comp (K.d (i + 1)) (K.d i)
  rw [hd] at hadj
  simpa [dAdj] using hadj.symm

/-- Pointwise form of `dAdj_comp_dAdj`: `dᵢ† dᵢ₊₁† y = 0`. -/
@[simp]
theorem dAdj_comp_dAdj_apply (i : ℕ) (y : K.C (i + 2)) :
    K.dAdj i (K.dAdj (i + 1) y) = 0 := by
  have h := congrArg (fun f : K.C (i + 2) →ₗ[ℂ] K.C i => f y) (K.dAdj_comp_dAdj i)
  simpa using h

/-- Pointwise form of the Laplacian: down part plus up part. -/
@[simp]
theorem lap_apply (i : ℕ) (x : K.C i) :
    K.lap i x = K.dAdj i (K.d i x) + K.lapUp i x := rfl

/-- The Laplacian splits as the sum of the down- and up-Laplacians. -/
theorem lap_eq_lapDown_add_lapUp (i : ℕ) :
    K.lap i = K.lapDown i + K.lapUp i := rfl

/-- The two Laplacian summands annihilate each other: `(d†d)(dd†) = 0`, because
`d ∘ d = 0`. -/
theorem lapDown_comp_lapUp (i : ℕ) : (K.lapDown i).comp (K.lapUp i) = 0 := by
  cases i with
  | zero => simp [lapDown]
  | succ j =>
      rw [lapDown, lapUp_succ]
      have hd : (K.d (j + 1)).comp (K.d j) = 0 := by
        ext y
        exact K.d_comp j y
      ext x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [show K.d (j + 1) (K.d j (K.dAdj j x)) = 0 from by
        rw [← LinearMap.comp_apply, hd]
        simp]
      simp

/-- The Laplacian is positive semidefinite: its inner-product quadratic form is
the sum of two squared norms. -/
theorem inner_lap (i : ℕ) (x : K.C i) :
    ⟪x, K.lap i x⟫ = ((‖K.d i x‖ ^ 2 + K.upNorm i x ^ 2 : ℝ) : ℂ) := by
  have h1 : ⟪x, K.dAdj i (K.d i x)⟫ = ((‖K.d i x‖ ^ 2 : ℝ) : ℂ) := by
    rw [show K.dAdj i (K.d i x) = (K.d i).adjoint (K.d i x) from rfl,
      LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_num [Complex.ofReal_pow]
  cases i with
  | zero =>
      simp only [lap, lapDown, lapUp_zero, add_zero, upNorm_zero,
        LinearMap.comp_apply]
      rw [h1]
      push_cast
      ring
  | succ j =>
      have h2 : ⟪x, K.d j (K.dAdj j x)⟫ = ((‖K.dAdj j x‖ ^ 2 : ℝ) : ℂ) := by
        rw [show K.dAdj j x = (K.d j).adjoint x from rfl]
        rw [← LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
        norm_num [Complex.ofReal_pow]
      simp only [lap, lapDown, lapUp_succ, LinearMap.comp_apply,
        LinearMap.add_apply, upNorm_succ]
      rw [inner_add_right, h1, h2]
      push_cast
      ring

/-- A cochain is harmonic iff it is killed by `dᵢ` and by the "upper"
differential. -/
theorem lap_eq_zero_iff (i : ℕ) (x : K.C i) :
    K.lap i x = 0 ↔ K.d i x = 0 ∧ K.upNorm i x = 0 := by
  constructor
  · intro hx
    have hinner := K.inner_lap i x
    rw [hx, inner_zero_right] at hinner
    have hreal : ‖K.d i x‖ ^ 2 + K.upNorm i x ^ 2 = 0 := by
      exact_mod_cast hinner.symm
    have hd : ‖K.d i x‖ = 0 := by
      nlinarith [sq_nonneg ‖K.d i x‖, sq_nonneg (K.upNorm i x)]
    have hu : K.upNorm i x = 0 := by
      nlinarith [sq_nonneg ‖K.d i x‖, sq_nonneg (K.upNorm i x)]
    exact ⟨norm_eq_zero.mp hd, hu⟩
  · rintro ⟨hd, hu⟩
    cases i with
    | zero =>
        simp only [lap, lapDown, lapUp_zero, add_zero, LinearMap.comp_apply]
        rw [hd]
        simp
    | succ j =>
        simp only [lap, lapDown, lapUp_succ, LinearMap.comp_apply,
          LinearMap.add_apply, upNorm_succ]
        have hdadj : K.dAdj j x = 0 := by
          have h : ‖K.dAdj j x‖ = 0 := by simpa using hu
          exact norm_eq_zero.mp h
        rw [hd, hdadj]
        simp

/-- `ℋᵢ` is the intersection of `ker dᵢ` and the kernel of the upper
differential (paper eq. (6.2): `ker dᵢ ∩ ker dᵢ₋₁†`). -/
theorem harmonic_eq_inf (i : ℕ) :
    K.harmonic i = (K.d i).ker ⊓ K.upKer i := by
  ext x
  rw [mem_harmonic, lap_eq_zero_iff]
  simp [mem_upKer_iff, LinearMap.mem_ker]

/-- `ker dᵢ` is the orthogonal complement of `range dᵢ†`. -/
theorem ker_eq_orthogonal_range_dAdj (i : ℕ) :
    (K.d i).ker = (K.dAdj i).rangeᗮ := by
  have h := LinearMap.orthogonal_range (K.dAdj i)
  simpa [dAdj] using h.symm

/-- `ker dᵢ†` is the orthogonal complement of `range dᵢ`. -/
theorem ker_dAdj_eq_orthogonal_range (i : ℕ) :
    (K.dAdj i).ker = (K.d i).rangeᗮ := by
  have h := LinearMap.orthogonal_range (K.d i)
  simpa [dAdj] using h.symm

/-- The harmonic chains are orthogonal to `Im dᵢ`. -/
theorem harmonic_le_orthogonal_range_left (i : ℕ) :
    K.harmonic (i + 1) ≤ (K.d i).rangeᗮ := by
  intro x hx
  rw [harmonic_eq_inf] at hx
  have h2 : x ∈ K.upKer (i + 1) := hx.2
  rw [upKer_succ, K.ker_dAdj_eq_orthogonal_range i] at h2
  exact h2

/-- The harmonic chains are orthogonal to `Im dᵢ₊₁†`. -/
theorem harmonic_le_orthogonal_range_right (i : ℕ) :
    K.harmonic (i + 1) ≤ (K.dAdj (i + 1)).rangeᗮ := by
  intro x hx
  rw [harmonic_eq_inf] at hx
  have h1 : x ∈ (K.d (i + 1)).ker := hx.1
  rwa [K.ker_eq_orthogonal_range_dAdj (i + 1)] at h1

/-- The harmonic chains are orthogonal to `Im dᵢ†`. -/
theorem harmonic_le_orthogonal_range_dAdj (i : ℕ) :
    K.harmonic i ≤ (K.dAdj i).rangeᗮ := by
  intro x hx
  rw [harmonic_eq_inf] at hx
  have h1 : x ∈ (K.d i).ker := hx.1
  rwa [K.ker_eq_orthogonal_range_dAdj i] at h1

/-- Orthogonality reverses inclusions: `H ⊆ Rᗮ` gives `R ⊆ Hᗮ`. -/
theorem orthogonal_of_le_orthogonal {i : ℕ} {H R : Submodule ℂ (K.C i)}
    (h : H ≤ Rᗮ) : R ≤ Hᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hu' : u ∈ Rᗮ := h hu
  rw [Submodule.mem_orthogonal] at hu'
  rw [← inner_conj_symm, hu' x hx]
  simp

/-- Theorem 9 (eq. (6.3)): `Cⁱ = ℋⁱ ⊕ (Im dᵢ₋₁ ⊔ Im dᵢ†)`, at degree `i+1`. -/
theorem harmonic_sup_ranges (i : ℕ) :
    K.harmonic (i + 1) ⊔ ((K.d i).range ⊔ (K.dAdj (i + 1)).range) = ⊤ := by
  have hle : (K.d i).range ≤ (K.d (i + 1)).ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact K.d_comp i z
  have hspan := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (K₁ := (K.d i).range) (K₂ := (K.d (i + 1)).ker) hle
  have hharm : (K.d i).rangeᗮ ⊓ (K.d (i + 1)).ker = K.harmonic (i + 1) := by
    rw [harmonic_eq_inf, upKer_succ, K.ker_dAdj_eq_orthogonal_range i, inf_comm]
  rw [hharm] at hspan
  have hker : K.harmonic (i + 1) ⊔ (K.d i).range = (K.d (i + 1)).ker := by
    rw [← hspan, sup_comm]
  have hone : (K.d (i + 1)).kerᗮ = (K.dAdj (i + 1)).range := by
    rw [K.ker_eq_orthogonal_range_dAdj (i + 1), Submodule.orthogonal_orthogonal]
  calc K.harmonic (i + 1) ⊔ ((K.d i).range ⊔ (K.dAdj (i + 1)).range)
      = (K.harmonic (i + 1) ⊔ (K.d i).range) ⊔ (K.dAdj (i + 1)).range := by
        rw [sup_assoc]
    _ = (K.d (i + 1)).ker ⊔ (K.dAdj (i + 1)).range := by rw [hker]
    _ = (K.d (i + 1)).ker ⊔ (K.d (i + 1)).kerᗮ := by rw [hone]
    _ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- Theorem 9 (eq. (6.3)), disjointness of `ℋᵢ` from the two image summands. -/
theorem harmonic_disjoint_ranges (i : ℕ) :
    Disjoint (K.harmonic (i + 1)) ((K.d i).range ⊔ (K.dAdj (i + 1)).range) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hh, hr⟩ := hx
  rw [Submodule.mem_sup] at hr
  obtain ⟨a, ha, b, hb, hab⟩ := hr
  have horthL : x ∈ (K.d i).rangeᗮ := K.harmonic_le_orthogonal_range_left i hh
  have horthR : x ∈ (K.dAdj (i + 1)).rangeᗮ :=
    K.harmonic_le_orthogonal_range_right i hh
  rw [Submodule.mem_orthogonal] at horthL horthR
  have hxa : ⟪a, a + b⟫ = 0 := by rw [hab]; exact horthL a ha
  have hxb : ⟪b, a + b⟫ = 0 := by rw [hab]; exact horthR b hb
  have hxx : ⟪a + b, a + b⟫ = 0 := by
    rw [inner_add_left, hxa, hxb, add_zero]
  rw [Submodule.mem_bot, ← hab]
  exact inner_self_eq_zero.mp hxx

/-- Eq. (6.3), orthogonal-complement form: the orthogonal complement of `ℋᵢ₊₁`
is the sum of the two image spaces. -/
theorem harmonic_orthogonal_eq_ranges (i : ℕ) :
    (K.harmonic (i + 1))ᗮ = (K.d i).range ⊔ (K.dAdj (i + 1)).range := by
  apply le_antisymm
  · intro x hx
    have hsup := K.harmonic_sup_ranges i
    have hx' : x ∈ K.harmonic (i + 1) ⊔
        ((K.d i).range ⊔ (K.dAdj (i + 1)).range) := by
      rw [hsup]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    have hxorth : ∀ u ∈ K.harmonic (i + 1), ⟪u, x⟫ = 0 := by
      rw [Submodule.mem_orthogonal] at hx
      exact hx
    have haR : a ∈ ((K.d i).range ⊔ (K.dAdj (i + 1)).range)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_sup] at hu
      obtain ⟨u1, hu1, u2, hu2, rfl⟩ := hu
      have h1 : a ∈ (K.d i).rangeᗮ := K.harmonic_le_orthogonal_range_left i ha
      have h2 : a ∈ (K.dAdj (i + 1)).rangeᗮ :=
        K.harmonic_le_orthogonal_range_right i ha
      rw [Submodule.mem_orthogonal] at h1 h2
      rw [inner_add_left, h1 u1 hu1, h2 u2 hu2, add_zero]
    rw [Submodule.mem_orthogonal] at haR
    have haa : ⟪a, a⟫ = 0 := by
      have h1 : ⟪a, x⟫ = 0 := hxorth a ha
      have h2 : ⟪a, b⟫ = 0 := by
        rw [← inner_conj_symm, haR b hb]
        simp
      have hxab : ⟪a, x⟫ = ⟪a, a + b⟫ := by rw [hab]
      rw [hxab, inner_add_right, h2, add_zero] at h1
      exact h1
    have ha0 : a = 0 := inner_self_eq_zero.mp haa
    rw [← hab, ha0, zero_add]
    exact hb
  · intro x hx
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_sup] at hx
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hx
    have h1 : ⟪u, b1⟫ = 0 := by
      have h := K.harmonic_le_orthogonal_range_left i hu
      rw [Submodule.mem_orthogonal] at h
      rw [← inner_conj_symm, h b1 hb1]
      simp
    have h2 : ⟪u, b2⟫ = 0 := by
      have h := K.harmonic_le_orthogonal_range_right i hu
      rw [Submodule.mem_orthogonal] at h
      rw [← inner_conj_symm, h b2 hb2]
      simp
    rw [inner_add_right, h1, h2, add_zero]

/-- The Hodge decomposition is an orthogonal complement. -/
theorem harmonic_isCompl (i : ℕ) : IsCompl (K.harmonic i) (K.harmonic i)ᗮ :=
  Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

/-- Every cycle decomposes as a harmonic chain plus a boundary:
`ker dᵢ₊₁ = ℋᵢ₊₁ ⊔ Im dᵢ`, at degree `i+1`. -/
theorem cycles_eq_harmonic_sup_range (i : ℕ) :
    (K.d (i + 1)).ker = K.harmonic (i + 1) ⊔ (K.d i).range := by
  have hle : (K.d i).range ≤ (K.d (i + 1)).ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact K.d_comp i z
  have hspan := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (K₁ := (K.d i).range) (K₂ := (K.d (i + 1)).ker) hle
  have hharm : (K.d i).rangeᗮ ⊓ (K.d (i + 1)).ker = K.harmonic (i + 1) := by
    rw [harmonic_eq_inf, upKer_succ, K.ker_dAdj_eq_orthogonal_range i, inf_comm]
  rw [hharm] at hspan
  rw [← hspan, sup_comm]

/-- The Laplacian commutes with the differential: `Δᵢ₊₁ ∘ dᵢ = dᵢ ∘ Δᵢ`. -/
theorem lap_d (i : ℕ) (x : K.C i) :
    K.lap (i + 1) (K.d i x) = K.d i (K.lap i x) := by
  cases i with
  | zero =>
      simp [lap, lapDown, lapUp, K.d_comp]
  | succ j =>
      simp [lap, lapDown, lapUp, K.d_comp]

/-- The Laplacian commutes with the adjoint differential: `Δᵢ ∘ dᵢ† =
dᵢ† ∘ Δᵢ₊₁`. -/
theorem lap_dAdj (i : ℕ) (x : K.C (i + 1)) :
    K.lap i (K.dAdj i x) = K.dAdj i (K.lap (i + 1) x) := by
  cases i with
  | zero =>
      simp [lap, lapDown, lapUp, K.d_comp, dAdj_comp_dAdj_apply]
  | succ j =>
      simp [lap, lapDown, lapUp, K.d_comp, dAdj_comp_dAdj_apply]

/-! ## Khovanov local data: `V = span(1, X)` and merge/comultiplication -/

/-- The paper's two-dimensional space `V = span(𝟙, X)` over `ℂ`, with coordinate
`0` the basis vector `𝟙` and coordinate `1` the basis vector `X`. -/
abbrev KahanevV : Type := Fin 2 → ℂ

/-- The basis vector `𝟙`. -/
def kVone : KahanevV := fun i => if i = (0 : Fin 2) then 1 else 0

/-- The basis vector `X`. -/
def kVx : KahanevV := fun i => if i = (1 : Fin 2) then 1 else 0

/-- Coordinate projection `(Fin 4 → ℂ) → ℂ` at coordinate `i`. -/
def coord4 (i : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

/-- Coordinate projection `(Fin 2 → ℂ) → ℂ` at coordinate `i`. -/
def coord2 (i : Fin 2) : (Fin 2 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

/-- Merge (multiplication) `m : V ⊗ V → V` of Section 8.2.1:
`|11⟩ ↦ |1⟩`, `|1X⟩, |X1⟩ ↦ |X⟩`, `|XX⟩ ↦ 0`.

We model `V ⊗ V` as the four coordinate functions on `Fin 4`, ordered as
`|11⟩, |1X⟩, |X1⟩, |XX⟩`. -/
def kvMerge : (Fin 4 → ℂ) →ₗ[ℂ] KahanevV :=
  LinearMap.pi fun (j : Fin 2) =>
    match j with
    | 0 => coord4 0
    | _ => coord4 1 + coord4 2

/-- Comultiplication `δ : V → V ⊗ V` of Section 8.2.1:
`|1⟩ ↦ |1X⟩ + |X1⟩`, `|X⟩ ↦ |XX⟩`. -/
def kvComult : KahanevV →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.pi fun (j : Fin 4) =>
    match j with
    | 0 => 0
    | 1 => coord2 0
    | 2 => coord2 0
    | _ => coord2 1

/-- The local Laplacian summand `m†m : V ⊗ V → V ⊗ V` in the form used in the
proof of Proposition 19 (eq. (8.2)): on the four basis vectors it is
`|11⟩ ↦ |11⟩`, `|1X⟩ ↦ |1X⟩ + |X1⟩`, `|X1⟩ ↦ |1X⟩ + |X1⟩`, `|XX⟩ ↦ 0`. -/
def kvMergeLap : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.pi fun (j : Fin 4) =>
    match j with
    | 0 => coord4 0
    | 1 => coord4 1 + coord4 2
    | 2 => coord4 1 + coord4 2
    | _ => 0

/-- The local comultiplication summand `d†d : V → V` of eq. (8.2):
`|1⟩ ↦ 2|1⟩`, `|X⟩ ↦ |X⟩`. -/
def kvComultLap : KahanevV →ₗ[ℂ] KahanevV :=
  LinearMap.pi fun (j : Fin 2) =>
    match j with
    | 0 => (2 : ℂ) • coord2 0
    | _ => coord2 1

/-- The value of `m†m` on the all-`1` basis vector is itself (weight `1` loop in
Proposition 19). -/
@[simp]
theorem kvMergeLap_11 : kvMergeLap (fun i => if i = (0 : Fin 4) then 1 else 0) =
    (fun i => if i = (0 : Fin 4) then 1 else 0) := by
  ext j
  fin_cases j <;> simp [kvMergeLap, coord4]

/-- The value of `m†m` on `|1X⟩` is `|1X⟩ + |X1⟩` (the edge part of the graph
`G_{n,k}`). -/
@[simp]
theorem kvMergeLap_1X :
    kvMergeLap (fun i => if i = (1 : Fin 4) then 1 else 0) =
      (fun i => if i = (1 : Fin 4) then 1 else 0) +
        (fun i => if i = (2 : Fin 4) then 1 else 0) := by
  ext j
  fin_cases j <;> simp [kvMergeLap, coord4]

/-- `m†m` kills `|XX⟩`. -/
@[simp]
theorem kvMergeLap_XX :
    kvMergeLap (fun i => if i = (3 : Fin 4) then 1 else 0) = 0 := by
  ext j
  fin_cases j <;> simp [kvMergeLap, coord4]

end CochainComplex

end Qatlib.Papers.KhovanovHom25.MainResults
