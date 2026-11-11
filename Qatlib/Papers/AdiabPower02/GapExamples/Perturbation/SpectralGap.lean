/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral gap bounds from finite-dimensional perturbations

Develops quadratic-form and Rayleigh-quotient estimates for real symmetric operators. A
comparison operator with two orthonormal vectors at its lowest energy gives an upper bound on
the gap between the two smallest eigenvalues.

The operator `erase` removes the coupling between a unit vector and its orthogonal complement.
Rank-two norm estimates control this modification and yield gap bounds in terms of a
perturbation action or a rank-one overlap. See [VanDamMoscaVazirani2001].

## Main statements

* `gap_perturb`: Bounds the lowest spectral gap by twice an operator-norm perturbation bound.
* `norm_sub_erase_le`: Controls the erasure error by the component of `A e` orthogonal to `e`.
* `gap_erase_le_amp`: Bounds the gap for a rank-one perturbation by a scalar overlap.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace BigOperators
open Module

namespace Qatlib

namespace Papers

namespace AdiabPower02

namespace GapExamples

namespace SpectralGap

/-- The real Euclidean space with coordinates indexed by `Fin n`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The real quadratic form `⟪T x, x⟫` of a continuous linear operator. -/
def qform (T : Vec n →L[ℝ] Vec n) (x : Vec n) : ℝ := ⟪T x, x⟫

/-- The quadratic form of `T` at `x` divided by `‖x‖ ^ 2`. -/
def ray (T : Vec n →L[ℝ] Vec n) (x : Vec n) : ℝ := qform T x / ‖x‖ ^ 2

/-- The difference of the quadratic forms of two operators is the quadratic form of their
difference. -/
lemma qform_sub (A B : Vec n →L[ℝ] Vec n) (x : Vec n) :
    qform A x - qform B x = qform (A - B) x := by
  simp [qform, ContinuousLinearMap.sub_apply, inner_sub_left]

/-- The absolute quadratic form is at most the operator norm times the squared vector norm. -/
lemma qform_abs_le (C : Vec n →L[ℝ] Vec n) (x : Vec n) :
    |qform C x| ≤ ‖C‖ * ‖x‖ ^ 2 := by
  have h₁ : |qform C x| ≤ ‖C x‖ * ‖x‖ := by
    simpa [qform] using abs_real_inner_le_norm (C x) x
  have h₂ : ‖C x‖ * ‖x‖ ≤ ‖C‖ * ‖x‖ ^ 2 := by
    have h := ContinuousLinearMap.le_opNorm C x
    have hc : 0 ≤ ‖C‖ := ContinuousLinearMap.opNorm_nonneg C
    nlinarith [norm_nonneg x, norm_nonneg (C x), h, hc, sq_nonneg ‖x‖]
  exact le_trans h₁ h₂

/-- For a nonzero vector, the Rayleigh quotients of two operators differ by at most the norm of
their difference. -/
lemma ray_perturb (A B : Vec n →L[ℝ] Vec n) {x : Vec n} (hx : x ≠ 0) :
    |ray A x - ray B x| ≤ ‖A - B‖ := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hq : ray A x - ray B x = qform (A - B) x / ‖x‖ ^ 2 := by
    rw [ray, ray, ← sub_div, ← qform_sub]
  rw [hq, abs_div, abs_of_pos hx2]
  rw [div_le_iff₀ hx2]
  exact qform_abs_le (A - B) x

section Expansion

variable (T : Vec n →L[ℝ] Vec n) (hT : (T : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
  (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)

/-- The quadratic form of a symmetric operator expands as the sum of its eigenvalues times
squared eigenbasis coordinates. -/
theorem qform_expand (x : Vec n) :
    qform T x = ∑ i, (hT.eigenvalues hn i) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
  have h1 : qform T x = ∑ i, ⟪T x, hT.eigenvectorBasis hn i⟫ * ⟪hT.eigenvectorBasis hn i, x⟫ := by
    rw [qform]
    exact (OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hn) (T x) x).symm
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : ⟪T x, hT.eigenvectorBasis hn i⟫ = (hT.eigenvalues hn i) * ⟪hT.eigenvectorBasis hn i, x⟫ := by
    rw [hT.apply_clm]
    change ⟪x, (T : Vec n →ₗ[ℝ] Vec n) (hT.eigenvectorBasis hn i)⟫ = _
    rw [LinearMap.IsSymmetric.apply_eigenvectorBasis]
    rw [inner_smul_right, real_inner_comm]
    norm_cast
  rw [h2]; ring

/-- The squared norm of a vector is the sum of its squared coordinates in the orthonormal
eigenvector basis. -/
theorem norm_sq_expand (x : Vec n) :
    ‖x‖ ^ 2 = ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
  have h := OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hn) x x
  rw [real_inner_self_eq_norm_sq] at h
  calc ‖x‖ ^ 2 = ∑ i, ⟪x, hT.eigenvectorBasis hn i⟫ * ⟪hT.eigenvectorBasis hn i, x⟫ := h.symm
    _ = ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm x, sq]

/-- The smallest eigenvalue of a symmetric operator is at most its Rayleigh quotient at any
nonzero vector. -/
theorem last_le_ray {x : Vec n} (hx : x ≠ 0) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ ≤ ray T x := by
  have hanti := hT.eigenvalues_antitone hn
  have hx2 : 0 < ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
    rw [← norm_sq_expand T hT hn]; positivity
  have hsum : (∑ i, (hT.eigenvalues hn ⟨n - 1, by omega⟩) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2)
      ≤ ∑ i, (hT.eigenvalues hn i) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hle : hT.eigenvalues hn ⟨n - 1, by omega⟩ ≤ hT.eigenvalues hn i :=
      hanti (by
        show i ≤ (⟨n - 1, by omega⟩ : Fin n)
        show i.val ≤ n - 1
        have := i.isLt; omega)
    have : (0:ℝ) ≤ (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := sq_nonneg _
    nlinarith
  rw [ray, qform_expand T hT hn, norm_sq_expand T hT hn, le_div_iff₀ hx2]
  calc (hT.eigenvalues hn ⟨n - 1, by omega⟩) * ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      = ∑ i, (hT.eigenvalues hn ⟨n - 1, by omega⟩) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := hsum

/-- On nonzero vectors orthogonal to the chosen lowest eigenvector, the Rayleigh quotient is at
least the second-smallest eigenvalue. -/
theorem second_le_ray {x : Vec n} (hx : x ≠ 0)
    (horth : ⟪hT.eigenvectorBasis hn ⟨n - 1, by omega⟩, x⟫ = 0) :
    hT.eigenvalues hn ⟨n - 2, by omega⟩ ≤ ray T x := by
  have hanti := hT.eigenvalues_antitone hn
  have hx2 : 0 < ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
    rw [← norm_sq_expand T hT hn]; positivity
  have hsum : (∑ i, (hT.eigenvalues hn ⟨n - 2, by omega⟩) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2)
      ≤ ∑ i, (hT.eigenvalues hn i) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = ⟨n - 1, by omega⟩
    · subst hi
      rw [horth]
      simp
    · have hlt : i ≤ (⟨n - 2, by omega⟩ : Fin n) := by
        show i.val ≤ n - 2
        have := i.isLt
        have hne : i.val ≠ n - 1 := by
          intro h
          exact hi (Fin.ext h)
        omega
      have hle : hT.eigenvalues hn ⟨n - 2, by omega⟩ ≤ hT.eigenvalues hn i := hanti hlt
      have : (0:ℝ) ≤ (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := sq_nonneg _
      nlinarith
  rw [ray, qform_expand T hT hn, norm_sq_expand T hT hn, le_div_iff₀ hx2]
  calc (hT.eigenvalues hn ⟨n - 2, by omega⟩) * ∑ i, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      = ∑ i, (hT.eigenvalues hn ⟨n - 2, by omega⟩) * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := hsum

end Expansion

open SpectralGap
variable {n : ℕ}

section More

variable (T : Vec n →L[ℝ] Vec n) (hT : (T : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
  (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)

/-- The Rayleigh quotient of an eigenbasis vector equals its corresponding eigenvalue. -/
theorem ray_eigenvector (i : Fin n) :
    ray T (hT.eigenvectorBasis hn i) = hT.eigenvalues hn i := by
  have hnorm : ‖hT.eigenvectorBasis hn i‖ = 1 := by simp
  have hd : ‖hT.eigenvectorBasis hn i‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  rw [ray, qform, hd, div_one]
  change ⟪(T : Vec n →ₗ[ℝ] Vec n) (hT.eigenvectorBasis hn i), hT.eigenvectorBasis hn i⟫
      = hT.eigenvalues hn i
  rw [LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_left]
  rw [show (inner ℝ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i)) = 1 from by simp]
  simp

/-- On the span of two vectors with common eigenvalue `μ`, the quadratic form equals `μ` times
the squared norm. -/
theorem qform_span_eq (B : Vec n →L[ℝ] Vec n) {μ : ℝ} {u w x : Vec n}
    (huB : B u = μ • u) (hwB : B w = μ • w)
    (hx : x ∈ Submodule.span ℝ ({u, w} : Set (Vec n))) :
    qform B x = μ * ‖x‖ ^ 2 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  have hBx : B (a • u + b • w) = μ • (a • u + b • w) := by
    rw [map_add, map_smul, map_smul, huB, hwB]
    simp [smul_add, smul_smul, mul_comm μ]
  rw [qform, hBx, inner_smul_left, real_inner_self_eq_norm_sq]
  norm_cast

/-- Every nonzero vector in the span of two eigenvectors with common eigenvalue `μ` has Rayleigh
quotient `μ`. -/
theorem ray_span_eq (B : Vec n →L[ℝ] Vec n) {μ : ℝ} {u w x : Vec n}
    (huB : B u = μ • u) (hwB : B w = μ • w)
    (hx : x ∈ Submodule.span ℝ ({u, w} : Set (Vec n))) (hx0 : x ≠ 0) :
    ray B x = μ := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  rw [ray, qform_span_eq B huB hwB hx]
  exact mul_div_cancel_right₀ μ hx2.ne'

end More

variable {n : ℕ}

/-- A quadratic-form lower bound `μ * ‖x‖ ^ 2 ≤ qform B x` gives the Rayleigh-quotient lower
bound `μ` on nonzero vectors. -/
theorem ray_ge_of_lower (B : Vec n →L[ℝ] Vec n) {μ : ℝ}
    (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform B x) {x : Vec n} (hx : x ≠ 0) :
    μ ≤ ray B x := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  rw [ray, le_div_iff₀ hx2]
  simpa [mul_comm] using hμ x

section TwoDim

variable (T : Vec n →L[ℝ] Vec n) (hT : (T : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
  (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)

/-- If the Rayleigh quotient is at most `c` on the nonzero vectors of a span of two nonzero
orthogonal vectors, the second-smallest eigenvalue is at most `c`. -/
theorem second_le_of_twoDim (c : ℝ) {p q : Vec n}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : ⟪p, q⟫ = 0)
    (hbound : ∀ x : Vec n, x ∈ Submodule.span ℝ ({p, q} : Set (Vec n)) → x ≠ 0 →
      ray T x ≤ c) :
    hT.eigenvalues hn ⟨n - 2, by omega⟩ ≤ c := by
  have hind : ∀ α β : ℝ, α • p + β • q = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hp2 : 0 < ‖p‖ ^ 2 := by positivity
    have hinner := congrArg (fun v => ⟪p, v⟫) h
    change ⟪p, α • p + β • q⟫ = ⟪p, (0 : Vec n)⟫ at hinner
    rw [inner_add_right, inner_smul_right, inner_smul_right, hpq, inner_zero_right,
      real_inner_self_eq_norm_sq] at hinner
    have h1 : α * ‖p‖ ^ 2 = 0 := by linarith
    have hα : α = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hp2.ne'
    subst hα
    have h2 : β • q = 0 := by simpa using h
    exact ⟨rfl, Or.resolve_right (smul_eq_zero.mp h2) hq⟩
  set el : Vec n := hT.eigenvectorBasis hn ⟨n - 1, by omega⟩ with hel
  by_cases hzero : ⟪el, q⟫ • p - ⟪el, p⟫ • q = 0
  · have hind' := hind ⟪el, q⟫ (-⟪el, p⟫) (by simpa [sub_eq_add_neg] using hzero)
    have hp0 : ⟪el, p⟫ = 0 := by linarith [hind'.2]
    have hself : ray T p ≤ c := hbound p (Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩) hp
    exact le_trans (second_le_ray T hT hn hn2 hp hp0) hself
  · have hmem : ⟪el, q⟫ • p - ⟪el, p⟫ • q ∈ Submodule.span ℝ ({p, q} : Set (Vec n)) :=
      Submodule.mem_span_pair.mpr ⟨⟪el, q⟫, -⟪el, p⟫, by simp [sub_eq_add_neg]⟩
    have horth : ⟪el, ⟪el, q⟫ • p - ⟪el, p⟫ • q⟫ = 0 := by
      rw [inner_sub_right, inner_smul_right, inner_smul_right]
      ring
    exact le_trans (second_le_ray T hT hn hn2 hzero horth) (hbound _ hmem hzero)

end TwoDim

section Main

open SpectralGap

variable (A B : Vec n →L[ℝ] Vec n) (hA : (A : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
  (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)

/-- If `B` has quadratic-form lower bound `μ` and two orthonormal eigenvectors of eigenvalue
`μ`, and `‖A - B‖ ≤ δ`, the gap between the two smallest eigenvalues of symmetric `A` is at
most `2 * δ` [VanDamMoscaVazirani2001]. -/
theorem gap_perturb (μ δ : ℝ) (hδ : ‖A - B‖ ≤ δ)
    (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform B x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : B u = μ • u) (hwB : B w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩ ≤ 2 * δ := by
  have hel_ne : hA.eigenvectorBasis hn ⟨n - 1, by omega⟩ ≠ 0 := by
    intro h
    have := (hA.eigenvectorBasis hn).orthonormal.1 ⟨n - 1, by omega⟩
    rw [h] at this
    norm_num at this
  have hlow : μ - δ ≤ hA.eigenvalues hn ⟨n - 1, by omega⟩ := by
    have heq : hA.eigenvalues hn ⟨n - 1, by omega⟩
        = ray A (hA.eigenvectorBasis hn ⟨n - 1, by omega⟩) :=
      (ray_eigenvector A hA hn _).symm
    rw [heq]
    have h1 : μ ≤ ray B (hA.eigenvectorBasis hn ⟨n - 1, by omega⟩) :=
      ray_ge_of_lower B hμ hel_ne
    have h2 : ray B (hA.eigenvectorBasis hn ⟨n - 1, by omega⟩) - δ
        ≤ ray A (hA.eigenvectorBasis hn ⟨n - 1, by omega⟩) := by
      have h3 := abs_le.mp (ray_perturb A B hel_ne)
      linarith [h3.1, hδ]
    linarith
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  have hhigh : hA.eigenvalues hn ⟨n - 2, by omega⟩ ≤ μ + δ := by
    refine second_le_of_twoDim A hA hn hn2 (μ + δ) (p := u) (q := w) hu0 hw0 huw ?_
    intro x hxmem hx0
    have hxB : ray B x = μ := ray_span_eq B huB hwB hxmem hx0
    have h3 := abs_le.mp (ray_perturb A B hx0)
    linarith [h3.2, hδ]
  linarith

end Main

section Erasure

variable {n : ℕ}

/-- The rank-one continuous linear operator `x ↦ ⟪e, x⟫ • e`. -/
def proj (e : Vec n) : Vec n →L[ℝ] Vec n :=
  ContinuousLinearMap.smulRight (innerSL ℝ e) e

/-- The rank-one operator sends `x` to `⟪e, x⟫ • e`. -/
lemma proj_apply (e x : Vec n) : proj e x = ⟪e, x⟫ • e := by
  simp [proj, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- The rank-one operator associated with a unit vector fixes that vector. -/
lemma proj_self (e : Vec n) (he : ‖e‖ = 1) : proj e e = e := by
  rw [proj_apply, real_inner_self_eq_norm_sq, he]
  norm_num

/-- The rank-one operator vanishes on vectors orthogonal to its defining vector. -/
lemma proj_orth {e x : Vec n} (h : ⟪e, x⟫ = 0) : proj e x = 0 := by
  rw [proj_apply, h, zero_smul]

/-- The operator `A - A ∘ proj e - proj e ∘ A + (2 * ⟪e, A e⟫) • proj e`, which decouples `e`
when `e` is a unit vector. -/
def erase (A : Vec n →L[ℝ] Vec n) (e : Vec n) : Vec n →L[ℝ] Vec n :=
  A - A.comp (proj e) - (proj e).comp A + (2 * ⟪e, A e⟫) • proj e

/-- The action of `erase A e` expands into `A x` and the three explicit rank-one correction
terms. -/
lemma erase_apply (A : Vec n →L[ℝ] Vec n) (e x : Vec n) :
    erase A e x = A x - ⟪e, x⟫ • A e - ⟪e, A x⟫ • e
      + (2 * ⟪e, A e⟫) • (⟪e, x⟫ • e) := by
  simp only [erase, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, proj_apply,
    ContinuousLinearMap.map_smul]

/-- For a unit vector `e`, the erased operator sends `e` to `⟪e, A e⟫ • e`. -/
lemma erase_self (A : Vec n →L[ℝ] Vec n) (e : Vec n) (he : ‖e‖ = 1) :
    erase A e e = ⟪e, A e⟫ • e := by
  rw [erase_apply, real_inner_self_eq_norm_sq, he]
  module

/-- On a vector orthogonal to `e`, erasure subtracts the component `⟪e, A x⟫ • e` from `A x`. -/
lemma erase_of_orth (A : Vec n →L[ℝ] Vec n) {e x : Vec n} (h : ⟪e, x⟫ = 0) :
    erase A e x = A x - ⟪e, A x⟫ • e := by
  rw [erase_apply, h]
  simp

/-- For symmetric `A`, the erasure difference is the sum of the two rank-one couplings between
`e` and `A e - ⟪e, A e⟫ • e`. -/
lemma sub_erase_apply (A : Vec n →L[ℝ] Vec n)
    (hA : (A : Vec n →ₗ[ℝ] Vec n).IsSymmetric) (e x : Vec n) :
    (A - erase A e) x
      = ⟪e, x⟫ • (A e - ⟪e, A e⟫ • e) + ⟪A e - ⟪e, A e⟫ • e, x⟫ • e := by
  rw [ContinuousLinearMap.sub_apply, erase_apply, (hA.apply_clm e x).symm,
    inner_sub_left, real_inner_smul_left]
  module

/-- If a unit vector `e` is orthogonal to `u`, the operator `x ↦ ⟪e, x⟫ • u + ⟪u, x⟫ • e` has
norm at most `‖u‖`. -/
theorem norm_le_of_rankTwo {M : Vec n →L[ℝ] Vec n} {e u : Vec n}
    (he : ‖e‖ = 1) (hu : ⟪e, u⟫ = 0)
    (hM : ∀ x : Vec n, M x = ⟪e, x⟫ • u + ⟪u, x⟫ • e) :
    ‖M‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  set a : ℝ := ⟪e, x⟫ with ha
  set y : Vec n := x - a • e with hy
  have hxdecomp : x = a • e + y := by
    rw [hy]; abel
  have hyorth : ⟪e, y⟫ = 0 := by
    rw [hy, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    simp [ha]
  have hue : ⟪u, e⟫ = 0 := by
    rw [real_inner_comm]; exact hu
  have hux : ⟪u, x⟫ = ⟪u, y⟫ := by
    rw [hxdecomp, inner_add_right, real_inner_smul_right, hue, mul_zero, zero_add]
  have hxy : ⟪a • e, y⟫ = 0 := by
    rw [real_inner_smul_left, hyorth, mul_zero]
  have hdecomp2 : ‖x‖ ^ 2 = a ^ 2 + ‖y‖ ^ 2 := by
    rw [hxdecomp, norm_add_sq_real, hxy]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
    ring
  have hux' : ⟪u, x⟫ = ⟪u, y⟫ := hux
  have hMx : M x = a • u + ⟪u, y⟫ • e := by
    rw [hM x, hux']
  have h3 : a ^ 2 ≤ ‖x‖ ^ 2 := by
    have hb := abs_real_inner_le_norm e x
    rw [he, one_mul] at hb
    have h2 : |a| ^ 2 ≤ ‖x‖ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg a) hb 2
      simpa using this
    simpa [sq_abs] using h2
  have h4 : ⟪u, y⟫ ^ 2 ≤ ‖u‖ ^ 2 * ‖y‖ ^ 2 := by
    have hb := abs_real_inner_le_norm u y
    have h2 : |⟪u, y⟫| ^ 2 ≤ (‖u‖ * ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc ⟪u, y⟫ ^ 2 = |⟪u, y⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖u‖ * ‖y‖) ^ 2 := h2
      _ = ‖u‖ ^ 2 * ‖y‖ ^ 2 := mul_pow _ _ _
  have hsq : ‖a • u + ⟪u, y⟫ • e‖ ^ 2 ≤ (‖u‖ * ‖x‖) ^ 2 := by
    rw [norm_add_sq_real]
    have horth : ⟪a • u, ⟪u, y⟫ • e⟫ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, hue]
      ring
    rw [horth]
    simp only [mul_zero, add_zero]
    have h1 : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h2 : ‖⟪u, y⟫ • e‖ ^ 2 = ⟪u, y⟫ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
      ring
    rw [h1, h2]
    have hu2 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    nlinarith [h3, h4, hdecomp2, hu2]
  rw [hMx]
  have habs : |‖a • u + ⟪u, y⟫ • e‖| ≤ |‖u‖ * ‖x‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    at habs

/-- For symmetric `A` and unit `e`, the erasure error is at most the norm of `A e - ⟪e, A e⟫ •
e`. -/
theorem norm_sub_erase_le (A : Vec n →L[ℝ] Vec n)
    (hA : (A : Vec n →ₗ[ℝ] Vec n).IsSymmetric) (e : Vec n) (he : ‖e‖ = 1) :
    ‖A - erase A e‖ ≤ ‖A e - ⟪e, A e⟫ • e‖ := by
  refine norm_le_of_rankTwo he ?_ ?_
  · rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  · intro x
    exact sub_erase_apply A hA e x

/-- For symmetric `A` and unit `e`, the erasure error is at most `sqrt 2` times the norm of `A e
- ⟪e, A e⟫ • e` [VanDamMoscaVazirani2001]. -/
theorem norm_sub_erase_le_sqrt_two (A : Vec n →L[ℝ] Vec n)
    (hA : (A : Vec n →ₗ[ℝ] Vec n).IsSymmetric) (e : Vec n) (he : ‖e‖ = 1) :
    ‖A - erase A e‖ ≤ Real.sqrt 2 * ‖A e - ⟪e, A e⟫ • e‖ := by
  refine le_trans (norm_sub_erase_le A hA e he) ?_
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (A e - ⟪e, A e⟫ • e))
  simpa using h2

end Erasure

section Perturbed

variable {n : ℕ}

/-- The rank-one operator `proj v` is symmetric. -/
lemma proj_symm (v : Vec n) : (proj v : Vec n →ₗ[ℝ] Vec n).IsSymmetric := by
  intro x y
  rw [show (proj v : Vec n →ₗ[ℝ] Vec n) x = ⟪v, x⟫ • v from proj_apply v x,
    show (proj v : Vec n →ₗ[ℝ] Vec n) y = ⟪v, y⟫ • v from proj_apply v y,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm x v]
  ring

/-- Removing the component along a unit vector does not increase a vector's norm. -/
lemma norm_sub_inner_smul_le (e v : Vec n) (he : ‖e‖ = 1) :
    ‖v - ⟪e, v⟫ • e‖ ≤ ‖v‖ := by
  have hsq : ‖v - ⟪e, v⟫ • e‖ ^ 2 = ‖v‖ ^ 2 - ⟪e, v⟫ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm v e]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
    ring
  have h2 : ‖v - ⟪e, v⟫ • e‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ⟪e, v⟫]
  have habs : |‖v - ⟪e, v⟫ • e‖| ≤ |‖v‖| := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

/-- If symmetric `D` annihilates unit `e` and `v` is unit, the erasure error of `D - α • proj v`
is at most `|α * ⟪v, e⟫|`. -/
theorem norm_sub_erase_le_amp
    (D : Vec n →L[ℝ] Vec n) (hD : (D : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (e v : Vec n) (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hDe : D e = 0) (α : ℝ) :
    ‖(D - α • proj v) - erase (D - α • proj v) e‖ ≤ |α * ⟪v, e⟫| := by
  have hA : ((D - α • proj v : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric := by
    simpa using hD.sub ((proj_symm v).smul (c := α) (by simp))
  have hbound := norm_sub_erase_le (D - α • proj v) hA e he
  have hAe : (D - α • proj v) e = (-(α * ⟪v, e⟫)) • v := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, hDe, proj_apply]
    module
  have hc : ⟪e, (D - α • proj v) e⟫ = -(α * ⟪v, e⟫ ^ 2) := by
    rw [hAe, real_inner_smul_right, real_inner_comm e v]
    ring
  have hdiff : (D - α • proj v) e - ⟪e, (D - α • proj v) e⟫ • e
      = (-(α * ⟪v, e⟫)) • (v - ⟪e, v⟫ • e) := by
    rw [hAe, real_inner_smul_right, real_inner_comm e v]
    module
  refine le_trans hbound ?_
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg]
  have hle : ‖v - ⟪e, v⟫ • e‖ ≤ 1 := le_trans (norm_sub_inner_smul_le e v he) (le_of_eq hv)
  have hnonneg : 0 ≤ |α * ⟪v, e⟫| := abs_nonneg _
  calc |α * ⟪v, e⟫| * ‖v - ⟪e, v⟫ • e‖ ≤ |α * ⟪v, e⟫| * 1 :=
        mul_le_mul_of_nonneg_left hle hnonneg
    _ = |α * ⟪v, e⟫| := mul_one _

end Perturbed

section EqSix

variable {n : ℕ}

/-- If `D` annihilates unit `e` and `D + P` is symmetric, its erasure error is at most `‖P e‖`
[VanDamMoscaVazirani2001]. -/
theorem norm_sub_erase_le_pert (D P : Vec n →L[ℝ] Vec n)
    (hA : ((D + P : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (e : Vec n) (he : ‖e‖ = 1) (hDe : D e = 0) :
    ‖(D + P) - erase (D + P) e‖ ≤ ‖P e‖ := by
  refine le_trans (norm_sub_erase_le (D + P) hA e he) ?_
  have hAe : (D + P) e = P e := by
    rw [ContinuousLinearMap.add_apply, hDe, zero_add]
  rw [hAe]
  exact norm_sub_inner_smul_le e (P e) he

/-- If the erased operator has a quadratic-form lower bound attained by two orthonormal
eigenvectors, the lowest gap of symmetric `D + P` is at most `2 * ‖P e‖`, provided `D e = 0`
and `e` is unit [VanDamMoscaVazirani2001]. -/
theorem gap_erase_le (D P : Vec n →L[ℝ] Vec n)
    (hA : ((D + P : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)
    (e : Vec n) (he : ‖e‖ = 1) (hDe : D e = 0)
    (μ : ℝ) (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform (erase (D + P) e) x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : erase (D + P) e u = μ • u) (hwB : erase (D + P) e w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩ ≤ 2 * ‖P e‖ := by
  have hδ : ‖(D + P) - erase (D + P) e‖ ≤ ‖P e‖ := norm_sub_erase_le_pert D P hA e he hDe
  exact le_trans (gap_perturb (D + P) (erase (D + P) e) hA hn hn2 μ ‖P e‖ hδ hμ u w hu hw huw huB hwB)
    (by linarith [norm_nonneg (P e)])

/-- Under the stated erasure and degeneracy hypotheses, the lowest gap of `D + P` is at most `2
* (sqrt 2 * ‖P e‖)`. -/
theorem gap_erase_le_sqrt_two (D P : Vec n →L[ℝ] Vec n)
    (hA : ((D + P : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)
    (e : Vec n) (he : ‖e‖ = 1) (hDe : D e = 0)
    (μ : ℝ) (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform (erase (D + P) e) x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : erase (D + P) e u = μ • u) (hwB : erase (D + P) e w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩
      ≤ 2 * (Real.sqrt 2 * ‖P e‖) := by
  have h2 : ‖(D + P) e - ⟪e, (D + P) e⟫ • e‖ ≤ ‖P e‖ := by
    have hAe : (D + P) e = P e := by
      rw [ContinuousLinearMap.add_apply, hDe, zero_add]
    rw [hAe]
    exact norm_sub_inner_smul_le e (P e) he
  have h1 : ‖(D + P) - erase (D + P) e‖ ≤ Real.sqrt 2 * ‖P e‖ := by
    refine le_trans (norm_sub_erase_le_sqrt_two (D + P) hA e he) ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact gap_perturb (D + P) (erase (D + P) e) hA hn hn2 μ (Real.sqrt 2 * ‖P e‖) h1 hμ
    u w hu hw huw huB hwB

/-- Under the stated erasure and degeneracy hypotheses, a bound `‖P e‖ ≤ c` gives a lowest
spectral gap of at most `2 * c` for `D + P` [VanDamMoscaVazirani2001]. -/
theorem gap_erase_le_of_bound (D P : Vec n →L[ℝ] Vec n)
    (hA : ((D + P : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)
    (e : Vec n) (he : ‖e‖ = 1) (hDe : D e = 0)
    {c : ℝ} (hc : ‖P e‖ ≤ c)
    (μ : ℝ) (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform (erase (D + P) e) x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : erase (D + P) e u = μ • u) (hwB : erase (D + P) e w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩ ≤ 2 * c := by
  refine le_trans (gap_erase_le D P hA hn hn2 e he hDe μ hμ u w hu hw huw huB hwB) ?_
  linarith

/-- If the erased operator has a quadratic-form lower bound attained by two orthonormal
eigenvectors, the lowest gap of symmetric `A` is at most twice `‖A e - ⟪e, A e⟫ • e‖` for
unit `e`. -/
theorem gap_erase_self (A : Vec n →L[ℝ] Vec n)
    (hA : (A : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)
    (e : Vec n) (he : ‖e‖ = 1)
    (μ : ℝ) (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform (erase A e) x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : erase A e u = μ • u) (hwB : erase A e w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩
      ≤ 2 * ‖A e - ⟪e, A e⟫ • e‖ := by
  have hδ : ‖A - erase A e‖ ≤ ‖A e - ⟪e, A e⟫ • e‖ := norm_sub_erase_le A hA e he
  exact gap_perturb A (erase A e) hA hn hn2 μ ‖A e - ⟪e, A e⟫ • e‖ hδ hμ
    u w hu hw huw huB hwB

/-- For a rank-one perturbation `D - α • proj v`, the stated unit-vector, kernel, and
erased-ground-space hypotheses bound the lowest spectral gap by `2 * |α * ⟪v, e⟫|`
[VanDamMoscaVazirani2001]. -/
theorem gap_erase_le_amp (D : Vec n →L[ℝ] Vec n)
    (e v : Vec n) (α : ℝ)
    (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hDe : D e = 0)
    (hD : (D : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (hn : Module.finrank ℝ (Vec n) = n) (hn2 : 2 ≤ n)
    (hA : ((D - α • proj v : Vec n →L[ℝ] Vec n) : Vec n →ₗ[ℝ] Vec n).IsSymmetric)
    (μ : ℝ) (hμ : ∀ x : Vec n, μ * ‖x‖ ^ 2 ≤ qform (erase (D - α • proj v) e) x)
    (u w : Vec n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0)
    (huB : erase (D - α • proj v) e u = μ • u)
    (hwB : erase (D - α • proj v) e w = μ • w) :
    hA.eigenvalues hn ⟨n - 2, by omega⟩ - hA.eigenvalues hn ⟨n - 1, by omega⟩
      ≤ 2 * |α * ⟪v, e⟫| := by
  have hδ : ‖(D - α • proj v) - erase (D - α • proj v) e‖ ≤ |α * ⟪v, e⟫| :=
    norm_sub_erase_le_amp D hD e v he hv hDe α
  exact gap_perturb (D - α • proj v) (erase (D - α • proj v) e) hA hn hn2 μ
    |α * ⟪v, e⟫| hδ hμ u w hu hw huw huB hwB

end EqSix

end SpectralGap

end GapExamples

end AdiabPower02

end Papers

end Qatlib
