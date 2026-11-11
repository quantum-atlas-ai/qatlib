/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Data.Complex.Basic

/-!
# Unitary spectral tools for the hypercube search analysis

Finite-dimensional complex linear isometries possess orthonormal eigenvector bases with
unit-modulus eigenvalues. This module proves weighted spectral formulas and overlap bounds,
including a bound of two on the number of eigenvalues above a real-part threshold when the
common orthogonal complement of two trial vectors satisfies the corresponding expectation bound.

These tools support the spectral analysis of the search walk in [ShenviKempeWhaley2003].

## Main statements

* `exists_orthonormalBasis_eigenvector`: constructs an orthonormal eigenbasis.
* `spectral_support_lower`: extracts a distinguished spectral overlap from an expectation lower
  bound.
* `card_large_eigen_le_two`: bounds the number of eigenbasis entries above a real-part
  threshold.

## References

* [Shenvi et al., 2003][ShenviKempeWhaley2003]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkSearch02.MainResults

open scoped ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A linear isometry equivalence of a positive-dimensional complex inner product space has a
unit eigenvector with a unit-modulus eigenvalue. -/
theorem exists_unit_eigenvector (U : E ≃ₗᵢ[ℂ] E) (h : 0 < Module.finrank ℂ E) :
    ∃ (v : E) (μ : ℂ), ‖v‖ = 1 ∧ U v = μ • v ∧ ‖μ‖ = 1 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos h
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (U : E →ₗ[ℂ] E)
  obtain ⟨v, hvmem, hvne⟩ := hμ.exists_hasEigenvector
  have hveq : U v = μ • v := by
    have h := Module.End.HasEigenvector.apply_eq_smul (f := (U : E →ₗ[ℂ] E)) ⟨hvmem, hvne⟩
    simpa using h
  have hvpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hvne
  refine ⟨((((‖v‖)⁻¹ : ℝ)) : ℂ) • v, μ, ?_, ?_, ?_⟩
  · have h1 : ‖(((‖v‖)⁻¹ : ℝ) : ℂ)‖ = (‖v‖)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
    rw [norm_smul, h1, inv_mul_cancel₀ (ne_of_gt hvpos)]
  · rw [map_smul, hveq, smul_comm]
  · set c : ℂ := (((‖v‖)⁻¹ : ℝ) : ℂ) with hc
    have h1 : ‖c‖ = (‖v‖)⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
    have hiso : ‖U (c • v)‖ = ‖c • v‖ := U.norm_map _
    rw [map_smul, hveq, norm_smul, norm_smul, h1] at hiso
    have hvpos' : ‖v‖ ≠ 0 := ne_of_gt hvpos
    rw [norm_smul, h1, inv_mul_cancel₀ hvpos'] at hiso
    rw [show ‖v‖⁻¹ * (‖μ‖ * ‖v‖) = ‖μ‖ * (‖v‖⁻¹ * ‖v‖) by ring,
      inv_mul_cancel₀ hvpos', mul_one] at hiso
    exact hiso

omit [FiniteDimensional ℂ E] in

/-- A linear isometry equivalence preserves the orthogonal complement of an eigenvector whose
eigenvalue has modulus one. -/
lemma maps_orthogonal_eigenvector (U : E ≃ₗᵢ[ℂ] E) {v : E} {μ : ℂ} (hμ : ‖μ‖ = 1)
    (hv : U v = μ • v) {w : E} (hw : ⟪v, w⟫_ℂ = 0) : ⟪v, U w⟫_ℂ = 0 := by
  have hμ0 : μ ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hμ; exact zero_ne_one hμ
  have hinner : ⟪v, U w⟫_ℂ = ⟪U.symm v, w⟫_ℂ := by
    conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply U v]
    rw [LinearIsometryEquiv.inner_map_map]
  have hsymm : U.symm v = μ⁻¹ • v := by
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, hv, smul_smul,
      inv_mul_cancel₀ hμ0, one_smul]
  rw [hinner, hsymm, inner_smul_left, hw, mul_zero]

/-- A linear isometry equivalence on a complex inner product space of dimension `n` has an
orthonormal eigenbasis indexed by `Fin n`, with unit-modulus eigenvalues. See
[ShenviKempeWhaley2003]. -/
theorem exists_orthonormalBasis_eigenvector (n : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      (U : E ≃ₗᵢ[ℂ] E), Module.finrank ℂ E = n →
      ∃ (b : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℂ),
        (∀ i, U (b i) = μ i • b i) ∧ (∀ i, ‖μ i‖ = 1) := by
  induction n with
  | zero =>
    intro E _ _ _ U hn
    refine ⟨(stdOrthonormalBasis ℂ E).reindex (finCongr hn), fun _ => 0, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ n ih =>
    intro E _ _ _ U hn
    haveI : Fact (Module.finrank ℂ E = n + 1) := ⟨hn⟩
    have hpos : 0 < Module.finrank ℂ E := by rw [hn]; exact Nat.succ_pos n
    obtain ⟨v, μ0, hvnorm, hvU, hμnorm⟩ := exists_unit_eigenvector U hpos
    have hvne : v ≠ 0 := by
      intro hc; rw [hc, norm_zero] at hvnorm; exact zero_ne_one hvnorm
    have hWfin : Module.finrank ℂ ((ℂ ∙ v)ᗮ : Submodule ℂ E) = n :=
      Submodule.finrank_orthogonal_span_singleton hvne
    have hpres : ∀ x ∈ ((ℂ ∙ v)ᗮ : Submodule ℂ E), U x ∈ ((ℂ ∙ v)ᗮ : Submodule ℂ E) := by
      intro x hx
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
      exact maps_orthogonal_eigenvector U hμnorm hvU hx
    set fr : ((ℂ ∙ v)ᗮ : Submodule ℂ E) →ₗ[ℂ] ((ℂ ∙ v)ᗮ : Submodule ℂ E) :=
      LinearMap.restrict (U : E →ₗ[ℂ] E) hpres with hfr
    have hfr_apply : ∀ x : ((ℂ ∙ v)ᗮ : Submodule ℂ E), (fr x : E) = U (x : E) := by
      intro x; rfl
    have hf_inj : Function.Injective fr := by
      intro a b hab
      apply Subtype.ext
      have h : (fr a : E) = (fr b : E) := congrArg Subtype.val hab
      rw [hfr_apply, hfr_apply] at h
      exact U.injective h
    have hf_norm : ∀ x : ((ℂ ∙ v)ᗮ : Submodule ℂ E), ‖fr x‖ = ‖x‖ := by
      intro x
      exact U.norm_map (x : E)
    have hf_surj : Function.Surjective fr := LinearMap.injective_iff_surjective.mp hf_inj
    let UW : ((ℂ ∙ v)ᗮ : Submodule ℂ E) ≃ₗᵢ[ℂ] ((ℂ ∙ v)ᗮ : Submodule ℂ E) :=
      LinearIsometryEquiv.ofSurjective (LinearIsometry.mk fr hf_norm) hf_surj
    have hUW_apply : ∀ x : ((ℂ ∙ v)ᗮ : Submodule ℂ E), (UW x : E) = U (x : E) := by
      intro x; exact hfr_apply x
    obtain ⟨bW, μW, hbW, hμW⟩ := ih ((ℂ ∙ v)ᗮ : Submodule ℂ E) UW hWfin
    set vf : Fin (n + 1) → E := Matrix.vecCons v (fun i => ((bW i : ((ℂ ∙ v)ᗮ : Submodule ℂ E)) : E)) with hvf
    have hon : Orthonormal ℂ vf := by
      rw [hvf, orthonormal_vecCons_iff]
      refine ⟨hvnorm, ?_, bW.orthonormal⟩
      intro i
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (bW i).2)
    have hcard : Fintype.card (Fin (n + 1)) = Module.finrank ℂ E := by simp [hn]
    haveI : Nonempty (Fin (n + 1)) := ⟨0⟩
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range vf) := by
      have h := (basisOfOrthonormalOfCardEqFinrank hon hcard).span_eq
      have hcoe : (⇑(basisOfOrthonormalOfCardEqFinrank hon hcard) : Fin (n + 1) → E) = vf :=
        coe_basisOfOrthonormalOfCardEqFinrank hon hcard
      rw [← hcoe, h]
    refine ⟨OrthonormalBasis.mk hon hsp, Matrix.vecCons μ0 μW, ?_, ?_⟩
    · intro i
      rw [show (OrthonormalBasis.mk hon hsp : Fin (n + 1) → E) = vf from
        OrthonormalBasis.coe_mk hon hsp]
      refine Fin.cases ?_ ?_ i
      · rw [hvf, Matrix.cons_val_zero, Matrix.cons_val_zero]
        exact hvU
      · intro j
        rw [hvf, Matrix.cons_val_succ, Matrix.cons_val_succ, ← hUW_apply (bW j), hbW j]
        rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hμnorm
      · intro j
        simpa using hμW j

omit [FiniteDimensional ℂ E] in

/-- In an orthonormal eigenbasis, the real part of `⟪ψ, U ψ⟫` is the sum of eigenvalue real
parts weighted by squared overlaps with `ψ`. See [ShenviKempeWhaley2003]. -/
theorem re_inner_apply_eq_sum {n : ℕ} (U : E ≃ₗᵢ[ℂ] E) (b : OrthonormalBasis (Fin n) ℂ E)
    (μ : Fin n → ℂ) (hb : ∀ i, U (b i) = μ i • b i) (hμ : ∀ i, ‖μ i‖ = 1) (ψ : E) :
    (⟪ψ, U ψ⟫_ℂ).re = ∑ i, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
  have hinner : ∀ i, ⟪b i, U ψ⟫_ℂ = μ i * ⟪b i, ψ⟫_ℂ := by
    intro i
    have hμi0 : μ i ≠ 0 := by
      intro hc
      have h1 := hμ i
      rw [hc, norm_zero] at h1
      exact zero_ne_one h1
    have hsymm : U.symm (b i) = (μ i)⁻¹ • b i := by
      apply U.injective
      rw [LinearIsometryEquiv.apply_symm_apply, map_smul, hb i, smul_smul,
        inv_mul_cancel₀ hμi0, one_smul]
    have h1 : ⟪b i, U ψ⟫_ℂ = ⟪U.symm (b i), ψ⟫_ℂ := by
      conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply U (b i)]
      rw [LinearIsometryEquiv.inner_map_map]
    rw [h1, hsymm, inner_smul_left, Complex.inv_eq_conj (hμ i), Complex.conj_conj]
  have hterm : ∀ i, (⟪ψ, b i⟫_ℂ * ⟪b i, U ψ⟫_ℂ).re
      = (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
    intro i
    rw [hinner i, ← inner_conj_symm ψ (b i)]
    have hzz : (starRingEnd ℂ) ⟪b i, ψ⟫_ℂ * ⟪b i, ψ⟫_ℂ
        = ((‖⟪b i, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [show (starRingEnd ℂ) ⟪b i, ψ⟫_ℂ * (μ i * ⟪b i, ψ⟫_ℂ)
        = μ i * ((starRingEnd ℂ) ⟪b i, ψ⟫_ℂ * ⟪b i, ψ⟫_ℂ) by ring, hzz]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← OrthonormalBasis.sum_inner_mul_inner b ψ (U ψ)]
  rw [show (∑ i, ⟪ψ, b i⟫_ℂ * ⟪b i, U ψ⟫_ℂ).re
      = ∑ i, (⟪ψ, b i⟫_ℂ * ⟪b i, U ψ⟫_ℂ).re from by simp]
  exact Finset.sum_congr rfl fun i _ => hterm i

omit [FiniteDimensional ℂ E] in

/-- If every eigenvalue real part is at most `c`, then the real part of `⟪ψ, U ψ⟫` is at most `c
* ‖ψ‖²`. See [ShenviKempeWhaley2003]. -/
theorem re_inner_apply_le_of_re_le {n : ℕ} (U : E ≃ₗᵢ[ℂ] E) (b : OrthonormalBasis (Fin n) ℂ E)
    (μ : Fin n → ℂ) (hb : ∀ i, U (b i) = μ i • b i) (hμ : ∀ i, ‖μ i‖ = 1) (ψ : E) {c : ℝ}
    (hc : ∀ i, (μ i).re ≤ c) :
    (⟪ψ, U ψ⟫_ℂ).re ≤ c * ‖ψ‖ ^ 2 := by
  rw [re_inner_apply_eq_sum U b μ hb hμ ψ]
  calc ∑ i, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2
      ≤ ∑ i, c * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (by positivity)
    _ = c * ∑ i, ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by rw [Finset.mul_sum]
    _ = c * ‖ψ‖ ^ 2 := by rw [OrthonormalBasis.sum_sq_norm_inner_right]

omit [FiniteDimensional ℂ E] in

/-- For a unit vector, if the distinguished eigenvalue has real part at most one and all others
have real part at most `t`, then the real expectation is at most `t + (1 - t) * ‖⟪b j0,
ψ⟫‖²`. See [ShenviKempeWhaley2003]. -/
theorem re_inner_apply_le_of_support {n : ℕ} (U : E ≃ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℂ) (hb : ∀ i, U (b i) = μ i • b i)
    (hμ : ∀ i, ‖μ i‖ = 1) (ψ : E) (hψ : ‖ψ‖ = 1) (j0 : Fin n) {t : ℝ}
    (hj0 : (μ j0).re ≤ 1) (hother : ∀ i, i ≠ j0 → (μ i).re ≤ t) :
    (⟪ψ, U ψ⟫_ℂ).re ≤ t + (1 - t) * ‖⟪b j0, ψ⟫_ℂ‖ ^ 2 := by
  set y : ℝ := ‖⟪b j0, ψ⟫_ℂ‖ ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  rw [re_inner_apply_eq_sum U b μ hb hμ ψ]
  have hsum1 : ∑ i, ‖⟪b i, ψ⟫_ℂ‖ ^ 2 = 1 := by
    rw [OrthonormalBasis.sum_sq_norm_inner_right, hψ]; norm_num
  have hsplit : ∑ i, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2
      = (μ j0).re * y + ∑ i ∈ Finset.univ.erase j0, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
    have h := Finset.add_sum_erase Finset.univ
      (fun i => (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2) (Finset.mem_univ j0)
    simpa only [hy] using h.symm
  rw [hsplit]
  have h1 : (μ j0).re * y ≤ 1 * y := mul_le_mul_of_nonneg_right hj0 hy0
  have h2 : ∑ i ∈ Finset.univ.erase j0, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2
      ≤ t * ∑ i ∈ Finset.univ.erase j0, ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hother i (Finset.ne_of_mem_erase hi)) (by positivity)
  have h3 : ∑ i ∈ Finset.univ.erase j0, ‖⟪b i, ψ⟫_ℂ‖ ^ 2 = 1 - y := by
    have h := Finset.sum_erase_add Finset.univ (fun i => ‖⟪b i, ψ⟫_ℂ‖ ^ 2)
      (Finset.mem_univ j0)
    rw [hsum1] at h
    have h' : y = ‖⟪b j0, ψ⟫_ℂ‖ ^ 2 := hy
    linarith
  have hsumle : (μ j0).re * y + ∑ i ∈ Finset.univ.erase j0, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2
      ≤ 1 * y + t * (1 - y) := by
    have h := add_le_add h1 (h2.trans_eq (by rw [h3]))
    exact h
  calc (μ j0).re * y + ∑ i ∈ Finset.univ.erase j0, (μ i).re * ‖⟪b i, ψ⟫_ℂ‖ ^ 2
      ≤ 1 * y + t * (1 - y) := hsumle
    _ = t + (1 - t) * y := by ring

omit [FiniteDimensional ℂ E] in

/-- If `t < 1`, all nondistinguished eigenvalues have real part at most `t`, the distinguished
one has real part at most one, and the unit-vector expectation is at least `R`, then its
distinguished squared overlap is at least `(R - t) / (1 - t)`. See [ShenviKempeWhaley2003]. -/
theorem spectral_support_lower {n : ℕ} (U : E ≃ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℂ) (hb : ∀ i, U (b i) = μ i • b i)
    (hμ : ∀ i, ‖μ i‖ = 1) (ψ : E) (hψ : ‖ψ‖ = 1) (j0 : Fin n) {t R : ℝ}
    (hj0 : (μ j0).re ≤ 1) (hother : ∀ i, i ≠ j0 → (μ i).re ≤ t) (ht : t < 1)
    (hR : R ≤ (⟪ψ, U ψ⟫_ℂ).re) :
    (R - t) / (1 - t) ≤ ‖⟪b j0, ψ⟫_ℂ‖ ^ 2 := by
  have hmain := re_inner_apply_le_of_support U b μ hb hμ ψ hψ j0 hj0 hother
  have hpos : (0 : ℝ) < 1 - t := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [hR, hmain]

omit [FiniteDimensional ℂ E] in

/-- The squared overlaps of a unit vector with two orthogonal unit vectors sum to at most one.
See [ShenviKempeWhaley2003]. -/
theorem overlap_sq_sum_le_one {ψ0 ψ1 ω : E} (h0 : ‖ψ0‖ = 1) (h1 : ‖ψ1‖ = 1)
    (h01 : ⟪ψ0, ψ1⟫_ℂ = 0) (hω : ‖ω‖ = 1) :
    ‖⟪ψ0, ω⟫_ℂ‖ ^ 2 + ‖⟪ψ1, ω⟫_ℂ‖ ^ 2 ≤ 1 := by
  let v : Fin 2 → E := ![ψ0, ψ1]
  have h10 : ⟪ψ1, ψ0⟫_ℂ = 0 := by
    rw [← inner_conj_symm ψ1 ψ0, h01, map_zero]
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, h0, h1, h01, h10]
  have hb := hv.sum_inner_products_le ω (s := Finset.univ)
  simpa [v, Fin.sum_univ_two, hω] using hb

omit [FiniteDimensional ℂ E] in

/-- If every unit vector orthogonal to both trial vectors has real expectation at most `t`, then
any basis eigenvector whose eigenvalue has real part greater than `t` overlaps at least one
trial vector. See [ShenviKempeWhaley2003]. -/
theorem eigenvector_overlaps_trial_of_re_gt {m : ℕ} (U : E ≃ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin m) ℂ E) (μ : Fin m → ℂ) (hb : ∀ i, U (b i) = μ i • b i)
    (hμ : ∀ i, ‖μ i‖ = 1) {ψ0 ψ1 : E} {t : ℝ}
    (hbound : ∀ α : E, ‖α‖ = 1 → ⟪ψ0, α⟫_ℂ = 0 → ⟪ψ1, α⟫_ℂ = 0 →
      (⟪α, U α⟫_ℂ).re ≤ t)
    {j : Fin m} (hj : t < (μ j).re) :
    ⟪ψ0, b j⟫_ℂ ≠ 0 ∨ ⟪ψ1, b j⟫_ℂ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h0, h1⟩ := h
  have hjb : ‖b j‖ = 1 := b.norm_eq_one j
  have hle := hbound (b j) hjb h0 h1
  have hexp := re_inner_apply_eq_sum U b μ hb hμ (b j)
  have hsum : ∑ i, (μ i).re * ‖⟪b i, b j⟫_ℂ‖ ^ 2 = (μ j).re := by
    rw [Finset.sum_eq_single j]
    · rw [b.inner_eq_one, norm_one, one_pow, mul_one]
    · intro i _ hij
      rw [b.inner_eq_zero hij, norm_zero, zero_pow (by norm_num), mul_zero]
    · intro hjnot
      exact absurd (Finset.mem_univ j) hjnot
  rw [hsum] at hexp
  linarith

/-- If the real expectation on unit vectors orthogonal to two trial vectors is at most `t`, then
at most two entries of an orthonormal eigenbasis have eigenvalue real part greater than `t`.
See [ShenviKempeWhaley2003]. -/
theorem card_large_eigen_le_two {m : ℕ} (U : E ≃ₗᵢ[ℂ] E) (b : OrthonormalBasis (Fin m) ℂ E)
    (μ : Fin m → ℂ) (hb : ∀ i, U (b i) = μ i • b i) (hμ : ∀ i, ‖μ i‖ = 1)
    {ψ0 ψ1 : E} {t : ℝ}
    (hbound : ∀ α : E, ‖α‖ = 1 → ⟪ψ0, α⟫_ℂ = 0 → ⟪ψ1, α⟫_ℂ = 0 →
      (⟪α, U α⟫_ℂ).re ≤ t) :
    (Finset.univ.filter (fun i : Fin m => t < (μ i).re)).card ≤ 2 := by
  classical
  by_contra hle
  have hcard : 2 < (Finset.univ.filter (fun i : Fin m => t < (μ i).re)).card := by omega
  obtain ⟨j1, hj1, j2, hj2, j3, hj3, h12, h13, h23⟩ := Finset.two_lt_card.mp hcard
  rw [Finset.mem_filter] at hj1 hj2 hj3
  obtain ⟨_, hj1t⟩ := hj1
  obtain ⟨_, hj2t⟩ := hj2
  obtain ⟨_, hj3t⟩ := hj3
  have hv : Orthonormal ℂ ![b j1, b j2, b j3] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [b.inner_eq_zero, h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  set V : Submodule ℂ E := Submodule.span ℂ (Set.range ![b j1, b j2, b j3]) with hV
  have hVfin : Module.finrank ℂ V = 3 := by
    rw [hV, finrank_span_eq_card hv.linearIndependent]
    simp
  let φ : V →ₗ[ℂ] (ℂ × ℂ) :=
    ((innerSL ℂ ψ0 : E →ₗ[ℂ] ℂ).comp V.subtype).prod
      ((innerSL ℂ ψ1 : E →ₗ[ℂ] ℂ).comp V.subtype)
  have hker : LinearMap.ker φ ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_prod, hVfin]
    norm_num
  obtain ⟨x, hxker, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxvalne : (x : E) ≠ 0 := fun hc => hxne (Subtype.ext hc)
  have hx0 : ⟪ψ0, (x : E)⟫_ℂ = 0 := by
    have h := hxker
    rw [LinearMap.mem_ker] at h
    have h1 := congrArg Prod.fst h
    simpa [φ, LinearMap.prod_apply, LinearMap.comp_apply, innerSL_apply_apply] using h1
  have hx1 : ⟪ψ1, (x : E)⟫_ℂ = 0 := by
    have h := hxker
    rw [LinearMap.mem_ker] at h
    have h1 := congrArg Prod.snd h
    simpa [φ, LinearMap.prod_apply, LinearMap.comp_apply, innerSL_apply_apply] using h1
  have hxnpos : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hxvalne
  set α : E := ((((‖(x : E)‖)⁻¹ : ℝ)) : ℂ) • (x : E) with hαdef
  have hαnorm : ‖α‖ = 1 := by
    rw [hαdef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxnpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxnpos)
  have hα0 : ⟪ψ0, α⟫_ℂ = 0 := by
    rw [hαdef, inner_smul_right, hx0, mul_zero]
  have hα1 : ⟪ψ1, α⟫_ℂ = 0 := by
    rw [hαdef, inner_smul_right, hx1, mul_zero]
  have hαV : α ∈ V := by
    rw [hαdef]
    exact Submodule.smul_mem V _ x.2
  have hspan0 : ∀ y ∈ V, ∀ i : Fin m, i ≠ j1 → i ≠ j2 → i ≠ j3 → ⟪b i, y⟫_ℂ = 0 := by
    intro y hy i hi1 hi2 hi3
    rw [hV] at hy
    refine Submodule.span_induction (p := fun z _ => ⟪b i, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨k, rfl⟩ := hz
      fin_cases k
      · simpa using b.inner_eq_zero hi1
      · simpa using b.inner_eq_zero hi2
      · simpa using b.inner_eq_zero hi3
    · simp
    · intro a c _ _ ha hc
      rw [inner_add_right, ha, hc, add_zero]
    · intro a c _ hc
      rw [inner_smul_right, hc, mul_zero]
  have hsupp : ∀ i : Fin m, i ∉ ({j1, j2, j3} : Finset (Fin m)) → ⟪b i, α⟫_ℂ = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hspan0 α hαV i hi.1 hi.2.1 hi.2.2
  have hsum_supp : (∑ i, (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2)
      = ∑ i ∈ ({j1, j2, j3} : Finset (Fin m)), (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ∉ ({j1, j2, j3} : Finset (Fin m)) →
        (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2 = 0 := by
      intro i _ hi
      rw [hsupp i hi, norm_zero, zero_pow (by norm_num), mul_zero]
    simpa using (Finset.sum_subset (Finset.subset_univ ({j1, j2, j3} : Finset (Fin m)))
      hz).symm
  have hparse : ∑ i ∈ ({j1, j2, j3} : Finset (Fin m)), ‖⟪b i, α⟫_ℂ‖ ^ 2 = 1 := by
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ∉ ({j1, j2, j3} : Finset (Fin m)) →
        ‖⟪b i, α⟫_ℂ‖ ^ 2 = 0 := by
      intro i _ hi
      rw [hsupp i hi, norm_zero, zero_pow (by norm_num)]
    have h1 := Finset.sum_subset (Finset.subset_univ ({j1, j2, j3} : Finset (Fin m))) hz
    have hfull : ∑ i : Fin m, ‖⟪b i, α⟫_ℂ‖ ^ 2 = 1 := by
      rw [OrthonormalBasis.sum_sq_norm_inner_right, hαnorm]
      norm_num
    rw [h1]
    simpa using hfull
  have hlt : t < ∑ i ∈ ({j1, j2, j3} : Finset (Fin m)), (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
    have hmem : ∀ i ∈ ({j1, j2, j3} : Finset (Fin m)), t < (μ i).re := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact hj1t
      · exact hj2t
      · exact hj3t
    have hle' : ∀ i ∈ ({j1, j2, j3} : Finset (Fin m)),
        t * ‖⟪b i, α⟫_ℂ‖ ^ 2 ≤ (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
      intro i hi
      exact mul_le_mul_of_nonneg_right (le_of_lt (hmem i hi)) (by positivity)
    have hex : ∃ i ∈ ({j1, j2, j3} : Finset (Fin m)),
        t * ‖⟪b i, α⟫_ℂ‖ ^ 2 < (μ i).re * ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
      have hpos : ∃ i ∈ ({j1, j2, j3} : Finset (Fin m)), 0 < ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
        by_contra hc
        push Not at hc
        have hc' : ∀ i ∈ ({j1, j2, j3} : Finset (Fin m)), ‖⟪b i, α⟫_ℂ‖ ^ 2 = 0 :=
          fun i hi => le_antisymm (hc i hi) (by positivity)
        rw [Finset.sum_eq_zero hc'] at hparse
        norm_num at hparse
      obtain ⟨i, hi, hc⟩ := hpos
      exact ⟨i, hi, mul_lt_mul_of_pos_right (hmem i hi) hc⟩
    have hstrict := Finset.sum_lt_sum hle' hex
    calc t = t * 1 := by ring
      _ = t * ∑ i ∈ ({j1, j2, j3} : Finset (Fin m)), ‖⟪b i, α⟫_ℂ‖ ^ 2 := by rw [hparse]
      _ = ∑ i ∈ ({j1, j2, j3} : Finset (Fin m)), t * ‖⟪b i, α⟫_ℂ‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ < _ := hstrict
  have hexp := re_inner_apply_eq_sum U b μ hb hμ α
  rw [hsum_supp] at hexp
  have hbound' := hbound α hαnorm hα0 hα1
  linarith

end Qatlib.Papers.QWalkSearch02.MainResults
