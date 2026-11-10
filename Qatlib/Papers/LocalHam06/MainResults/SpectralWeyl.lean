/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace Qatlib.Papers.LocalHam06.MainResults.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem inner_apply_eq_sum_eigen
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n) (x : E) :
    ⟪x, T x⟫ = ∑ i : Fin n, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
  have hsum := (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hsymm : ⟪(hT.eigenvectorBasis hn) i, T x⟫ = ⟪T ((hT.eigenvectorBasis hn) i), x⟫ :=
    (hT ((hT.eigenvectorBasis hn) i) x).symm
  rw [hsymm, hT.apply_eigenvectorBasis hn i, real_inner_smul_left]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [real_inner_comm x ((hT.eigenvectorBasis hn) i)]
  ring

theorem inner_eq_zero_of_mem_span
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n)
    (s : Finset (Fin n)) {j : Fin n} (hj : j ∉ s) {x : E}
    (hx : x ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (s : Set (Fin n)))) :
    ⟪(hT.eigenvectorBasis hn) j, x⟫ = 0 := by
  classical
  have horth : Orthonormal ℝ (fun i => (hT.eigenvectorBasis hn) i) :=
    (hT.eigenvectorBasis hn).orthonormal
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have hne : j ≠ i := by rintro rfl; exact hj hi
    rw [orthonormal_iff_ite.mp horth j i, if_neg hne]
  · simp
  · intro p q _ _ hp hq
    rw [inner_add_right, hp, hq, add_zero]
  · intro a p _ hp
    rw [inner_smul_right, hp, mul_zero]

theorem sum_sq_inner_eigen
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n) (x : E) :
    ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 = ‖x‖ ^ 2 := by
  have h := (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem quad_le_of_span
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n)
    {μ : ℝ} {s : Finset (Fin n)} (hμ : ∀ i ∈ s, hT.eigenvalues hn i ≤ μ) {x : E}
    (hx : x ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (s : Set (Fin n)))) :
    ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2 := by
  classical
  rw [inner_apply_eq_sum_eigen T hT hn x]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ s →
      hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 = 0 := by
    intro i _ hi
    rw [inner_eq_zero_of_mem_span hT hn s hi hx]
    simp
  have hsplit : ∑ i ∈ s, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      = ∑ i : Fin n, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
    Finset.sum_subset (Finset.subset_univ s) hzero
  rw [← hsplit]
  calc ∑ i ∈ s, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      ≤ ∑ i ∈ s, μ * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hμ i hi) (sq_nonneg _)
    _ = μ * ∑ i ∈ s, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        rw [Finset.mul_sum]
    _ = μ * ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        congr 1
        have hsplit₂ : ∑ i ∈ s, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
            = ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
          Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
            rw [inner_eq_zero_of_mem_span hT hn s hi hx]; simp)
        rw [← hsplit₂]
    _ = μ * ‖x‖ ^ 2 := by rw [sum_sq_inner_eigen T hT hn x]

theorem quad_lt_of_span
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n)
    {μ : ℝ} {s : Finset (Fin n)} (hμ : ∀ i ∈ s, μ < hT.eigenvalues hn i) {x : E}
    (hx : x ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (s : Set (Fin n)))) (hx0 : x ≠ 0) :
    μ * ‖x‖ ^ 2 < ⟪x, T x⟫ := by
  classical
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ s →
      hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 = 0 := by
    intro i _ hi
    rw [inner_eq_zero_of_mem_span hT hn s hi hx]
    simp

  have hex : ∃ i ∈ s, (⟪hT.eigenvectorBasis hn i, x⟫) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) = 0 := by
      intro i
      by_cases hi : i ∈ s
      · exact hcon i hi
      · exact inner_eq_zero_of_mem_span hT hn s hi hx
    refine hx0 ?_
    calc x = ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) • (hT.eigenvectorBasis hn) i :=
          ((hT.eigenvectorBasis hn).sum_repr' x).symm
      _ = 0 := by simp [hall]
  obtain ⟨i₀, hi₀, hc₀⟩ := hex
  rw [inner_apply_eq_sum_eigen T hT hn x]
  have hsplit : ∑ i ∈ s, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      = ∑ i : Fin n, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
    Finset.sum_subset (Finset.subset_univ s) hzero
  rw [← hsplit]
  have hle : ∀ i ∈ s, μ * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      ≤ hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := fun i hi =>
    mul_le_mul_of_nonneg_right (le_of_lt (hμ i hi)) (sq_nonneg _)
  have hlt : ∃ i ∈ s, μ * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
      < hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
    ⟨i₀, hi₀, mul_lt_mul_of_pos_right (hμ i₀ hi₀) (sq_pos_of_ne_zero hc₀)⟩
  have hsumlt := Finset.sum_lt_sum hle hlt
  calc μ * ‖x‖ ^ 2
      = μ * ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        rw [sum_sq_inner_eigen T hT hn x]
    _ = μ * ∑ i ∈ s, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by
        congr 1
        have hsplit₂ : ∑ i ∈ s, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2
            = ∑ i : Fin n, (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 :=
          Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
            rw [inner_eq_zero_of_mem_span hT hn s hi hx]; simp)
        rw [← hsplit₂]
    _ = ∑ i ∈ s, μ * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := by rw [Finset.mul_sum]
    _ < ∑ i ∈ s, hT.eigenvalues hn i * (⟪hT.eigenvectorBasis hn i, x⟫) ^ 2 := hsumlt

omit [FiniteDimensional ℝ E] in

theorem span_image_eq_range {n : ℕ} (f : Fin n → E) (s : Finset (Fin n)) :
    Submodule.span ℝ (f '' (s : Set (Fin n))) =
      Submodule.span ℝ (Set.range (fun j : {j : Fin n // j ∈ s} => f j)) := by
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

omit [FiniteDimensional ℝ E] in

theorem finrank_span_image {n : ℕ} (f : Fin n → E) (s : Finset (Fin n))
    (hf : Orthonormal ℝ f) :
    Module.finrank ℝ (Submodule.span ℝ (f '' (s : Set (Fin n)))) = s.card := by
  rw [span_image_eq_range]
  have hcard : Fintype.card {j : Fin n // j ∈ s} = s.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [← hcard]
  exact finrank_span_eq_card
      ((hf.comp (fun j : {j : Fin n // j ∈ s} => (j : Fin n)) Subtype.val_injective).linearIndependent)

theorem eigenvalues_le_add {T S : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) {ε : ℝ}
    (hTS : ∀ x, ⟪x, T x⟫ ≤ ⟪x, S x⟫ + ε * ‖x‖ ^ 2) (i : Fin n) :
    hT.eigenvalues hn i ≤ hS.eigenvalues hn i + ε := by
  classical
  set μ : ℝ := hS.eigenvalues hn i + ε with hμdef
  by_contra hcon
  rw [not_le] at hcon
  set sT : Finset (Fin n) := Finset.univ.filter (fun j => μ < hT.eigenvalues hn j) with hsTdef
  have hmem : ∀ j, j ∈ sT ↔ μ < hT.eigenvalues hn j := by
    intro j; rw [hsTdef]; simp
  have hcard_le : sT.card ≤ i.val := by
    by_contra hbig
    rw [not_le] at hbig
    have hW : Module.finrank ℝ
        (Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n)))) = sT.card :=
      finrank_span_image _ sT (hT.eigenvectorBasis hn).orthonormal
    have hV : Module.finrank ℝ
        (Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n))))
        = n - i.val := by
      rw [finrank_span_image _ _ (hS.eigenvectorBasis hn).orthonormal, Fin.card_Ici]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n))))
      (Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n))))
    have hle : Module.finrank ℝ ↥(Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n)))
        ⊔ Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n)))) ≤ n := by
      calc Module.finrank ℝ ↥(Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n)))
          ⊔ Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n))))
          ≤ Module.finrank ℝ E := Submodule.finrank_le _
        _ = n := hn
    have hcardT : sT.card ≤ n := by
      have h1 : sT.card ≤ Fintype.card (Fin n) := Finset.card_le_univ sT
      simpa using h1
    have hiT : i.val < n := i.isLt
    have hpos : 0 < Module.finrank ℝ ↥(Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n)))
        ⊓ Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n)))) := by
      rw [hW, hV] at hsum
      omega
    have hne : Submodule.span ℝ ((hT.eigenvectorBasis hn) '' (sT : Set (Fin n)))
        ⊓ Submodule.span ℝ ((hS.eigenvectorBasis hn) '' ((Finset.Ici i) : Set (Fin n))) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hpos
      simp at hpos
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
    have hxW := hx.1
    have hxV := hx.2
    have hlt : μ * ‖x‖ ^ 2 < ⟪x, T x⟫ :=
      quad_lt_of_span hT hn (s := sT) (fun j hj => (hmem j).mp hj) hxW hx0
    have hle' : ⟪x, S x⟫ ≤ hS.eigenvalues hn i * ‖x‖ ^ 2 :=
      quad_le_of_span hS hn (s := Finset.Ici i) (μ := hS.eigenvalues hn i)
        (fun j hj => by
          rw [Finset.mem_Ici] at hj
          exact hS.eigenvalues_antitone hn hj) hxV
    have hTSx := hTS x
    have hposx : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    rw [hμdef] at hlt
    nlinarith [hlt, hle', hTSx]
  have hi_not : i ∉ sT := by
    intro hi
    have hsub : Finset.Iic i ⊆ sT := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [hmem]
      exact lt_of_lt_of_le hcon (hT.eigenvalues_antitone hn hj)
    have hle2 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hle2
    omega
  exact hi_not ((hmem i).mpr hcon)

theorem eigenvalues_abs_sub_le {T S : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) {ε : ℝ}
    (hTS : ∀ x, ⟪x, T x⟫ ≤ ⟪x, S x⟫ + ε * ‖x‖ ^ 2)
    (hST : ∀ x, ⟪x, S x⟫ ≤ ⟪x, T x⟫ + ε * ‖x‖ ^ 2) (i : Fin n) :
    |hT.eigenvalues hn i - hS.eigenvalues hn i| ≤ ε := by
  have h1 := eigenvalues_le_add hT hS hn hTS i
  have h2 := eigenvalues_le_add hS hT hn hST i
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Qatlib.Papers.LocalHam06.MainResults.Spectral
