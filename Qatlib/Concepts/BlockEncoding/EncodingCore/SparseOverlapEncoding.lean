/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.BlockEncoding.EncodingCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def sparseOverlapLeft {I O : Type} [Fintype I] [Fintype O]
 [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (s : ℝ) :
 Matrix ((O×I)⊕(O⊕I)) O ℂ := fun h o => match h with
 | .inl (u,i) => if u=o then (Real.sqrt (‖A o i‖/s):ℂ) else 0
 | .inr (.inl u) => if u=o then (Real.sqrt (1-(∑ i,‖A o i‖)/s):ℂ) else 0
 | .inr (.inr _) => 0

noncomputable def sparseOverlapRight {I O : Type} [Fintype I] [Fintype O]
 [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (s : ℝ) :
 Matrix ((O×I)⊕(O⊕I)) I ℂ := fun h i => match h with
 | .inl (o,v) => if v=i then A o i / ((Real.sqrt s*Real.sqrt ‖A o i‖:ℝ):ℂ) else 0
 | .inr (.inl _) => 0
 | .inr (.inr v) => if v=i then (Real.sqrt (1-(∑ o,‖A o i‖)/s):ℂ) else 0

private theorem sparse_sqrt_mass (x : ℝ) (hx : 0 ≤ x) :
    star (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two,
    Real.sq_sqrt hx]

private theorem sparse_right_mass (a : ℂ) (s : ℝ) (hs : 0 < s) :
    star (a / ((Real.sqrt s * Real.sqrt ‖a‖ : ℝ) : ℂ)) *
      (a / ((Real.sqrt s * Real.sqrt ‖a‖ : ℝ) : ℂ)) = ((‖a‖ / s : ℝ) : ℂ) := by
  rw [Complex.star_def, map_div₀, Complex.conj_ofReal, div_mul_div_comm,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_mul, ← Complex.ofReal_div]
  congr 1
  by_cases ha : a = 0
  · simp [ha]
  · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hsqrt : (Real.sqrt s * Real.sqrt ‖a‖) *
        (Real.sqrt s * Real.sqrt ‖a‖) = s * ‖a‖ := by
      calc
        _ = (Real.sqrt s) ^ 2 * (Real.sqrt ‖a‖) ^ 2 := by ring
        _ = s * ‖a‖ := by rw [Real.sq_sqrt hs.le, Real.sq_sqrt hn.le]
    rw [hsqrt]
    field_simp

private theorem sparse_entry_overlap (a : ℂ) (s : ℝ) (hs : 0 < s) :
    star (Real.sqrt (‖a‖ / s) : ℂ) *
      (a / ((Real.sqrt s * Real.sqrt ‖a‖ : ℝ) : ℂ)) = (s : ℂ)⁻¹ * a := by
  rw [Complex.star_def, Complex.conj_ofReal, Real.sqrt_div (norm_nonneg a), Complex.ofReal_div,
    Complex.ofReal_mul]
  by_cases ha : a = 0
  · simp [ha]
  · have hn : Real.sqrt ‖a‖ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr ha))
    have ht : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
    have htC : (Real.sqrt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have hnC : (Real.sqrt ‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hsq : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
    rw [← hsq]
    field_simp

private theorem sparse_left_isometry {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (s : ℝ) (hs : 0 < s)
    (hrow : ∀ o, (∑ i, ‖A o i‖) ≤ s) : IsIsometry (sparseOverlapLeft A s) := by
  unfold IsIsometry
  ext o p
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, sparseOverlapLeft]
  by_cases h : o = p
  · subst p
    simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
      ← ite_and, and_self, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const_zero,
      add_zero, Matrix.one_apply_eq]
    have hr : 0 ≤ 1 - (∑ i, ‖A o i‖) / s := by
      have := (div_le_one hs).mpr (hrow o)
      linarith
    simp_rw [sparse_sqrt_mass _ (div_nonneg (norm_nonneg _) hs.le)]
    rw [sparse_sqrt_mass _ hr, ← Complex.ofReal_sum, ← Finset.sum_div,
      ← Complex.ofReal_add]
    norm_num
  · have h' : p ≠ o := Ne.symm h
    simp [apply_ite star, ite_mul, mul_ite, h, h', Matrix.one_apply_ne]

private theorem sparse_right_isometry {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (s : ℝ) (hs : 0 < s)
    (hcol : ∀ i, (∑ o, ‖A o i‖) ≤ s) : IsIsometry (sparseOverlapRight A s) := by
  unfold IsIsometry
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, sparseOverlapRight]
  by_cases h : i = j
  · subst j
    simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
      ← ite_and, and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero,
      zero_add, Matrix.one_apply_eq]
    have hr : 0 ≤ 1 - (∑ o, ‖A o i‖) / s := by
      have := (div_le_one hs).mpr (hcol i)
      linarith
    simp_rw [sparse_right_mass _ _ hs]
    rw [sparse_sqrt_mass _ hr, ← Complex.ofReal_sum, ← Finset.sum_div,
      ← Complex.ofReal_add]
    norm_num
  · have h' : j ≠ i := Ne.symm h
    simp [apply_ite star, ite_mul, mul_ite, h, h', Matrix.one_apply_ne]

theorem sparse_overlap_actual_frames_and_corner :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (s : ℝ), 0 < s → (∀ o, (∑ i, ‖A o i‖) ≤ s) →
      (∀ i, (∑ o, ‖A o i‖) ≤ s) →
      IsIsometry (sparseOverlapLeft A s) ∧ IsIsometry (sparseOverlapRight A s) ∧
      (sparseOverlapLeft A s)ᴴ * sparseOverlapRight A s = (s : ℂ)⁻¹ • A := by
  intro I O _ _ _ _ A s hs hr hc
  refine ⟨sparse_left_isometry A s hs hr, sparse_right_isometry A s hs hc, ?_⟩
  ext o i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, sparseOverlapLeft, sparseOverlapRight]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero,
    add_zero]
  exact sparse_entry_overlap (A o i) s hs

private theorem sparse_sum_norm_le {J : Type} [Fintype J] [DecidableEq J]
    (f : J → ℂ) (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hc : (Finset.univ.filter (fun j => f j ≠ 0)).card ≤ k)
    (hf : ∀ j, ‖f j‖ ≤ b) : (∑ j, ‖f j‖) ≤ k * b := by
  let t := Finset.univ.filter (fun j => f j ≠ 0)
  have he : (∑ j, ‖f j‖) = ∑ j ∈ t, ‖f j‖ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    have hz : f j = 0 := by simpa [t] using hj
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ _j ∈ t, b := Finset.sum_le_sum fun j _ => hf j
    _ = (t.card : ℝ) * b := by simp
    _ ≤ (k : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hb

theorem sparse_overlap_derived_sparse_entry_norm_consumer :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (k : ℕ) (b : ℝ), 0 < b → 0 < k →
      (∀ o, (Finset.univ.filter (fun i => A o i ≠ 0)).card ≤ k) →
      (∀ i, (Finset.univ.filter (fun o => A o i ≠ 0)).card ≤ k) →
      (∀ o i, ‖A o i‖ ≤ b) →
      ProjectedUnitaryEncoding (((k : ℂ) * (b : ℂ))⁻¹ • A)
        (1 : Matrix ((O × I) ⊕ (O ⊕ I)) ((O × I) ⊕ (O ⊕ I)) ℂ)
        (sparseOverlapLeft A (k * b)) (sparseOverlapRight A (k * b)) ∧ ‖A‖ ≤ k * b := by
  intro I O _ _ _ _ A k b hb hk hr hc he
  have hs : 0 < (k : ℝ) * b := mul_pos (by exact_mod_cast hk) hb
  have hrow := fun o => sparse_sum_norm_le (A o) k b hb.le (hr o) (he o)
  have hcol := fun i => sparse_sum_norm_le (fun o => A o i) k b hb.le (hc i) (fun o => he o i)
  obtain ⟨hL, hR, hcorner⟩ := sparse_overlap_actual_frames_and_corner I O A (k * b) hs hrow hcol
  have hU : (1 : Matrix ((O × I) ⊕ (O ⊕ I)) ((O × I) ⊕ (O ⊕ I)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ := by simp
  have hn := l2_norm_compress_le_one hL hU hR
  have heq : compress (sparseOverlapLeft A (k * b)) 1 (sparseOverlapRight A (k * b)) =
      (((k : ℝ) * b : ℝ) : ℂ)⁻¹ • A := by simpa [compress] using hcorner
  refine ⟨⟨hU, hL, hR, ?_⟩, ?_⟩
  · simpa using heq
  · rw [heq, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs, inv_mul_eq_div] at hn
    exact (div_le_one hs).mp hn

end Qatlib.Concepts.BlockEncoding.EncodingCore
