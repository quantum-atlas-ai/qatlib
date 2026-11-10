/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProductCav06.MainResults.SequentialDefs
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.MatProductCav06.MainResults

open Qatlib.Concepts.GramQueryCore.GramRealization

def standardMap {D : ℕ} (v : Fin D × Fin 2 × Fin 2) : Fin D × Fin 2 × Fin 2 :=
  (v.1, v.2.2, v.2.1)

theorem standardMap_involutive {D : ℕ} :
    Function.Involutive (@standardMap D) := by
  intro v
  rcases v with ⟨a, t, b⟩
  rfl

def standardTensor {D : ℕ} (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) :
    Fin 2 → Matrix (Fin D) (Fin D) ℂ :=
  fun b => Matrix.of fun aOut aIn => U (aOut, b) (aIn, 0)

theorem standardTensor_apply {D : ℕ}
    (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) (b : Fin 2)
    (aOut aIn : Fin D) :
    standardTensor U b aOut aIn = U (aOut, b) (aIn, 0) :=
  rfl

theorem standardTensor_isStepIsometry {D : ℕ}
    (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    IsStepIsometry (standardTensor U) := by
  unfold IsStepIsometry
  ext aIn aIn'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    standardTensor, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  have h := congrFun (congrFun hU (aIn, 0)) (aIn', 0)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Prod.mk.injEq] at h
  rw [Fintype.sum_prod_type] at h
  simpa using h

def stdEmbed (D : ℕ) : Matrix (Fin D × Fin 2) (Fin D) ℂ :=
  fun ab a' => if ab.2 = 0 then (if ab.1 = a' then 1 else 0) else 0

theorem stdEmbed_gram (D : ℕ) : (stdEmbed D)ᴴ * (stdEmbed D) = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  have h : ∀ d : Fin D, (∑ t : Fin 2, (stdEmbed D)ᴴ a (d, t) * (stdEmbed D) (d, t) b)
      = if a = d ∧ b = d then 1 else 0 := by
    intro d
    rw [Fin.sum_univ_two]
    show (stdEmbed D)ᴴ a (d, 0) * (stdEmbed D) (d, 0) b +
        (stdEmbed D)ᴴ a (d, 1) * (stdEmbed D) (d, 1) b = if a = d ∧ b = d then 1 else 0
    simp only [stdEmbed, Matrix.conjTranspose_apply]
    rw [if_neg (by norm_num : ¬ ((1:Fin 2) = 0))]
    simp only [star_zero]
    by_cases ha : a = d
    · by_cases hb : b = d
      · subst ha; subst hb; simp
      · simp [ha, hb, Ne.symm hb]
    · have h' : ¬ (d = a) := fun hda => ha hda.symm
      simp [ha, h']
  simp only [h]
  by_cases hab : a = b
  · subst hab; simp
  · have h' : ∀ d : Fin D, ¬ (a = d ∧ b = d) := by
      intro d hd; exact hab (hd.1.trans hd.2.symm)
    simp [h', hab]

def stdColumns {D : ℕ} (V : Fin 2 → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin 2) (Fin D) ℂ :=
  fun ab a' => V ab.2 ab.1 a'

theorem step_to_columns {D : ℕ} (V : Fin 2 → Matrix (Fin D) (Fin D) ℂ)
    (hV : ∑ x : Fin 2, (V x)ᴴ * (V x) = 1) :
    (stdEmbed D)ᴴ * (stdEmbed D) = (stdColumns V)ᴴ * (stdColumns V) := by
  have hW : (stdColumns V)ᴴ * (stdColumns V) = ∑ x : Fin 2, (V x)ᴴ * (V x) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stdColumns, Matrix.sum_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hW, hV, stdEmbed_gram]

theorem unitary_completion {D : ℕ} (V : Fin 2 → Matrix (Fin D) (Fin D) ℂ)
    (hV : ∑ x : Fin 2, (V x)ᴴ * (V x) = 1) :
    ∃ U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ,
      U ∈ Matrix.unitaryGroup (Fin D × Fin 2) ℂ ∧ U * (stdEmbed D) = stdColumns V :=
  gram_equal_actual_unitary_transport (Fin D × Fin 2) (Fin D) (stdEmbed D)
    (stdColumns V) (step_to_columns V hV)

theorem mul_stdEmbed_apply {D : ℕ}
    (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) (b : Fin 2) (a a' : Fin D) :
    (U * stdEmbed D) (a, b) a' = U (a, b) (a', 0) := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ x : Fin D, (∑ t : Fin 2, U (a, b) (x, t) * stdEmbed D (x, t) a')
      = U (a, b) (x, 0) * stdEmbed D (x, 0) a' := by
    intro x
    rw [Fin.sum_univ_two]
    simp [stdEmbed]
  simp only [h1]
  rw [Finset.sum_eq_single a']
  · simp [stdEmbed]
  · intro x _ hx
    simp [stdEmbed, hx]
  · intro hmem; exact absurd (Finset.mem_univ a') hmem

def InStandardMapClass (n D : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (U : Fin n → Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) (φI φF : Fin D → ℂ),
    (∀ i, (U i)ᴴ * (U i) = 1) ∧
      ∀ x, ψ x = seqAmplitude (fun i => standardTensor (U i)) φI φF x

theorem standardMapClass_subset_det {n D : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : InStandardMapClass n D ψ) : InDetSequentialClass n 2 D ψ := by
  rcases h with ⟨U, φI, φF, hU, hψ⟩
  exact ⟨fun i => standardTensor (U i), φI, φF,
    fun i => standardTensor_isStepIsometry (U i) (hU i), hψ⟩

theorem standardMapClass_subset_mps {n D : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : InStandardMapClass n D ψ) : InMpsClass n 2 D ψ :=
  det_subset_mps (standardMapClass_subset_det h)

theorem det_subset_standardMapClass {n D : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : InDetSequentialClass n 2 D ψ) : InStandardMapClass n D ψ := by
  classical
  rcases h with ⟨A, φI, φF, hIso, hψ⟩
  have hchoice : ∀ i : Fin n,
      ∃ U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ,
        U ∈ Matrix.unitaryGroup (Fin D × Fin 2) ℂ ∧ U * (stdEmbed D) = stdColumns (A i) :=
    fun i => unitary_completion (A i) (hIso i)
  choose U hUmem hUeq using hchoice
  refine ⟨U, φI, φF, ?_, ?_⟩
  · intro i
    have h := Matrix.mem_unitaryGroup_iff'.mp (hUmem i)
    simpa only [Matrix.star_eq_conjTranspose] using h
  · have hA : (fun i => standardTensor (U i)) = A := by
      funext i b a a'
      rw [standardTensor_apply, ← mul_stdEmbed_apply (U i) b a a', hUeq i]
      rfl
    intro x
    rw [hψ x, hA]

theorem standard_map_generates_all_mps {n D : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ) :
    InStandardMapClass n D ψ ↔ InDetSequentialClass n 2 D ψ := by
  constructor
  · exact standardMapClass_subset_det
  · exact det_subset_standardMapClass

end Qatlib.Papers.MatProductCav06.MainResults
