/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {J I K L : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

def BlockCorner {J I : Type*} [Fintype J] [Fintype I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) : Matrix I I ℂ :=
  Matrix.of fun i i' => U (j₀, i) (j₀, i')

theorem blockCorner_apply {J I : Type*} [Fintype J] [Fintype I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (i i' : I) :
    BlockCorner U j₀ i i' = U (j₀, i) (j₀, i') := rfl

def IsBlockEncoding {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × I) ℂ ∧ 0 < α ∧
    BlockCorner U j₀ = ((α⁻¹ : ℝ) : ℂ) • A

theorem lcu_isBlockEncoding (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) {P : Matrix J J ℂ} {j₀ : J} (hP : IsPrepare P w j₀) :
    IsBlockEncoding (LCUWorkspace U P) j₀ (∑ j, w j • U j) 1 := by
  have hP1 : P * Pᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hP.1
    rwa [Matrix.star_eq_conjTranspose] at h
  have hPct : Pᴴ ∈ Matrix.unitaryGroup J ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hP1
  refine ⟨?_, one_pos, ?_⟩
  · exact Submonoid.mul_mem _ (tensorGate_unitary hPct (Submonoid.one_mem _))
      (Submonoid.mul_mem _ (select_unitary U hU)
        (tensorGate_unitary hP.1 (Submonoid.one_mem _)))
  · have hcorner : BlockCorner (LCUWorkspace U P) j₀ = ∑ j, w j • U j := by
      ext i i'
      calc BlockCorner (LCUWorkspace U P) j₀ i i'
          = (LCUWorkspace U P *ᵥ Ket (j₀, i')) (j₀, i) := by
            rw [blockCorner_apply]
            exact (mulVec_ket_apply _ _ _).symm
        _ = (LCUWorkspace U P *ᵥ TensorState (Ket j₀) (Ket i')) (j₀, i) := by
            rw [tensorState_ket_ket]
        _ = ((∑ j, w j • U j) *ᵥ Ket i') i :=
            congrFun (lcu_corner_apply U hw hP (Ket i')) i
        _ = (∑ j, w j • U j) i i' := mulVec_ket_apply _ _ _
    rw [hcorner]
    simp

theorem blockEncoding_scale {U : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ}
    {α : ℝ} (h : IsBlockEncoding U j₀ A α) {c : ℝ} (hc : 0 < c) :
    IsBlockEncoding U j₀ (c • A) (c * α) := by
  refine ⟨h.1, mul_pos hc h.2.1, ?_⟩
  rw [h.2.2]
  ext i i'
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  rw [mul_inv]
  symm
  calc (↑c)⁻¹ * (↑α)⁻¹ * (↑c * A i i')
      = (↑α)⁻¹ * ((↑c)⁻¹ * ↑c) * (A i i') := by ring
    _ = (↑α)⁻¹ * A i i' := by rw [inv_mul_cancel₀ hcc, mul_one]

def FiberEmbed {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    (j₀ : J) (A : Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun (a, i) (b, i') => if a = j₀ ∧ b = j₀ then A i i' else 0

theorem fiberEmbed_apply {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    (j₀ : J) (A : Matrix I I ℂ) (a : J) (i : I) (b : J) (i' : I) :
    FiberEmbed j₀ A (a, i) (b, i') = if a = j₀ ∧ b = j₀ then A i i' else 0 := rfl

theorem fiberEmbed_injective (j₀ : J) :
    Function.Injective (FiberEmbed (I := I) j₀) := by
  intro A B h
  ext i i'
  have h' := congrFun (congrFun h (j₀, i)) (j₀, i')
  rw [fiberEmbed_apply, fiberEmbed_apply, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩] at h'
  exact h'

theorem fiberEmbed_mul (j₀ : J) (A B : Matrix I I ℂ) :
    FiberEmbed j₀ A * FiberEmbed j₀ B = FiberEmbed j₀ (A * B) := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [fiberEmbed_apply]
  by_cases ha : a = j₀ <;> by_cases hb : b = j₀
  · rw [if_pos ⟨ha, hb⟩, Matrix.mul_apply, Finset.sum_eq_single j₀]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_pos ⟨ha, rfl⟩, if_pos ⟨rfl, hb⟩]
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (show ¬(a = j₀ ∧ m = j₀) from fun h => hm h.2), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ j₀) hcon
  · rw [if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => hb h.2)]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (show ¬(m = j₀ ∧ b = j₀) from fun h => hb h.2), mul_zero]
  · rw [if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (show ¬(a = j₀ ∧ m = j₀) from fun h => ha h.1), zero_mul]
  · rw [if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (show ¬(a = j₀ ∧ m = j₀) from fun h => ha h.1), zero_mul]

theorem fiberEmbed_conjTranspose (j₀ : J) (A : Matrix I I ℂ) :
    (FiberEmbed j₀ A)ᴴ = FiberEmbed j₀ Aᴴ := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [Matrix.conjTranspose_apply]
  by_cases ha : a = j₀ <;> by_cases hb : b = j₀ <;>
    simp [fiberEmbed_apply, ha, hb, Matrix.conjTranspose_apply]

def FiberProjector {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (j₀ : J) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun (a, i) (b, i') => if a = j₀ ∧ (a, i) = (b, i') then 1 else 0

theorem fiberProjector_apply {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (j₀ : J) (a : J) (i : I) (b : J) (i' : I) :
    FiberProjector (I := I) j₀ (a, i) (b, i')
      = if a = j₀ ∧ (a, i) = (b, i') then 1 else 0 := rfl

theorem fiberProjector_eq_fiberEmbed_one (j₀ : J) :
    FiberProjector (I := I) j₀ = FiberEmbed j₀ (1 : Matrix I I ℂ) := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [fiberProjector_apply, fiberEmbed_apply, Matrix.one_apply]
  by_cases ha : a = j₀ <;> by_cases hb : b = j₀ <;> by_cases hi : i = i'
  · rw [if_pos ⟨ha, Prod.ext_iff.mpr ⟨ha.trans hb.symm, hi⟩⟩, if_pos ⟨ha, hb⟩,
      if_pos hi]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from
        fun h => hi ((Prod.mk.injEq _ _ _ _) ▸ h.2).2),
      if_pos ⟨ha, hb⟩, if_neg hi]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from
        fun h => hb (((Prod.mk.injEq _ _ _ _) ▸ h.2).1.symm.trans ha)),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => hb h.2)]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from
        fun h => hb (((Prod.mk.injEq _ _ _ _) ▸ h.2).1.symm.trans ha)),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => hb h.2)]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from fun h => ha h.1),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from fun h => ha h.1),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from fun h => ha h.1),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]
  · rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (b, i')) from fun h => ha h.1),
      if_neg (show ¬(a = j₀ ∧ b = j₀) from fun h => ha h.1)]

theorem isOrthogonalProjector_fiberProjector (j₀ : J) :
    IsOrthogonalProjector (FiberProjector (I := I) j₀) := by
  constructor
  · show FiberProjector (I := I) j₀ * FiberProjector j₀ = FiberProjector j₀
    rw [fiberProjector_eq_fiberEmbed_one, fiberEmbed_mul, mul_one]
  · show star (FiberProjector (I := I) j₀) = FiberProjector j₀
    rw [Matrix.star_eq_conjTranspose, fiberProjector_eq_fiberEmbed_one,
      fiberEmbed_conjTranspose, Matrix.conjTranspose_one]

theorem fiberProjector_mul (j₀ : J) (M : Matrix (J × I) (J × I) ℂ) :
    FiberProjector j₀ * M
      = Matrix.of fun (a, i) (b, i') => if a = j₀ then M (a, i) (b, i') else 0 := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [fiberProjector_apply, Matrix.of_apply]
  by_cases ha : a = j₀
  · subst a
    rw [if_pos rfl, Finset.sum_eq_single j₀]
    · rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨rfl, rfl⟩, one_mul]
      · intro k _ hk
        rw [if_neg (show ¬(j₀ = j₀ ∧ (j₀, i) = (j₀, k)) from
          fun h => hk ((Prod.mk.injEq _ _ _ _) ▸ h.2).2.symm), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (show ¬(j₀ = j₀ ∧ (j₀, i) = (m, k)) from
        fun h => hm ((Prod.mk.injEq _ _ _ _) ▸ h.2).1.symm), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ j₀) hcon
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (m, k)) from fun h => ha h.1), zero_mul]

theorem mul_fiberProjector (j₀ : J) (M : Matrix (J × I) (J × I) ℂ) :
    M * FiberProjector j₀
      = Matrix.of fun (a, i) (b, i') => if b = j₀ then M (a, i) (b, i') else 0 := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [fiberProjector_apply, Matrix.of_apply]
  by_cases hb : b = j₀
  · subst b
    rw [if_pos rfl, Finset.sum_eq_single j₀]
    · rw [Finset.sum_eq_single i']
      · rw [if_pos ⟨rfl, rfl⟩, mul_one]
      · intro k _ hk
        rw [if_neg (show ¬(j₀ = j₀ ∧ (j₀, k) = (j₀, i')) from
          fun h => hk ((Prod.mk.injEq _ _ _ _) ▸ h.2).2), mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ i') hcon
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (show ¬(m = j₀ ∧ (m, k) = (j₀, i')) from
        fun h => hm ((Prod.mk.injEq _ _ _ _) ▸ h.2).1), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j₀) hcon
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (show ¬(m = j₀ ∧ (m, k) = (b, i')) from
      fun h => hb (((Prod.mk.injEq _ _ _ _) ▸ h.2).1 ▸ h.1)), mul_zero]

theorem fiberProjector_mul_mul_corner (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    FiberProjector j₀ * (U * FiberProjector j₀)
      = FiberEmbed j₀ (BlockCorner U j₀) := by
  rw [fiberProjector_mul, mul_fiberProjector]
  ext ⟨a, i⟩ ⟨b, i'⟩
  simp only [Matrix.of_apply, fiberEmbed_apply, blockCorner_apply]
  by_cases ha : a = j₀ <;> by_cases hb : b = j₀ <;> simp [ha, hb]

def IsProjectedEncoding {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) :
    Prop :=
  U ∈ Matrix.unitaryGroup (J × I) ℂ ∧ 0 < α ∧
    FiberProjector j₀ * (U * FiberProjector j₀) = FiberEmbed j₀ (((α⁻¹ : ℝ) : ℂ) • A)

theorem isProjectedEncoding_iff_isBlockEncoding
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) :
    IsProjectedEncoding U j₀ A α ↔ IsBlockEncoding U j₀ A α := by
  constructor
  · rintro ⟨hU, hα, hproj⟩
    exact ⟨hU, hα, fiberEmbed_injective j₀
      (by rwa [fiberProjector_mul_mul_corner] at hproj)⟩
  · rintro ⟨hU, hα, hcorner⟩
    exact ⟨hU, hα, by rw [fiberProjector_mul_mul_corner, hcorner]⟩

noncomputable def FiberReflection {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (j₀ : J) : Matrix (J × I) (J × I) ℂ :=
  ReflectionAbout (FiberProjector j₀)

theorem fiberReflection_unitary (j₀ : J) :
    FiberReflection (I := I) j₀ ∈ Matrix.unitaryGroup (J × I) ℂ :=
  reflectionAbout_unitary (isOrthogonalProjector_fiberProjector j₀)

theorem fiberReflection_conjTranspose (j₀ : J) :
    (FiberReflection (I := I) j₀)ᴴ = FiberReflection j₀ :=
  reflectionAbout_conjTranspose (isOrthogonalProjector_fiberProjector j₀)

theorem fiberReflection_mul_self (j₀ : J) :
    FiberReflection (I := I) j₀ * FiberReflection j₀ = 1 :=
  reflectionAbout_mul_self (isOrthogonalProjector_fiberProjector j₀)

theorem fiberEmbed_mul_fiberReflection (j₀ : J) (A : Matrix I I ℂ) :
    FiberEmbed j₀ A * FiberReflection j₀ = FiberEmbed j₀ A := by
  simp only [FiberReflection, ReflectionAbout, Matrix.mul_sub, Matrix.mul_smul,
    fiberProjector_eq_fiberEmbed_one, fiberEmbed_mul, mul_one, Matrix.mul_one]
  module

def tensorBlockEquiv : (J × I) × (K × L) ≃ (J × K) × (I × L) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem tensorBlockEquiv_symm_apply (j : J) (k : K) (i : I) (l : L) :
    tensorBlockEquiv.symm ((j, k), (i, l)) = ((j, i), (k, l)) := rfl

theorem conjTranspose_reindex {M N : Type*} [Fintype M] [Fintype N] (e : M ≃ N)
    (A : Matrix M M ℂ) :
    (Matrix.reindex e e A)ᴴ = Matrix.reindex e e Aᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.reindex_apply]

theorem unitaryGroup_reindex {M N : Type*} [Fintype M] [DecidableEq M] [Fintype N]
    [DecidableEq N] (e : M ≃ N) {A : Matrix M M ℂ}
    (hA : A ∈ Matrix.unitaryGroup M ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup N ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA ⊢
  rw [conjTranspose_reindex]
  have hmul := map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) Aᴴ A
  simp only [Matrix.reindexAlgEquiv_apply] at hmul
  rw [← hmul, hA, ← Matrix.reindexAlgEquiv_apply ℂ ℂ e, map_one]

theorem blockCorner_reindex_tensorGate (U : Matrix (J × I) (J × I) ℂ)
    (V : Matrix (K × L) (K × L) ℂ) (j₀ : J) (k₀ : K) :
    BlockCorner (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U V))
        (j₀, k₀)
      = TensorGate (BlockCorner U j₀) (BlockCorner V k₀) := by
  ext ⟨i, l⟩ ⟨i', l'⟩
  simp [blockCorner_apply, Matrix.reindex_apply, tensorBlockEquiv_symm_apply,
    tensorGate_apply]

theorem blockEncoding_tensor {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} {α : ℝ} (hU : IsBlockEncoding U j₀ A α)
    {V : Matrix (K × L) (K × L) ℂ} {k₀ : K} {B : Matrix L L ℂ} {β : ℝ}
    (hV : IsBlockEncoding V k₀ B β) :
    IsBlockEncoding (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U V))
      (j₀, k₀) (TensorGate A B) (α * β) := by
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast hU.2.1.ne'
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hV.2.1.ne'
  refine ⟨unitaryGroup_reindex _ (tensorGate_unitary hU.1 hV.1),
    mul_pos hU.2.1 hV.2.1, ?_⟩
  rw [blockCorner_reindex_tensorGate, hU.2.2, hV.2.2]
  ext ⟨i, l⟩ ⟨i', l'⟩
  simp only [tensorGate_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rw [mul_inv]
  ring

def IsScaledPrepare {J : Type*} [Fintype J] [DecidableEq J]
    (P : Matrix J J ℂ) (w : J → ℝ) (s : ℝ) (j₀ : J) : Prop :=
  P ∈ Matrix.unitaryGroup J ℂ ∧ 0 < s ∧
    P *ᵥ Ket j₀ = fun j => ((Real.sqrt (w j / s) : ℝ) : ℂ)

theorem isScaledPrepare_one {P : Matrix J J ℂ} {w : J → ℝ} {j₀ : J} :
    IsScaledPrepare P w 1 j₀ ↔ IsPrepare P w j₀ := by
  unfold IsScaledPrepare IsPrepare
  simp

theorem lcu_isBlockEncoding_of_isScaledPrepare (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    {w : J → ℝ} (hw : ∀ j, 0 ≤ w j)
    {P : Matrix J J ℂ} {s : ℝ} {j₀ : J} (hP : IsScaledPrepare P w s j₀) :
    IsBlockEncoding (LCUWorkspace U P) j₀ (∑ j, w j • U j) s := by
  have hprepare : IsPrepare P (fun j => w j / s) j₀ := ⟨hP.1, hP.2.2⟩
  have hnormalized := lcu_isBlockEncoding U hU
    (fun j => div_nonneg (hw j) hP.2.1.le) hprepare
  have hscaled := blockEncoding_scale hnormalized hP.2.1
  have hweights : s • (∑ j, (w j / s) • U j) = ∑ j, w j • U j := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    field_simp [ne_of_gt hP.2.1]
  simpa only [hweights, mul_one] using hscaled

theorem fiberProjector_hermitian (j₀ : J) :
    (FiberProjector (I := I) j₀)ᴴ = FiberProjector j₀ :=
  (isOrthogonalProjector_fiberProjector j₀).2

theorem fiberProjector_idempotent (j₀ : J) :
    FiberProjector (I := I) j₀ * FiberProjector j₀ = FiberProjector j₀ :=
  (isOrthogonalProjector_fiberProjector j₀).1

theorem fiberReflection_mulVec (j₀ : J) (χ : QState (J × I)) :
    FiberReflection j₀ *ᵥ χ = (2 : ℂ) • (FiberProjector j₀ *ᵥ χ) - χ := by
  rw [FiberReflection, ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem fiberProjector_mulVec_tensorState_ket (j₀ : J) (ψ : QState I) :
    FiberProjector j₀ *ᵥ TensorState (Ket j₀) ψ = TensorState (Ket j₀) ψ := by
  funext ⟨a, i⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, fiberProjector_apply,
    tensorState_apply]
  by_cases ha : a = j₀
  · subst a
    rw [Finset.sum_eq_single j₀]
    · rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨rfl, rfl⟩]
        simp [Ket]
      · intro k _ hk
        rw [if_neg (show ¬(j₀ = j₀ ∧ (j₀, i) = (j₀, k)) from
          fun h => hk ((Prod.mk.injEq _ _ _ _) ▸ h.2).2.symm), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (show ¬(j₀ = j₀ ∧ (j₀, i) = (m, k)) from
        fun h => hm ((Prod.mk.injEq _ _ _ _) ▸ h.2).1.symm), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ j₀) hcon
  · rw [Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ =>
      by rw [if_neg (show ¬(a = j₀ ∧ (a, i) = (m, k)) from fun h => ha h.1), zero_mul]]
    simp [Ket, ha]

theorem fiberEmbed_mulVec_tensorState_ket (j₀ : J) (A : Matrix I I ℂ) (ψ : QState I) :
    FiberEmbed j₀ A *ᵥ TensorState (Ket j₀) ψ = TensorState (Ket j₀) (A *ᵥ ψ) := by
  funext ⟨a, i⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, fiberEmbed_apply,
    tensorState_apply]
  by_cases ha : a = j₀
  · subst a
    rw [Finset.sum_eq_single j₀]
    · rw [Finset.sum_congr rfl fun k _ => by rw [if_pos ⟨rfl, rfl⟩]]
      rw [show Ket j₀ j₀ = (1 : ℂ) from by simp [Ket]]
      simp only [one_mul, Matrix.mulVec, dotProduct]
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (show ¬(j₀ = j₀ ∧ m = j₀) from fun h => hm h.2), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ j₀) hcon
  · rw [Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ =>
      by rw [if_neg (show ¬(a = j₀ ∧ m = j₀) from fun h => ha h.1), zero_mul]]
    simp [Ket, ha]

theorem tensorState_smul_ket_right (c : ℂ) (j₀ : J) (ψ : QState I) :
    TensorState (Ket j₀) (c • ψ) = c • TensorState (Ket j₀) ψ := by
  funext ⟨a, i⟩
  simp only [TensorState, Pi.smul_apply]
  ring

theorem fiberProjector_mul_fiberReflection (j₀ : J) :
    FiberProjector (I := I) j₀ * FiberReflection j₀ = FiberProjector j₀ := by
  rw [FiberReflection, ReflectionAbout, Matrix.mul_sub, Matrix.mul_smul,
    fiberProjector_idempotent, Matrix.mul_one]
  module

end Qatlib.Concepts.BlockEncoding.StateBlockEncoding
