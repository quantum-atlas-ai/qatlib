/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ η : ℝ → ℂ} {a b c d : ℝ} {Ω Ω' : Set ℂ}

@[simp]
theorem isNullHomologous_univ (γ : ℝ → ℂ) (a b : ℝ) :
    IsNullHomologous γ a b (Set.univ : Set ℂ) := by
  rw [isNullHomologous_iff]
  intro w hw
  simp at hw

@[simp]
theorem isNullHomologous_const (x : ℂ) (a b : ℝ) (Ω : Set ℂ) :
    IsNullHomologous (fun _ : ℝ => x) a b Ω := by
  rw [isNullHomologous_iff]
  intro w _hw
  exact windingNumber_const x a b w

@[simp]
theorem isNullHomologous_empty_iff :
    IsNullHomologous γ a b (∅ : Set ℂ) ↔ ∀ w, windingNumber γ a b w = 0 := by
  rw [isNullHomologous_iff]
  simp

theorem IsNullHomologous.refl (γ : ℝ → ℂ) (a : ℝ) (Ω : Set ℂ) :
    IsNullHomologous γ a a Ω := by
  rw [isNullHomologous_iff]
  intro z _hz
  exact windingNumber_same γ a z

theorem IsNullHomologous.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (Ω : Set ℂ) :
    IsNullHomologous γ a b Ω := by
  subst b
  exact IsNullHomologous.refl γ a Ω

theorem isNullHomologous_empty_of_forall_windingNumber_eq_zero
    (h : ∀ w, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b (∅ : Set ℂ) :=
  isNullHomologous_empty_iff.2 h

theorem IsNullHomologous.mono (h : IsNullHomologous γ a b Ω) (hΩ : Ω ⊆ Ω') :
    IsNullHomologous γ a b Ω' := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  exact h w (fun hwΩ => hw (hΩ hwΩ))

theorem IsNullHomologous.of_empty (h : IsNullHomologous γ a b (∅ : Set ℂ)) :
    IsNullHomologous γ a b Ω :=
  h.mono (empty_subset Ω)

theorem IsNullHomologous.mono_compl (h : IsNullHomologous γ a b Ω) (hΩ : Ω'ᶜ ⊆ Ωᶜ) :
    IsNullHomologous γ a b Ω' :=
  h.mono (Set.compl_subset_compl.mp hΩ)

theorem isNullHomologous_of_compl_subset {E : Set ℂ} (hE : Ωᶜ ⊆ E)
    (h : ∀ w ∈ E, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b Ω := by
  rw [isNullHomologous_iff]
  intro w hw
  exact h w (hE hw)

theorem IsNullHomologous.congr_windingNumber (h : IsNullHomologous γ a b Ω)
    (hwind : ∀ w ∉ Ω, windingNumber η c d w = windingNumber γ a b w) :
    IsNullHomologous η c d Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  rw [hwind w hw]
  exact h w hw

theorem IsNullHomologous.union_left (h : IsNullHomologous γ a b Ω) :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_left)

theorem IsNullHomologous.union_right (h : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_right)

theorem IsNullHomologous.inter (hΩ : IsNullHomologous γ a b Ω) (hΩ' : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∩ Ω') := by
  rw [isNullHomologous_iff] at hΩ hΩ' ⊢
  intro w hw
  by_cases hwΩ : w ∈ Ω
  · exact hΩ' w (fun hwΩ' => hw ⟨hwΩ, hwΩ'⟩)
  · exact hΩ w hwΩ

theorem isNullHomologous_iInter {ι : Sort*} {Ω : ι → Set ℂ}
    (h : ∀ i, IsNullHomologous γ a b (Ω i)) :
    IsNullHomologous γ a b (⋂ i, Ω i) := by
  classical
  rw [isNullHomologous_iff]
  intro w hw
  rw [mem_iInter] at hw
  push Not at hw
  obtain ⟨i, hi⟩ := hw
  exact (isNullHomologous_iff.mp (h i)) w hi

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
