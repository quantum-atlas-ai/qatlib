/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic

/-!
# Winding-number null-homology rules

This module proves elementary rules for `IsNullHomologous`, expressed by vanishing winding
numbers outside an ambient set. It covers degenerate and constant curves, enlargement of the
ambient set, intersections, and transfer by winding-number equality, supporting the homological
contour calculus for [WangEtAl2026].

## Main statements

* `IsNullHomologous.mono`: enlargement of the ambient set.
* `IsNullHomologous.congr_windingNumber`: transfer through winding-number agreement.
* `isNullHomologous_iInter`: closure under arbitrary intersections.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ η : ℝ → ℂ} {a b c d : ℝ} {Ω Ω' : Set ℂ}

/-- Every curve is null-homologous relative to the whole complex plane in the winding-number
sense. -/
@[simp]
theorem isNullHomologous_univ (γ : ℝ → ℂ) (a b : ℝ) :
    IsNullHomologous γ a b (Set.univ : Set ℂ) := by
  rw [isNullHomologous_iff]
  intro w hw
  simp at hw

/-- A constant curve has vanishing winding number outside any prescribed set and hence is
null-homologous relative to that set. -/
@[simp]
theorem isNullHomologous_const (x : ℂ) (a b : ℝ) (Ω : Set ℂ) :
    IsNullHomologous (fun _ : ℝ => x) a b Ω := by
  rw [isNullHomologous_iff]
  intro w _hw
  exact windingNumber_const x a b w

/-- Null-homology relative to the empty set is equivalent to vanishing winding number at every
point. -/
@[simp]
theorem isNullHomologous_empty_iff :
    IsNullHomologous γ a b (∅ : Set ℂ) ↔ ∀ w, windingNumber γ a b w = 0 := by
  rw [isNullHomologous_iff]
  simp

/-- A curve on a degenerate parameter interval is null-homologous relative to any set. -/
theorem IsNullHomologous.refl (γ : ℝ → ℂ) (a : ℝ) (Ω : Set ℂ) :
    IsNullHomologous γ a a Ω := by
  rw [isNullHomologous_iff]
  intro z _hz
  exact windingNumber_same γ a z

/-- Equal parameter endpoints imply null-homology relative to any set. -/
theorem IsNullHomologous.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (Ω : Set ℂ) :
    IsNullHomologous γ a b Ω := by
  subst b
  exact IsNullHomologous.refl γ a Ω

/-- Vanishing of all winding numbers gives null-homology relative to the empty set. -/
theorem isNullHomologous_empty_of_forall_windingNumber_eq_zero
    (h : ∀ w, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b (∅ : Set ℂ) :=
  isNullHomologous_empty_iff.2 h

/-- Null-homology is preserved when the ambient set is enlarged. -/
theorem IsNullHomologous.mono (h : IsNullHomologous γ a b Ω) (hΩ : Ω ⊆ Ω') :
    IsNullHomologous γ a b Ω' := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  exact h w (fun hwΩ => hw (hΩ hwΩ))

/-- Null-homology relative to the empty set implies null-homology relative to every set. -/
theorem IsNullHomologous.of_empty (h : IsNullHomologous γ a b (∅ : Set ℂ)) :
    IsNullHomologous γ a b Ω :=
  h.mono (empty_subset Ω)

/-- Null-homology transfers to a set whose complement is contained in the original complement. -/
theorem IsNullHomologous.mono_compl (h : IsNullHomologous γ a b Ω) (hΩ : Ω'ᶜ ⊆ Ωᶜ) :
    IsNullHomologous γ a b Ω' :=
  h.mono (Set.compl_subset_compl.mp hΩ)

/-- Vanishing winding numbers on a set containing the ambient complement imply null-homology in
the ambient set. -/
theorem isNullHomologous_of_compl_subset {E : Set ℂ} (hE : Ωᶜ ⊆ E)
    (h : ∀ w ∈ E, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b Ω := by
  rw [isNullHomologous_iff]
  intro w hw
  exact h w (hE hw)

/-- Null-homology transfers between parametrized curves whose winding numbers agree outside the
ambient set. -/
theorem IsNullHomologous.congr_windingNumber (h : IsNullHomologous γ a b Ω)
    (hwind : ∀ w ∉ Ω, windingNumber η c d w = windingNumber γ a b w) :
    IsNullHomologous η c d Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  rw [hwind w hw]
  exact h w hw

/-- Null-homology relative to the left set implies null-homology relative to its union with
another set. -/
theorem IsNullHomologous.union_left (h : IsNullHomologous γ a b Ω) :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_left)

/-- Null-homology relative to the right set implies null-homology relative to its union with
another set. -/
theorem IsNullHomologous.union_right (h : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_right)

/-- Null-homology relative to each of two sets implies null-homology relative to their
intersection. -/
theorem IsNullHomologous.inter (hΩ : IsNullHomologous γ a b Ω) (hΩ' : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∩ Ω') := by
  rw [isNullHomologous_iff] at hΩ hΩ' ⊢
  intro w hw
  by_cases hwΩ : w ∈ Ω
  · exact hΩ' w (fun hwΩ' => hw ⟨hwΩ, hwΩ'⟩)
  · exact hΩ w hwΩ

/-- Null-homology relative to every member of a family implies null-homology relative to their
intersection. -/
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
