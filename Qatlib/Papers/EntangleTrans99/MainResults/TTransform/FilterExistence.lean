/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
import Qatlib.Papers.EntangleTrans99.MainResults.TTransform.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.TTransform

open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open scoped BigOperators

theorem tTransformSpectrum_pos {D : ℕ} (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D)
    (hpos : ∀ j, 0 < spec j) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : Fin D) :
    0 < tTransformSpectrum spec θ k l j := by
  by_cases hjk : j = k
  · rw [hjk, tTransformSpectrum_k]
    rcases lt_or_eq_of_le hθ0 with hθ0' | hθ0'
    · have h1 : 0 < θ * spec k := mul_pos hθ0' (hpos k)
      have h2 : 0 ≤ (1 - θ) * spec l :=
        mul_nonneg (by linarith) (le_of_lt (hpos l))
      linarith
    · subst hθ0'
      simpa using hpos l
  · by_cases hjl : j = l
    · rw [hjl, tTransformSpectrum_l]
      rcases lt_or_eq_of_le hθ0 with hθ0' | hθ0'
      · have h1 : 0 < θ * spec l := mul_pos hθ0' (hpos l)
        have h2 : 0 ≤ (1 - θ) * spec k :=
          mul_nonneg (by linarith) (le_of_lt (hpos k))
        linarith
      · subst hθ0'
        simpa using hpos k
    · rw [tTransformSpectrum_of_ne spec θ k l j hjk hjl]
      exact hpos j

theorem exists_admissible_filter {D : ℕ} (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D)
    (hpos : ∀ j, 0 < spec j) (hsum : (∑ j, spec j) = 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ p : ℝ, 0 < p ∧ (∀ j, 0 ≤ tTransformFilter spec p θ k l j) ∧
      (∀ j, tTransformFilter spec p θ k l j ≤ 1) := by
  classical
  have hApos : ∀ j, 0 < tTransformSpectrum spec θ k l j :=
    fun j => tTransformSpectrum_pos spec θ k l hpos hθ0 hθ1 j
  let S : Finset ℝ :=
    (Finset.univ : Finset (Fin D)).image
      (fun j => spec j / tTransformSpectrum spec θ k l j)
  have hS : S.Nonempty :=
    ⟨spec k / tTransformSpectrum spec θ k l k,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩
  let p : ℝ := S.min' hS
  have hp_le : ∀ j, p ≤ spec j / tTransformSpectrum spec θ k l j := by
    intro j
    have hmem : spec j / tTransformSpectrum spec θ k l j ∈ S :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    exact (Finset.isLeast_min' S hS).2 hmem
  have hp0 : 0 < p := by
    change 0 < S.min' hS
    rw [Finset.lt_min'_iff]
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact div_pos (hpos j) (hApos j)
  refine ⟨p, hp0, ?_, ?_⟩
  · intro j
    simp only [tTransformFilter]
    exact div_nonneg (mul_nonneg (le_of_lt hp0) (le_of_lt (hApos j))) (le_of_lt (hpos j))
  · intro j
    simp only [tTransformFilter]
    rw [div_le_one (hpos j)]
    calc p * tTransformSpectrum spec θ k l j
        ≤ (spec j / tTransformSpectrum spec θ k l j) * tTransformSpectrum spec θ k l j :=
          mul_le_mul_of_nonneg_right (hp_le j) (le_of_lt (hApos j))
      _ = spec j := div_mul_cancel₀ _ (ne_of_gt (hApos j))

theorem exists_tTransformCriterion {D E : ℕ} (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D)
    (hpos : ∀ j, 0 < spec j) (hsum : (∑ j, spec j) = 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ p : ℝ, 0 < p ∧ TTransformCriterion D E spec p θ k l := by
  obtain ⟨p, hp0, hf0, hf1⟩ := exists_admissible_filter spec θ k l hpos hsum hθ0 hθ1
  exact ⟨p, hp0, tTransformCriterion D E spec p θ k l hf1 hf0 hpos hp0 hsum hθ0 hθ1⟩

end Qatlib.Papers.EntangleTrans99.MainResults.TTransform
