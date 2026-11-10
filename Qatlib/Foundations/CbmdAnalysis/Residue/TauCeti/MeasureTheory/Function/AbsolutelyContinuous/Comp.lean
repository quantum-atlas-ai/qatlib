/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set

set_option maxHeartbeats 800000

theorem LipschitzOnWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {φ : X → Y} {γ : ℝ → X}
    {s : Set X} {a b : ℝ} {K : NNReal} (hφ : LipschitzOnWith K φ s)
    (hmap : MapsTo γ (uIcc a b) s) (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hγ ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδgood⟩ := hγ (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hsum := hδgood E hE hlen
  calc
    _ ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hφ.dist_le_mul _ (hmap (hE.left i hi).left) _ (hmap (hE.left i hi).right)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsum.le K.coe_nonneg
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field_simp

theorem LipschitzWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {φ : X → Y} {γ : ℝ → X}
    {a b : ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b :=
  LipschitzOnWith.comp_absolutelyContinuousOnInterval hφ.lipschitzOnWith (Set.mapsTo_univ _ _) hγ

theorem AbsolutelyContinuousOnInterval.congr
    {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgood⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have heq : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfg (hE.left i hi).left, hfg (hE.left i hi).right]
  rw [heq]
  exact hgood E hE hlen

theorem LocallyLipschitzOn.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {φ : X → Y} {γ : ℝ → X}
    {s : Set X} {a b : ℝ} (hφ : LocallyLipschitzOn s φ)
    (hmap : MapsTo γ (uIcc a b) s) (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  obtain ⟨K, hK⟩ := (hφ.mono hmap.image_subset).exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn (AbsolutelyContinuousOnInterval.continuousOn' hγ))
  exact LipschitzOnWith.comp_absolutelyContinuousOnInterval hK (mapsTo_image _ _) hγ

theorem Isometry.absolutelyContinuousOnInterval_comp_iff
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} (hf : Isometry f)
    {γ : ℝ → X} {a b : ℝ} :
    AbsolutelyContinuousOnInterval (f ∘ γ) a b ↔ AbsolutelyContinuousOnInterval γ a b := by
  simp only [absolutelyContinuousOnInterval_iff, Function.comp_apply, hf.dist_eq]

namespace AbsolutelyContinuousOnInterval

theorem comp_of_contDiffAt {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {γ : ℝ → F} {φ : F → G} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hφ : ∀ x ∈ γ '' uIcc a b, ContDiffAt ℝ 1 φ x) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  have hloc : LocallyLipschitzOn (γ '' uIcc a b) φ := by
    intro x hx
    obtain ⟨K, U, hU, hLip⟩ := (hφ x hx).exists_lipschitzOnWith
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  exact LocallyLipschitzOn.comp_absolutelyContinuousOnInterval hloc (mapsTo_image _ _) hγ

protected theorem log {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t ↦ Real.log (f t)) a b :=
  comp_of_contDiffAt hf fun _ ⟨t, ht, hft⟩ ↦ Real.contDiffAt_log.2 (hft ▸ h0 t ht)

end AbsolutelyContinuousOnInterval

end
end Qatlib.Foundations.CbmdAnalysis.Residue
