/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.MetricSpace.Kuratowski
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

theorem continuousOn' (hγ : AbsolutelyContinuousOnInterval γ a b) : ContinuousOn γ (uIcc a b) :=
  have he := TauCeti.isometry_kuratowskiEmbedding (γ a)
  he.isUniformInducing.isInducing.continuousOn_iff.2
    (show AbsolutelyContinuousOnInterval (TauCeti.kuratowskiEmbedding (γ a) ∘ γ) a b from
      by simpa only [AbsolutelyContinuousOnInterval, Function.comp_apply, he.dist_eq] using hγ).continuousOn

theorem aemeasurable_restrict_Ioc [MeasurableSpace X] [BorelSpace X]
    {μ : MeasureTheory.Measure ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AEMeasurable γ (μ.restrict (Ioc a b)) :=
  ((AbsolutelyContinuousOnInterval.continuousOn' hγ).mono (Ioc_subset_uIoc.trans uIoc_subset_uIcc)).aemeasurable measurableSet_Ioc

theorem boundedVariationOn' (hγ : AbsolutelyContinuousOnInterval γ a b) :
    BoundedVariationOn γ (uIcc a b) := by
  have he := TauCeti.isometry_kuratowskiEmbedding (γ a)
  have hvar : eVariationOn (TauCeti.kuratowskiEmbedding (γ a) ∘ γ) (uIcc a b) =
      eVariationOn γ (uIcc a b) := by
    simp only [eVariationOn, Function.comp_apply, he.edist_eq]
  rw [BoundedVariationOn, ← hvar]
  exact (show AbsolutelyContinuousOnInterval (TauCeti.kuratowskiEmbedding (γ a) ∘ γ) a b from
      by simpa only [AbsolutelyContinuousOnInterval, Function.comp_apply, he.dist_eq] using hγ).boundedVariationOn

theorem prodMk {Y : Type*} [PseudoMetricSpace Y] {δ : ℝ → Y}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hδ : AbsolutelyContinuousOnInterval δ a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (γ t, δ t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hγ hδ ⊢
  refine squeeze_zero (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg) (fun _ ↦ ?_)
    (by simpa using hγ.add hδ)
  rw [← Finset.sum_add_distrib]
  gcongr
  rw [Prod.dist_eq]
  exact max_le_add_of_nonneg dist_nonneg dist_nonneg

end AbsolutelyContinuousOnInterval

end
end Qatlib.Foundations.CbmdAnalysis.Residue
