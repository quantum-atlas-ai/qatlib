/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.EvenSVTOperatorActualRecordsStat
import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusActualRecordsSamp
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem evenSVTOperatorActualRecords : EvenSVTOperatorActualRecords := by
  intro K C _ _ _ _ A r c f fbar L Lbar d ε δ η₁ η₂ qs condQ
    hr hc hL hLb hd hε hδ hδ1 hA hη₁ hη₂ hbudget hε₁ hε₂ hband hqs hcond hLip hLipb hcons
  obtain ⟨Q,hQ,hprob⟩ := evenSVTFrobeniusActualRecords_proof K C A r c f fbar L Lbar d ε δ η₁ η₂ qs condQ
    hr hc hL hLb hd hε hδ hδ1 hA hη₁ hη₂ hbudget hε₁ hε₂ hband hqs hcond hLip hLipb hcons
  refine ⟨Q,hQ,le_trans ?_ hprob⟩
  unfold FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ ω,?_⟩
    exact ((Finset.mem_filter.mp hω).2).trans_le (spectral_operator_norm_le_frobenius _)
  · intro ω _ _
    exact Finset.prod_nonneg (fun _ _ => Q.nonneg _)
end Qatlib.Concepts.SketchSpectral.EvenSVT
