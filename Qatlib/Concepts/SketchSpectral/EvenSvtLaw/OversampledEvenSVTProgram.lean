/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusActualRecordsSamp
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.OversampledEvenSVTDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

end Qatlib.Concepts.SketchSpectral.EvenSvtLaw

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw.SamplingBasedLowRank2019
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem oversampledEvenSVTRun_records :
    ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
      (A : Matrix K C ℂ) (r c : ℕ) (f fbar : ℝ → ℂ) (qs : FinDist K)
      (condQ : (Fin r → K) → FinDist C) (v : Fin r → K) (w : Fin c → C),
      let run := oversampledEvenSVTRun A r c f fbar qs condQ v w
      run.rowRecords = List.ofFn (compactSketchData qs r v) ∧
      run.columnRecords = List.ofFn (compactSketchData (condQ v) c w) ∧
      run.rowData = compactSketchData qs r v ∧
      run.columnData = compactSketchData (condQ v) c w ∧
      run.rows = compactSketched (compactSketchData qs r v) A ∧
      run.columns = (compactSketched (compactSketchData (condQ v) c w)
        (compactSketched (compactSketchData qs r v) A)ᴴ)ᴴ := by
  intro K C _ _ _ _ A r c f fbar qs condQ v w
  simp [oversampledEvenSVTRun, compactSketchBuild_eq]

theorem oversampledActualGramTail :
    ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
      (q : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (φ δ : ℝ),
      0 < r → 1 ≤ φ → 0 < sketchSquared A → 0 < δ → δ < 1 →
      (∀ i, sketchRowSquared A i / (φ * sketchSquared A) ≤ q.prob i) →
      q.probEvent (fun v : Fin r → K =>
        Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (r : ℝ)) * sketchSquared A ≤
          spectralFrobenius ((compactSketched (compactSketchData q r v) A)ᴴ *
            compactSketched (compactSketchData q r v) A - Aᴴ * A)) ≤ δ := by
  intro K C _ _ _ _ q r A φ δ hr hφ hA hδ hδ1 hdom
  have hs (i : K) : Real.sqrt (sketchRowSquared A i) *
      Real.sqrt (sketchRowSquared A i) = sketchRowSquared A i :=
    Real.mul_self_sqrt (sketchRowSquared_nonneg A i)
  have hm : sketchRowProductMass A A = sketchSquared A := by
    simp only [sketchRowProductMass, hs, sketchSquared]
  have ht := compact_sketch_two_sided_source_frobenius_tail K C C q r A A φ δ
    hr hφ (by rw [hm]; exact hA) hδ hδ1 (fun i => by rw [hs, hm]; exact hdom i)
  simp only [hm] at ht
  simp_rw [(compact_sketch_actual_pairs_entries_and_queries K C C q r A A _).2.2.2.2.2,
    ← spectralFrobenius_eq_sampling_norm] at ht
  exact ht

end Qatlib.Concepts.SketchSpectral.EvenSvtLaw.SamplingBasedLowRank2019
