/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.FoldedEstimate
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.NumericalMedian

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.QCounting98.MainResults.ActualCounting

theorem sortedMedian_close_of_bad_le (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε : ℝ)
    (hε : 0 ≤ ε)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    |sortedBlockMedian r v - μ| ≤ ε := by
  by_contra h
  push Not at h
  have hmaj := heterogeneous_sorted_median_majority_witness r v μ ε hε h
  omega

theorem median_threshold_decides_above (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε τ : ℝ)
    (hε : 0 ≤ ε) (hμ : τ + ε < μ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    τ < sortedBlockMedian r v := by
  have hclo := sortedMedian_close_of_bad_le r v μ ε hε hbad
  have h1 := (abs_le.mp hclo).1
  linarith

theorem median_threshold_decides_below (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε τ : ℝ)
    (hε : 0 ≤ ε) (hμ : μ + ε < τ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    sortedBlockMedian r v < τ := by
  have hclo := sortedMedian_close_of_bad_le r v μ ε hε hbad
  have h2 := (abs_le.mp hclo).2
  linarith

theorem source_count_median_failure (N P r : ℕ)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin P))
    (μ ε : ℝ) (hε : 0 ≤ ε)
    (hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
      (fun z => ε < |(N : ℝ) * foldedEstimate P z - μ|) ≤ 1 / 3) :
    p.probEvent (fun ω : Fin (2 * r + 1) → Fin P => ε <
      |sortedBlockMedian r (fun k => (N : ℝ) * foldedEstimate P (ω k)) - μ|)
      ≤ (8 / 9 : ℝ) ^ r := by
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure
    p (fun z => (N : ℝ) * foldedEstimate P z) r μ ε hε hb

theorem countrel_frequency_test_fires (r : ℕ) (v : Fin (2 * r + 1) → ℝ)
    (μ ε τ : ℝ) (hε : 0 ≤ ε) (hμ : τ + ε < μ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    τ < sortedBlockMedian r v :=
  median_threshold_decides_above r v μ ε τ hε hμ hbad

end Qatlib.Papers.QCounting98.MainResults.NumericalMedian
