/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Finite value-at-risk bisection accuracy

This module proves the approximate quantile-bracket guarantee for `riskVaR` by combining median
CDF readout with finite routing. It also establishes monotonicity along sorted threshold indices
and normalization at the last threshold when the list contains all losses. These results
formalize the bisection analysis of [WoernerEgger2019].

## Main statements

* `riskCDF_indices`: monotonicity of cumulative probability along a sorted list.
* `riskCDF_last`: the last threshold has cumulative probability one.
* `riskVaRAlgorithmFinite`: establish the depth-weighted failure bound for the approximate
  quantile bracket.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators ENNReal
set_option warningAsError false
set_option autoImplicit false

/-- The cumulative risk probability is nondecreasing along valid indices of a sorted threshold
list. -/
theorem riskCDF_indices {I : Type} [Fintype I] (A : Matrix I I ℂ) (j : I) (loss : I → ℚ)
    (xs : List ℚ) (hs : xs.SortedLE) (u v : ℕ) (hu : u < xs.length) (hv : v < xs.length) (huv : u ≤ v) :
    riskCDF A j loss (xs.getD u 0) ≤ riskCDF A j loss (xs.getD v 0) := by
  apply riskCDF_monotone
  rw [List.getD_eq_getElem xs 0 hu, List.getD_eq_getElem xs 0 hv]
  exact hs.getElem_le_getElem_of_le huv

/-- For a unitary preparation, the last entry of a nonempty sorted list containing every loss
has cumulative probability one. -/
theorem riskCDF_last {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hxs : xs ≠ []) (hs : xs.SortedLE) (hloss : ∀ i, loss i ∈ xs) :
    riskCDF A j loss (xs.getLastD 0) = 1 := by
  have hlen := List.length_pos_of_ne_nil hxs
  have hb : ∀ i, loss i ≤ xs.getLastD 0 := by
    intro i
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp (hloss i)
    rw [← hn, List.get_eq_getElem, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hxs]
    simp only [Option.getD_some, List.getLast_eq_getElem]
    exact hs.getElem_le_getElem_of_le (by omega)
  rw [riskCDF_eq]
  simp only [riskCDFPayoff, if_pos (hb _), mul_one]
  exact bornProb_sum_eq_one (normalized_applyGate hA (normalized_ket j))

/-- If the readout window fits within the tolerance, `riskVaR` violates the approximate quantile
bracket with probability at most the search depth times `(8/9)^r`. This establishes the
finite bisection guarantee associated with [Woerner and Egger, Section
II][WoernerEgger2019]. -/
theorem riskVaRAlgorithmFinite : VaRAlgorithmFiniteRestricted := by
  intro I _ _ A j loss xs q eps M r hA hM hxs hs hloss hq0 hq1 heps hwindow
  have hsam : ∀ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskCDFLaw A j loss t M hA hM) r)
      (fun z => eps < |z-riskCDF A j loss t|) ≤ ENNReal.ofReal ((8/9:ℝ)^r) := by
    intro t
    apply le_trans (risk_event_mono _ (fun z hz => lt_of_le_of_lt hwindow hz))
    exact riskReadoutMedianFinite I A j loss t M r hA hM
  simpa only [riskVaR, Nat.cast_add, Nat.cast_one] using! (riskBisectFiniteRouting _ xs q eps ((8/9:ℝ)^r) (riskCDF A j loss) hxs hs hq0 hq1
    heps.le (by positivity) (riskCDF_monotone A j loss) (riskCDF_last A j loss xs hA hxs hs hloss) hsam).1
end Qatlib.Concepts.RiskEstimation.VaRQuantile
