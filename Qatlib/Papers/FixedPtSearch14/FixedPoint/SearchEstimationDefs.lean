/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefinedDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchEstimation

/-!
# Native count readout and pilot-tail estimates

This module defines rational label records and integer count readouts for the estimation
interfaces used alongside fixed-point search [YoderLowChuang2014]. It compares the native label
with the source readout and proves count-range, rounding-error, and boundary estimates.

The remaining lemmas expose the moment reserve needed for pilot-tail control and establish
minimum grid sizes for exact counting.

## Main statements

* `nextS2LabelRecord_agrees_with_source`: Comparison of the two finite-precision label
  decodings.
* `nextS2CountReadout_error`: Count error including decoding and rounding contributions.
* `nextPilotBadMoment_mass_le_reserve_s2`: Pilot failure mass bounded by the reserved failure
  budget.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib
open Matrix
open scoped ENNReal Classical
open BHMTQSearch
open RandomizedExecution
open Filter
open scoped Topology
open BHMTTh17

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint
namespace SearchEstimationCore

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The rational native label record at grid size `M`, precision `k`, and measured label `z`. -/
def nextS2LabelRecord (M k : ℕ) (z : Fin M) : ℚ :=
  AmplitudeReadoutRefined.nextLabelRecord M k z

/-- The integer count readout obtained from the native decoding at population size `N`. -/
noncomputable def nextS2CountReadout (N M k : ℕ) (z : Fin M) : ℤ :=
  AmplitudeReadoutRefined.nextCountReadout N M k z

/-- The native label record and the source readout differ by at most `2⁻ᵇ + 2⁻ᵏ`. -/
theorem nextS2LabelRecord_agrees_with_source (M b k : ℕ) (z : Fin M) :
    |(nextS2LabelRecord M k z : ℝ) - (s2EstimationReadout M b z : ℝ)|
      ≤ ((2 : ℝ)⁻¹) ^ b + ((2 : ℝ)⁻¹) ^ k := by
  have hsrc := s2_estimation_readout_terminating M b z
  have hsrc' : |(s2EstimationReadout M b z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ b := by
    have h1 : |(s2EstimationReadout M b z : ℝ) - aeEstimate M z| * (2 : ℝ)^b < 1 := hsrc.2
    have hpos : (0:ℝ) < (2 : ℝ)^b := by positivity
    have hlt : |(s2EstimationReadout M b z : ℝ) - aeEstimate M z| < 1 / (2 : ℝ)^b := by
      exact (lt_div_iff₀ hpos).2 h1
    have hid : 1 / (2 : ℝ)^b = (2 : ℝ)⁻¹ ^ b := by
      rw [one_div, inv_pow]
    rw [hid] at hlt
    linarith
  have hrec' : |((nextS2LabelRecord M k z : ℝ)) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := by
    rw [nextS2LabelRecord, AmplitudeReadoutRefined.nextLabelRecord]
    exact (native_ae_computed_scalar_precision M k z).2.2
  have hsrc'' : |(aeEstimate M z) - (s2EstimationReadout M b z : ℝ)| ≤ ((2 : ℝ)⁻¹) ^ b := by
    rw [abs_sub_comm]
    exact hsrc'
  calc
    |(nextS2LabelRecord M k z : ℝ) - (s2EstimationReadout M b z : ℝ)|
        ≤ |((nextS2LabelRecord M k z : ℝ)) - aeEstimate M z|
          + |(aeEstimate M z) - (s2EstimationReadout M b z : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ ((2 : ℝ)⁻¹) ^ k + ((2 : ℝ)⁻¹) ^ b := add_le_add hrec' hsrc''
    _ = ((2 : ℝ)⁻¹) ^ b + ((2 : ℝ)⁻¹) ^ k := by ring

/-- The integer count readout lies between zero and `N`. -/
theorem nextS2CountReadout_valid (N M k : ℕ) (z : Fin M) :
    0 ≤ nextS2CountReadout N M k z ∧ nextS2CountReadout N M k z ≤ N := by
  rw [nextS2CountReadout]
  exact AmplitudeReadoutRefined.nextCountReadout_valid N M k z

/-- The integer count differs from `N` times the ideal amplitude estimate by at most `N * 2⁻ᵏ +
1/2`. -/
theorem nextS2CountReadout_error (N M k : ℕ) (z : Fin M) :
    |(nextS2CountReadout N M k z : ℝ) - (N : ℝ) * aeEstimate M z|
      ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 := by
  rw [nextS2CountReadout]
  exact AmplitudeReadoutRefined.nextCountReadout_error N M k z

/-- At half-integer ideal counts, the error relative to the next integer is at most `N * 2⁻ᵏ +
1`; at integer ideal counts, the error is at most `N * 2⁻ᵏ + 1/2`. -/
theorem nextS2CountReadout_boundaries (N M k : ℕ) (z : Fin M) :
    (∀ n : ℝ, (N : ℝ) * aeEstimate M z = n + 1 / 2 →
        |(nextS2CountReadout N M k z : ℝ) - (n + 1)| ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1) ∧
      (∀ n : ℝ, (N : ℝ) * aeEstimate M z = n →
        |(nextS2CountReadout N M k z : ℝ) - n| ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2) := by
  unfold nextS2CountReadout
  constructor
  · intro n h
    have herr := AmplitudeReadoutRefined.nextCountReadout_error N M k z
    rw [h] at herr
    rw [abs_le] at herr
    rw [abs_le]
    constructor <;> linarith
  · intro n h
    have herr := AmplitudeReadoutRefined.nextCountReadout_error N M k z
    rw [h] at herr
    rw [abs_le] at herr
    rw [abs_le]
    constructor <;> linarith

/-- Whenever `(8/9)^r < δ`, there exists a two-dimensional unitary source and rational payoff
with positive second moment whose second-plus-fourth moment exceeds the proposed pilot-tail
reserve. -/
theorem unknownSigma_tail_promise_necessary_s2
    (N : ℕ) (nu : ℝ) (hnu : 0 < nu) (δ : ℝ) (r : ℕ) (hδ : (8/9 : ℝ)^r < δ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2)
      (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (f : Fin 2 → ℚ),
      unknownSigmaSecondMoment A j hA f > 0 ∧
      unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        > (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r) :=
  AmplitudeReadoutRefined.unknownSigma_tail_promise_necessary N nu hnu δ r hδ

/-- For positive sample count and scale, the stated second-plus-fourth moment reserve bounds the
pilot bad-moment probability by `δ - (8/9)^r`. -/
theorem nextPilotBadMoment_mass_le_reserve_s2
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ)
    (N : ℕ) (nu : ℝ) (r : ℕ) (hN : 0 < N) (hnu : 0 < nu) (δ : ℝ)
    (hδ : (8/9 : ℝ)^r < δ)
    (hreserve : unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        ≤ (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) :
    (signedMeanSource A j hA).probEvent (L := N)
        (AmplitudeReadoutRefined.nextPilotBadMoment A j hA f N nu) ≤ δ - (8/9 : ℝ)^r :=
  AmplitudeReadoutRefined.nextPilotBadMoment_mass_le_reserve A j hA f N nu r hN hnu δ hδ hreserve

/-- For a positive population size, the initial exact-counting grid has size at least two. -/
theorem exactCountM₀_ge_two_s2 {N : ℕ} (hN : 0 < N) : 2 ≤ exactCountM₀ N :=
  AmplitudeReadoutRefined.exactCountM₀_ge_two hN

/-- The exact-counting grid chosen from two initial amplitude estimates has size at least two
for a positive population size. -/
theorem exactCountGrid_ge_two_on_estimates_s2 {N : ℕ} (hN : 0 < N)
    (z₁ z₂ : Fin (exactCountM₀ N)) :
    2 ≤ exactCountGrid N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁)
      ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) :=
  AmplitudeReadoutRefined.exactCountGrid_ge_two_on_estimates hN z₁ z₂

end SearchEstimationCore
end Qatlib.Papers.FixedPtSearch14.FixedPoint
