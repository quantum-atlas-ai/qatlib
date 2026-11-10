/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefinedDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchEstimation
set_option warningAsError false
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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint
namespace SearchEstimationCore

variable {I : Type} [Fintype I] [DecidableEq I]

def nextS2LabelRecord (M k : ℕ) (z : Fin M) : ℚ :=
  AmplitudeReadoutRefined.nextLabelRecord M k z

noncomputable def nextS2CountReadout (N M k : ℕ) (z : Fin M) : ℤ :=
  AmplitudeReadoutRefined.nextCountReadout N M k z

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

theorem nextS2CountReadout_valid (N M k : ℕ) (z : Fin M) :
    0 ≤ nextS2CountReadout N M k z ∧ nextS2CountReadout N M k z ≤ N := by
  rw [nextS2CountReadout]
  exact AmplitudeReadoutRefined.nextCountReadout_valid N M k z

theorem nextS2CountReadout_error (N M k : ℕ) (z : Fin M) :
    |(nextS2CountReadout N M k z : ℝ) - (N : ℝ) * aeEstimate M z|
      ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 := by
  rw [nextS2CountReadout]
  exact AmplitudeReadoutRefined.nextCountReadout_error N M k z

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

theorem unknownSigma_tail_promise_necessary_s2
    (N : ℕ) (nu : ℝ) (hnu : 0 < nu) (δ : ℝ) (r : ℕ) (hδ : (8/9 : ℝ)^r < δ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2)
      (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (f : Fin 2 → ℚ),
      unknownSigmaSecondMoment A j hA f > 0 ∧
      unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        > (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r) :=
  AmplitudeReadoutRefined.unknownSigma_tail_promise_necessary N nu hnu δ r hδ

theorem nextPilotBadMoment_mass_le_reserve_s2
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ)
    (N : ℕ) (nu : ℝ) (r : ℕ) (hN : 0 < N) (hnu : 0 < nu) (δ : ℝ)
    (hδ : (8/9 : ℝ)^r < δ)
    (hreserve : unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        ≤ (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) :
    (signedMeanSource A j hA).probEvent (L := N)
        (AmplitudeReadoutRefined.nextPilotBadMoment A j hA f N nu) ≤ δ - (8/9 : ℝ)^r :=
  AmplitudeReadoutRefined.nextPilotBadMoment_mass_le_reserve A j hA f N nu r hN hnu δ hδ hreserve

theorem exactCountM₀_ge_two_s2 {N : ℕ} (hN : 0 < N) : 2 ≤ exactCountM₀ N :=
  AmplitudeReadoutRefined.exactCountM₀_ge_two hN

theorem exactCountGrid_ge_two_on_estimates_s2 {N : ℕ} (hN : 0 < N)
    (z₁ z₂ : Fin (exactCountM₀ N)) :
    2 ≤ exactCountGrid N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁)
      ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) :=
  AmplitudeReadoutRefined.exactCountGrid_ge_two_on_estimates hN z₁ z₂

end SearchEstimationCore
end Qatlib.Papers.FixedPtSearch14.FixedPoint
