/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Quantum mean estimation with pilot-selected precision

This module combines independent pilot samples with median-amplified signed mean estimation when
the variance is initially unknown. `unknownSigmaLaw` records the pilot and the trials at the
selected precision, while moment concentration controls failure and expected access costs in the
quantum Monte Carlo setting of [Montanaro2015].

## Main statements

* `unknownSigma_failure_bound`: the combined pilot and median failure bound.
* `unknownSigma_resources_eq`: the exact resource ledger at the selected precision.
* `unknownSigma_expected_accesses_le`: an expected-access bound using good-pilot and worst-case
  precision bounds.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PilotVariance

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
set_option warningAsError false

/-- The law of `N` independent pilot samples from the prepared signed-mean source. -/
noncomputable def unknownSigmaPilotLaw
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (N : ℕ) : FinDist (Fin N → I) :=
  independentSampleLaw (fun _ => signedMeanSource A j hA)

/-- The pilot-selected precision represented as an element of `Fin K` using the supplied uniform
upper bound. -/
def unknownSigmaPilotIndex (N h : ℕ) (f : I → ℚ) (nu eps : ℚ)
    (K : ℕ) (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K) (ω : Fin N → I) : Fin K :=
  ⟨pilotPrecision N h f nu eps ω, hk ω⟩

/-- The record of `2 * r + 1` signed-mean trials at precision `k`, each containing a source
sample and two layer records. -/
abbrev unknownSigmaTrialRecord (I : Type) [Fintype I] [DecidableEq I] (r : ℕ) (k : ℕ) : Type :=
  Fin (2*r+1) → (I × (LayerRecord k × LayerRecord k))

/-- The dependent full record containing a precision index, pilot samples, and signed-mean trial
records at that precision. -/
abbrev unknownSigmaFullRecord (I : Type) [Fintype I] [DecidableEq I] (N K r : ℕ) : Type :=
  Sigma (fun k : Fin K => (Fin N → I) × (unknownSigmaTrialRecord I r k.val))

/-- The law of one signed-mean trial at precision `k` using the scale selected by the pilot
record. -/
noncomputable def unknownSigmaTrialLaw
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (k : Fin K) (ωp : Fin N → I) :
    FinDist (I × (LayerRecord k.val × LayerRecord k.val)) :=
  signedMeanLaw k.val A j (fun i => (f i : ℝ)) (pilotScale N h f nu ωp) hA

/-- The joint weight of a precision, pilot record, and repeated-trial record, with zero weight
unless the precision equals the pilot-selected index. -/
noncomputable def unknownSigmaProbAt
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (k : Fin K) (ωp : Fin N → I) (ωt : unknownSigmaTrialRecord I r k.val) : ℝ :=
  (unknownSigmaPilotLaw A j hA N).prob ωp *
    (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
      (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt
    else 0)

/-- The probability weight of a full pilot-and-trial record. -/
noncomputable def unknownSigmaProb
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (rec : unknownSigmaFullRecord I N K r) : ℝ :=
  unknownSigmaProbAt A j hA f nu eps N h K r hk rec.1 rec.2.1 rec.2.2

/-- The normalized finite distribution on full records obtained by sampling the pilot and then
independent trials at its selected precision. -/
noncomputable def unknownSigmaLaw
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K) :
    FinDist (unknownSigmaFullRecord I N K r) where
  prob rec := unknownSigmaProb A j hA f nu eps N h K r hk rec
  nonneg rec := by
    refine mul_nonneg ((unknownSigmaPilotLaw A j hA N).nonneg _) ?_
    by_cases hc : rec.1 = unknownSigmaPilotIndex N h f nu eps K hk rec.2.1
    · rw [if_pos hc]
      exact Finset.prod_nonneg fun t _ =>
        (unknownSigmaTrialLaw A j hA f nu eps N h K r hk rec.1 rec.2.1).nonneg _
    · rw [if_neg hc]
  sum_one := by
    classical
    have htrials (k : Fin K) (ωp : Fin N → I) :
        (∑ ωt : unknownSigmaTrialRecord I r k.val,
          (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt) = 1 :=
      (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).sum_probOf (2*r+1)
    have h1 : (∑ rec : unknownSigmaFullRecord I N K r,
          unknownSigmaProb A j hA f nu eps N h K r hk rec)
        = ∑ k : Fin K, ∑ (ωp : Fin N → I),
            ∑ ωt : unknownSigmaTrialRecord I r k.val,
              unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt := by
      rw [show (∑ rec : unknownSigmaFullRecord I N K r,
            unknownSigmaProb A j hA f nu eps N h K r hk rec)
          = ∑ rec : unknownSigmaFullRecord I N K r,
            unknownSigmaProb A j hA f nu eps N h K r hk ⟨rec.1, rec.2⟩ from rfl]
      rw [Fintype.sum_sigma' (fun k y => unknownSigmaProb A j hA f nu eps N h K r hk ⟨k, y⟩)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun ωp _ => Finset.sum_congr rfl fun ωt _ => rfl
    have h2 : (∑ k : Fin K, ∑ (ωp : Fin N → I),
            ∑ ωt : unknownSigmaTrialRecord I r k.val,
              unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt)
        = ∑ ωp : Fin N → I, ∑ k : Fin K, (unknownSigmaPilotLaw A j hA N).prob ωp *
            (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then 1 else 0) := by
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin K)))
        (t := (Finset.univ : Finset (Fin N → I)))]
      refine Finset.sum_congr rfl fun ωp _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hc : k = unknownSigmaPilotIndex N h f nu eps K hk ωp
      · simp only [if_pos hc]
        unfold unknownSigmaProbAt
        simp only [if_pos hc]
        rw [← Finset.mul_sum]
        rw [htrials k ωp]
      · simp only [if_neg hc]
        unfold unknownSigmaProbAt
        simp only [if_neg hc]
        simp
    calc
      (∑ rec : unknownSigmaFullRecord I N K r,
          unknownSigmaProb A j hA f nu eps N h K r hk rec)
          = ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp * 1 := by
            rw [h1, h2]
            refine Finset.sum_congr rfl fun ωp _ => ?_
            have hstep : (∑ k : Fin K, (unknownSigmaPilotLaw A j hA N).prob ωp *
                (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then 1 else 0))
                = (unknownSigmaPilotLaw A j hA N).prob ωp * 1 := by
              rw [← Finset.mul_sum]
              rw [Fintype.sum_ite_eq' (unknownSigmaPilotIndex N h f nu eps K hk ωp)
                (fun _ => (1 : ℝ))]
            rw [hstep]
      _ = 1 := by
            simp only [mul_one]
            exact (unknownSigmaPilotLaw A j hA N).sum_one

/-- The median signed-mean estimate computed from the trial records using their precision and
pilot-selected scale. -/
noncomputable def unknownSigmaEstimate
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (rec : unknownSigmaFullRecord I N K r) : ℝ :=
  signedMeanMedian rec.1.val r (fun i => (f i : ℝ))
    (pilotScale N h f nu rec.2.1) rec.2.2

/-- The absolute deviation of the median signed-mean estimate from the source expectation. -/
noncomputable def unknownSigmaDeviation
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (k : Fin K) (ωp : Fin N → I) (ωt : unknownSigmaTrialRecord I r k.val) : ℝ :=
  |signedMeanMedian k.val r (fun i => (f i : ℝ)) (pilotScale N h f nu ωp) ωt -
    (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|

/-- The event that the median signed-mean estimate differs from the source expectation by more
than `eps`. -/
def unknownSigmaFails
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (rec : unknownSigmaFullRecord I N K r) : Prop :=
  (eps : ℝ) < unknownSigmaDeviation A j hA f nu eps N h K r hk rec.1 rec.2.1 rec.2.2

/-- The conditional failure mass of the repeated-trial estimate for a fixed precision and pilot
record. -/
noncomputable def unknownSigmaTrialFail
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (k : Fin K) (ωp : Fin N → I) : ℝ :=
  ∑ ωt : unknownSigmaTrialRecord I r k.val,
    (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
    (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then 1 else 0)

/-- For bounded `f`, positive pilot size and accuracy parameters, and `0 < nu ≤ 1/4`, the
failure mass is at most `(8/9)^r + 2 / (N * nu^2)`. -/
theorem unknownSigma_failure_bound
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
      (unknownSigmaFails A j hA f nu eps N h K r hk)
      ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) := by
  classical
  have hmass0 : SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (unknownSigmaFails A j hA f nu eps N h K r hk)
      = ∑ rec : unknownSigmaFullRecord I N K r,
          (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
            (if unknownSigmaFails A j hA f nu eps N h K r hk rec then (1 : ℝ) else 0) := by
    unfold SignedMean.mass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun rec _ => ?_
    by_cases he : unknownSigmaFails A j hA f nu eps N h K r hk rec
    · rw [if_pos he, if_pos he]; ring
    · rw [if_neg he, if_neg he]; ring
  have hmass1 : (∑ rec : unknownSigmaFullRecord I N K r,
          (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
            (if unknownSigmaFails A j hA f nu eps N h K r hk rec then (1 : ℝ) else 0))
      = ∑ k : Fin K, ∑ (ωp : Fin N → I), ∑ ωt : unknownSigmaTrialRecord I r k.val,
          unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0) := by
    rw [show (∑ rec : unknownSigmaFullRecord I N K r,
            (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
              (if unknownSigmaFails A j hA f nu eps N h K r hk rec then (1 : ℝ) else 0))
          = ∑ rec : unknownSigmaFullRecord I N K r,
            (unknownSigmaLaw A j hA f nu eps N h K r hk).prob ⟨rec.1, rec.2⟩ *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨rec.1, rec.2⟩ then (1 : ℝ) else 0) from rfl]
    rw [Fintype.sum_sigma' (fun k y =>
        (unknownSigmaLaw A j hA f nu eps N h K r hk).prob ⟨k, y⟩ *
          (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, y⟩ then (1 : ℝ) else 0))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  have hinner (ωp : Fin N → I) (k : Fin K) :
      (∑ ωt : unknownSigmaTrialRecord I r k.val,
          unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
      = (unknownSigmaPilotLaw A j hA N).prob ωp *
          (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
            unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp else (0 : ℝ)) := by
    by_cases hc : k = unknownSigmaPilotIndex N h f nu eps K hk ωp
    · simp only [if_pos hc]
      unfold unknownSigmaProbAt
      simp only [if_pos hc]
      have hteq : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
          = unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp := by
        unfold unknownSigmaTrialFail
        rfl
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      rw [hteq]
    · simp only [if_neg hc]
      unfold unknownSigmaProbAt
      simp only [if_neg hc]
      simp
  have htrial_le_one (k : Fin K) (ωp : Fin N → I) :
      unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp ≤ 1 := by
    have h1 : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
          = ∑ ωt : unknownSigmaTrialRecord I r k.val,
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then
              (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt else (0 : ℝ)) := by
      refine Finset.sum_congr rfl fun ωt _ => ?_
      by_cases hh : unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩
      · rw [if_pos hh, if_pos hh]; ring
      · rw [if_neg hh, if_neg hh]; ring
    calc
      unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp
        = ∑ ωt : unknownSigmaTrialRecord I r k.val,
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then
              (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt else (0 : ℝ)) := by
          unfold unknownSigmaTrialFail
          exact h1
        _ ≤ ∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt := by
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ωt _ _ =>
            Finset.prod_nonneg fun i _ =>
              (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).nonneg (ωt i))
        _ = 1 := (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).sum_probOf (2*r+1)
  have hgood (k : Fin K) (ωp : Fin N → I)
      (hc : k = unknownSigmaPilotIndex N h f nu eps K hk ωp)
      (hg : (pilotScale N h f nu ωp : ℝ)^2 ≥
        (signedMeanSource A j hA).variance (fun i => (f i : ℝ))) :
      unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp ≤ (8/9 : ℝ)^r := by
    have hk4 : 4 ≤ k.val := by
      have hh := (unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps ωp
        hN hf hnu hnu1 heps).1
      have hh' : 4 ≤ (unknownSigmaPilotIndex N h f nu eps K hk ωp).val := by
        simpa [unknownSigmaPilotIndex] using! hh
      rw [hc]
      exact hh'
    have hpos : 0 < (pilotScale N h f nu ωp : ℝ) := by
      have hh := (unknown_variance_pilot_native_moments_and_scale I N h f nu ωp
        hN hf hnu hnu1).2.2.2.2.1
      simpa [pilotScale] using! hh
    have hprec : 8*(pilotScale N h f nu ωp : ℝ)*(1/2 : ℝ)^k.val ≤ (eps : ℝ) := by
      have hh := (unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps ωp
        hN hf hnu hnu1 heps).2.1
      have hh' : 8*(pilotScale N h f nu ωp : ℝ)*(1/2 : ℝ)^(unknownSigmaPilotIndex N h f nu eps K hk ωp).val
          ≤ (eps : ℝ) := by
        simpa [unknownSigmaPilotIndex] using! hh
      rw [hc]
      exact hh'
    have hvar : (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
        ≤ (pilotScale N h f nu ωp : ℝ)^2 := hg
    have hmed := signed_centered_fresh_median_failure I k.val r
      A j (fun i => (f i : ℝ)) (pilotScale N h f nu ωp) hA hk4 hpos hvar
    (try dsimp only at hmed)
    have hsub : ∀ ωt : unknownSigmaTrialRecord I r k.val,
        unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ →
        8*(pilotScale N h f nu ωp : ℝ)*(1/2 : ℝ)^k.val <
          unknownSigmaDeviation A j hA f nu eps N h K r hk k ωp ωt := by
      intro ωt hω
      unfold unknownSigmaFails at hω
      simp only [unknownSigmaDeviation] at hω
      unfold unknownSigmaDeviation
      linarith
    have htf : unknownSigmaTrialFail A j hA f nu eps N h K r hk k ωp
        = (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0)) := by
      unfold unknownSigmaTrialFail
      rfl
    have hfilter : Finset.univ.filter
          (fun ωt : unknownSigmaTrialRecord I r k.val =>
            unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩)
        ⊆ Finset.univ.filter
          (fun ωt : unknownSigmaTrialRecord I r k.val =>
            8*(pilotScale N h f nu ωp : ℝ)*(1/2 : ℝ)^k.val <
              unknownSigmaDeviation A j hA f nu eps N h K r hk k ωp ωt) := by
      intro ωt hωt
      have hmem := Finset.mem_filter.mp hωt
      exact Finset.mem_filter.mpr ⟨hmem.1, hsub ωt hmem.2⟩
    have hle : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
        ≤ (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probEvent
            (fun ωt : unknownSigmaTrialRecord I r k.val =>
              8*(pilotScale N h f nu ωp : ℝ)*(1/2 : ℝ)^k.val <
                unknownSigmaDeviation A j hA f nu eps N h K r hk k ωp ωt) := by
      have h1 : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
          = ∑ ωt : unknownSigmaTrialRecord I r k.val,
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then
              (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt else (0 : ℝ)) := by
        refine Finset.sum_congr rfl fun ωt _ => ?_
        by_cases hh : unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩
        · rw [if_pos hh, if_pos hh]; ring
        · rw [if_neg hh, if_neg hh]; ring
      rw [h1, ← Finset.sum_filter]
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      refine Finset.sum_le_sum_of_subset_of_nonneg hfilter (fun ωt _ _ =>
        Finset.prod_nonneg fun i _ =>
          (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).nonneg (ωt i))
    rw [htf]
    exact hle.trans hmed
  have hbad :=
      unknown_variance_pilot_actual_born_certificate_failure I A j N h f nu hA hN hf hnu hnu1
  have hbad' : (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
        (pilotScale N h f nu ωp : ℝ)^2 <
          (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
        (unknownSigmaPilotLaw A j hA N).prob ωp) ≤ 2/((N : ℝ)*(nu : ℝ)^2) := by
    simpa [unknownSigmaPilotLaw, independentSampleLaw,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf] using! hbad
  calc
    SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (unknownSigmaFails A j hA f nu eps N h K r hk)
      = ∑ k : Fin K, ∑ (ωp : Fin N → I), ∑ ωt : unknownSigmaTrialRecord I r k.val,
          unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
            (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0) := by
        rw [hmass0, hmass1]
    _ ≤ ∑ (ωp : Fin N → I), (unknownSigmaPilotLaw A j hA N).prob ωp *
          (if (pilotScale N h f nu ωp : ℝ)^2 ≥
              (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
            then (8/9 : ℝ)^r else 1) := by
        have hstep1 : (∑ k : Fin K, ∑ (ωp : Fin N → I), ∑ ωt : unknownSigmaTrialRecord I r k.val,
              unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
                (if unknownSigmaFails A j hA f nu eps N h K r hk ⟨k, (ωp, ωt)⟩ then (1 : ℝ) else 0))
            ≤ ∑ k : Fin K, ∑ (ωp : Fin N → I), (unknownSigmaPilotLaw A j hA N).prob ωp *
                (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
                  (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                      (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                    then (8/9 : ℝ)^r else 1) else (0 : ℝ)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine Finset.sum_le_sum fun ωp _ => ?_
          rw [hinner ωp k]
          by_cases hc : k = unknownSigmaPilotIndex N h f nu eps K hk ωp
          · simp only [if_pos hc]
            by_cases hg : (pilotScale N h f nu ωp : ℝ)^2 ≥
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
            · simp only [if_pos hg]
              exact mul_le_mul_of_nonneg_left (hgood k ωp hc hg)
                ((unknownSigmaPilotLaw A j hA N).nonneg ωp)
            · simp only [if_neg hg]
              exact mul_le_mul_of_nonneg_left (htrial_le_one k ωp)
                ((unknownSigmaPilotLaw A j hA N).nonneg ωp)
          · simp only [if_neg hc]
            simp
        have hswap : (∑ k : Fin K, ∑ (ωp : Fin N → I), (unknownSigmaPilotLaw A j hA N).prob ωp *
                (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
                  (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                      (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                    then (8/9 : ℝ)^r else 1) else (0 : ℝ)))
            = ∑ (ωp : Fin N → I), (unknownSigmaPilotLaw A j hA N).prob ωp *
                (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                  then (8/9 : ℝ)^r else 1) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ωp _ => ?_
          rw [← Finset.mul_sum]
          rw [Fintype.sum_ite_eq' (unknownSigmaPilotIndex N h f nu eps K hk ωp)
            (fun _ => if (pilotScale N h f nu ωp : ℝ)^2 ≥
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
              then (8/9 : ℝ)^r else 1)]
        exact hstep1.trans_eq hswap
    _ = (8/9 : ℝ)^r * (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
              (pilotScale N h f nu ωp : ℝ)^2 ≥
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
              (unknownSigmaPilotLaw A j hA N).prob ωp)
        + (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
              (pilotScale N h f nu ωp : ℝ)^2 <
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
              (unknownSigmaPilotLaw A j hA N).prob ωp) := by
        have h1 : (∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp *
              (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                then (8/9 : ℝ)^r else 1))
            = ∑ ωp : Fin N → I,
                ((if (pilotScale N h f nu ωp : ℝ)^2 ≥
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                  then (8/9 : ℝ)^r * (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))
                  + (if (pilotScale N h f nu ωp : ℝ)^2 <
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                  then (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))) := by
          refine Finset.sum_congr rfl fun ωp _ => ?_
          by_cases hg : (pilotScale N h f nu ωp : ℝ)^2 ≥
              (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
          · rw [if_pos hg, if_pos hg, if_neg (by exact not_lt_of_ge hg)]; ring
          · rw [if_neg hg, if_neg hg, if_pos (lt_of_not_ge hg)]; ring
        rw [h1, Finset.sum_add_distrib]
        have ha : (∑ ωp : Fin N → I, (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
              then (8/9 : ℝ)^r * (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ)))
            = (8/9 : ℝ)^r * (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                (pilotScale N h f nu ωp : ℝ)^2 ≥
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                (unknownSigmaPilotLaw A j hA N).prob ωp) := by
          calc
            (∑ ωp : Fin N → I, (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                then (8/9 : ℝ)^r * (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ)))
                = ∑ ωp : Fin N → I, ((8/9 : ℝ)^r *
                  (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                      (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                    then (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))) := by
                  refine Finset.sum_congr rfl fun ωp _ => ?_
                  by_cases hg : (pilotScale N h f nu ωp : ℝ)^2 ≥
                      (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                  · rw [if_pos hg, if_pos hg]
                  · rw [if_neg hg, if_neg hg]
                    ring
            _ = (8/9 : ℝ)^r * (∑ ωp : Fin N → I, (if (pilotScale N h f nu ωp : ℝ)^2 ≥
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                then (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))) := by
                  rw [Finset.mul_sum]
            _ = (8/9 : ℝ)^r * (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                  (pilotScale N h f nu ωp : ℝ)^2 ≥
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                  (unknownSigmaPilotLaw A j hA N).prob ωp) := by
                  rw [← Finset.sum_filter]
        have hb : (∑ ωp : Fin N → I, (if (pilotScale N h f nu ωp : ℝ)^2 <
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
                then (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ)))
            = ∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                  (pilotScale N h f nu ωp : ℝ)^2 <
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                (unknownSigmaPilotLaw A j hA N).prob ωp := by
          rw [← Finset.sum_filter]
        rw [ha, hb]
    _ ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) := by
        have hpow : (0 : ℝ) ≤ (8/9 : ℝ)^r := by positivity
        have hgoodmass : (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
              (pilotScale N h f nu ωp : ℝ)^2 ≥
                (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
              (unknownSigmaPilotLaw A j hA N).prob ωp) ≤ 1 := by
          calc
            (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                (pilotScale N h f nu ωp : ℝ)^2 ≥
                  (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                (unknownSigmaPilotLaw A j hA N).prob ωp)
                ≤ ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _) (fun ωp _ _ =>
                  (unknownSigmaPilotLaw A j hA N).nonneg ωp)
            _ = 1 := (unknownSigmaPilotLaw A j hA N).sum_one
        have hstep : (8/9 : ℝ)^r *
                (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                  (pilotScale N h f nu ωp : ℝ)^2 ≥
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                  (unknownSigmaPilotLaw A j hA N).prob ωp)
              + (∑ ωp ∈ Finset.univ.filter (fun ωp : Fin N → I =>
                  (pilotScale N h f nu ωp : ℝ)^2 <
                    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))),
                  (unknownSigmaPilotLaw A j hA N).prob ωp)
              ≤ (8/9 : ℝ)^r * 1 + 2/((N : ℝ)*(nu : ℝ)^2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hgoodmass hpow) hbad'
        simpa using! hstep

/-- If the combined pilot and median failure bound is at most `δ ∈ (0, 1)`, the estimate
succeeds with probability at least `1 - δ` under the stated boundedness assumptions. -/
theorem unknownSigma_success_bound
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) ≤ δ) :
    SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
      (fun rec => ¬ unknownSigmaFails A j hA f nu eps N h K r hk rec)
      ≥ 1 - δ := by
  have hcomp := SignedMean.mass_complement (unknownSigmaLaw A j hA f nu eps N h K r hk)
    (unknownSigmaFails A j hA f nu eps N h K r hk)
  have hfail : SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
      (unknownSigmaFails A j hA f nu eps N h K r hk)
      ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) :=
    unknownSigma_failure_bound A j hA f nu eps N h K r hk hN hf hnu hnu1 heps
  linarith

/-- The second raw moment of `f` under the prepared signed-mean source. -/
noncomputable def unknownSigmaSecondMoment (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) : ℝ :=
  (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)

/-- The fourth raw moment of `f` under the prepared signed-mean source. -/
noncomputable def unknownSigmaFourthMoment (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) : ℝ :=
  (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^4)

/-- The probability of the union of two events on independent sample records is at most the sum
of their probabilities. -/
theorem unknownSigma_probEvent_union {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E F : (Fin L → X) → Prop) :
    p.probEvent (L := L) (fun ω => E ω ∨ F ω)
      ≤ p.probEvent (L := L) E + p.probEvent (L := L) F := by
  classical
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  have h2 : (∑ ω : Fin L → X, (if E ω ∨ F ω then p.probOf ω else 0))
      ≤ ∑ ω : Fin L → X, ((if E ω then p.probOf ω else 0)
          + (if F ω then p.probOf ω else 0)) := by
    refine Finset.sum_le_sum fun ω _ => ?_
    have hnn : 0 ≤ p.probOf ω := Finset.prod_nonneg fun i _ => p.nonneg _
    by_cases hE : E ω
    · by_cases hF : F ω
      · rw [if_pos (Or.inr hF), if_pos hF, if_pos hE]; linarith
      · rw [if_pos (Or.inl hE), if_neg hF, if_pos hE]; linarith
    · by_cases hF : F ω
      · rw [if_pos (Or.inr hF), if_neg hE, if_pos hF]; linarith
      · rw [if_neg (not_or.mpr ⟨hE, hF⟩), if_neg hE, if_neg hF]; linarith
  rw [Finset.sum_add_distrib] at h2
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Finset.sum_filter]
  exact h2

/-- If `|f i| ≤ 1` for every source label, its second and fourth raw moments are each at most
one. -/
theorem unknownSigma_bounded_moments
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (hf : ∀ i, |f i| ≤ 1) :
    unknownSigmaSecondMoment A j hA f ≤ 1 ∧ unknownSigmaFourthMoment A j hA f ≤ 1 := by
  have hfr : ∀ i : I, |(f i : ℝ)| ≤ 1 := fun i => by exact_mod_cast hf i
  have hsq (i : I) : (f i : ℝ)^2 ≤ 1 := by
    have h1 := abs_le.mp (hfr i)
    nlinarith
  have hquartic (i : I) : (f i : ℝ)^4 ≤ 1 := by
    have h1 := abs_le.mp (hfr i)
    have h2 : (f i : ℝ)^2 ≤ 1 := by nlinarith
    have h3 : (0 : ℝ) ≤ (f i : ℝ)^2 := sq_nonneg _
    nlinarith
  constructor
  · unfold unknownSigmaSecondMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    calc
      (∑ i, (signedMeanSource A j hA).prob i * (f i : ℝ)^2)
          ≤ ∑ i, (signedMeanSource A j hA).prob i * 1 := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul_of_nonneg_left (hsq i) ((signedMeanSource A j hA).nonneg i)
      _ = 1 := by simpa using! (signedMeanSource A j hA).sum_one
  · unfold unknownSigmaFourthMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    calc
      (∑ i, (signedMeanSource A j hA).prob i * (f i : ℝ)^4)
          ≤ ∑ i, (signedMeanSource A j hA).prob i * 1 := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul_of_nonneg_left (hquartic i) ((signedMeanSource A j hA).nonneg i)
      _ = 1 := by simpa using! (signedMeanSource A j hA).sum_one

/-- The variance of `f` under the source distribution is at most its second raw moment. -/
theorem unknownSigma_variance_le_second_moment
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) :
    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
      ≤ unknownSigmaSecondMoment A j hA f := by
  have h := SignedMean.shifted_second_moment (signedMeanSource A j hA)
    (fun i => (f i : ℝ)) 0
  simp only [sub_zero] at h
  change (∑ i, (signedMeanSource A j hA).prob i * (f i : ℝ)^2) = _ at h
  unfold unknownSigmaSecondMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  rw [h]
  nlinarith [sq_nonneg ((signedMeanSource A j hA).expect (fun i => (f i : ℝ)))]

/-- The square of the source variance of `f` is at most its fourth raw moment. -/
theorem unknownSigma_fourth_moment_ge_variance_sq
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) :
    (signedMeanSource A j hA).variance (fun i => (f i : ℝ))^2
      ≤ unknownSigmaFourthMoment A j hA f := by
  have hvar : (signedMeanSource A j hA).variance (fun i => (f i : ℝ))
      ≤ (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2) := by
    have hh := unknownSigma_variance_le_second_moment A j hA f
    rwa [unknownSigmaSecondMoment] at hh
  have hvar0 : 0 ≤ (signedMeanSource A j hA).variance (fun i => (f i : ℝ)) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((signedMeanSource A j hA).nonneg i) (sq_nonneg _)
  have hsq : ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))^2
      ≤ ((signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2))^2 := by
    have hba : 0 ≤ (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)
        - (signedMeanSource A j hA).variance (fun i => (f i : ℝ)) := by linarith
    have hsum : 0 ≤ (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)
        + (signedMeanSource A j hA).variance (fun i => (f i : ℝ)) := by linarith
    nlinarith [mul_nonneg hba hsum]
  have h := SignedMean.shifted_second_moment (signedMeanSource A j hA) (fun i => (f i : ℝ)^2) 0
  simp only [sub_zero] at h
  have heq : (∑ i, (signedMeanSource A j hA).prob i * (f i : ℝ)^4)
      = ∑ i, (signedMeanSource A j hA).prob i * ((f i : ℝ)^2)^2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold unknownSigmaFourthMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  rw [heq, h]
  have hnonneg : 0 ≤ (signedMeanSource A j hA).variance (fun i => (f i : ℝ)^2) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((signedMeanSource A j hA).nonneg i) (sq_nonneg _)
  nlinarith [hsq, hnonneg]

/-- For positive pilot size and tolerance, the probability that either empirical first or second
moment exceeds its tolerance is at most the sum of the second and fourth moments divided by
`N * nu^2`. -/
theorem unknownSigma_pilot_moment_failure_mass
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (N : ℕ) (nu : ℝ) (hN : 0 < N) (hnu : 0 < nu) :
    (signedMeanSource A j hA).probEvent (L := N)
      (fun ωp : Fin N → I =>
        (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
            - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ∨
        (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
            - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|)
      ≤ (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
          / ((N : ℝ)*(nu : ℝ)^2) := by
  have h1 : (signedMeanSource A j hA).probEvent (L := N)
      (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
          - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|)
      ≤ unknownSigmaSecondMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2) := by
    calc
      _ ≤ (signedMeanSource A j hA).variance (fun i => (f i : ℝ)) / ((N : ℝ)*(nu : ℝ)^2) :=
        (signedMeanSource A j hA).chebyshev_avg (fun i => (f i : ℝ)) hN nu hnu
      _ ≤ unknownSigmaSecondMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2) :=
        div_le_div_of_nonneg_right (unknownSigma_variance_le_second_moment A j hA f)
          (by positivity)
  have h2 : (signedMeanSource A j hA).probEvent (L := N)
      (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
          - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|)
      ≤ unknownSigmaFourthMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2) := by
    have hle : (signedMeanSource A j hA).variance (fun i => (f i : ℝ)^2)
        ≤ unknownSigmaFourthMoment A j hA f := by
      have h := SignedMean.shifted_second_moment (signedMeanSource A j hA)
        (fun i => (f i : ℝ)^2) 0
      simp only [sub_zero] at h
      have heq : (∑ i, (signedMeanSource A j hA).prob i * (f i : ℝ)^4)
          = ∑ i, (signedMeanSource A j hA).prob i * ((f i : ℝ)^2)^2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      unfold unknownSigmaFourthMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
      rw [heq, h]
      nlinarith [sq_nonneg ((signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2))]
    calc
      _ ≤ (signedMeanSource A j hA).variance (fun i => (f i : ℝ)^2) / ((N : ℝ)*(nu : ℝ)^2) :=
        (signedMeanSource A j hA).chebyshev_avg (fun i => (f i : ℝ)^2) hN nu hnu
      _ ≤ unknownSigmaFourthMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2) :=
        div_le_div_of_nonneg_right hle (by positivity)
  have hu := unknownSigma_probEvent_union (signedMeanSource A j hA)
    (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
        - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|)
    (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
        - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|)
  calc
    (signedMeanSource A j hA).probEvent (L := N)
        (fun ωp : Fin N → I =>
          (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ∨
          (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|)
      ≤ (signedMeanSource A j hA).probEvent (L := N)
          (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|)
        + (signedMeanSource A j hA).probEvent (L := N)
          (fun ωp : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|) := hu
    _ ≤ unknownSigmaSecondMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2)
        + unknownSigmaFourthMoment A j hA f / ((N : ℝ)*(nu : ℝ)^2) :=
      add_le_add h1 h2
    _ = (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
        / ((N : ℝ)*(nu : ℝ)^2) := by ring

/-- The scale bound `sqrt (sigmaSq + 6 * nu) + 2 / 2^h` for a pilot with controlled moment
errors. -/
noncomputable def unknownSigmaScaleBound (sigmaSq nu h : ℝ) : ℝ :=
  Real.sqrt (sigmaSq + 6*nu) + 2/(2:ℝ)^h

/-- The precision bound, with minimum four, computed from the good-pilot scale bound and target
error. -/
noncomputable def unknownSigmaGoodPrecision (sigmaSq nu h eps : ℝ) : ℕ :=
  max 4 (Nat.clog 2 ((Int.ceil ((8*unknownSigmaScaleBound sigmaSq nu h)/eps) : ℤ).toNat+1))

/-- The worst-case pilot precision bound, with minimum four, computed from the rational target
error. -/
def unknownSigmaWorstPrecision (eps : ℚ) : ℕ :=
  max 4 (Nat.clog 2 ((Int.ceil (16/eps) : ℤ).toNat+1))

/-- Componentwise comparison of all fields of two quantum-mean resource ledgers. -/
def unknownSigmaLedgerLe (a b : QuantumMeanResources) : Prop :=
  a.sourcePreparations ≤ b.sourcePreparations ∧ a.layerCopies ≤ b.layerCopies ∧
  a.measurements ≤ b.measurements ∧ a.layerForward ≤ b.layerForward ∧
  a.layerInverse ≤ b.layerInverse ∧ a.queries ≤ b.queries ∧ a.gates ≤ b.gates

/-- Componentwise addition of two quantum-mean resource ledgers. -/
def unknownSigmaAddResources (a b : QuantumMeanResources) : QuantumMeanResources :=
  ⟨a.sourcePreparations + b.sourcePreparations, a.layerCopies + b.layerCopies,
    a.measurements + b.measurements, a.layerForward + b.layerForward,
    a.layerInverse + b.layerInverse, a.queries + b.queries, a.gates + b.gates⟩

/-- The explicit resource ledger for `N` pilot samples and `2 * r + 1` signed-mean trials at
precision `k`. -/
noncomputable def unknownSigmaLedger (N r k : ℕ) : QuantumMeanResources :=
  let m := 2*r+1
  let q := (k+2)*(2*layerRepetitions k+1)
  ⟨N + m, m*(2*q), N + m*(1+2*q), m*(2*q*layerGrid k),
    m*(2*q*(layerGrid k-1)), m*(2*q*(layerGrid k-1)),
    N + m*(1+2*q*(5*(layerGrid k-1)+3))⟩

/-- The resources of a full execution record, adding pilot-sampling resources to those of the
signed-mean median trials. -/
noncomputable def unknownSigmaResources
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (rec : unknownSigmaFullRecord I N K r) : QuantumMeanResources :=
  unknownSigmaAddResources (meanProgramResources 0 N A [])
    (signedMeanMedianResources rec.1.val r A j
      (fun i => (rec.2.2 i).1) (fun i => (f i : ℝ)) (pilotScale N h f nu rec.2.1))

/-- The total number of source preparations and forward and inverse layer accesses in a resource
ledger. -/
def unknownSigmaAccesses (res : QuantumMeanResources) : ℕ :=
  res.sourcePreparations + res.layerForward + res.layerInverse

/-- The access count extracted from the explicit ledger at pilot size `N`, repetition parameter
`r`, and precision `k`. -/
noncomputable def unknownSigmaLedgerAccesses (N r k : ℕ) : ℕ :=
  unknownSigmaAccesses (unknownSigmaLedger N r k)

/-- The pilot event that the empirical first moment or empirical second moment differs from its
expectation by more than `nu`. -/
def unknownSigmaBadMoments (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (N : ℕ) (nu : ℝ)
    (ωp : Fin N → I) : Prop :=
  (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
      - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ∨
  (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
      - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|

/-- The pilot event that both empirical first and second moments differ from their expectations
by at most `nu`. -/
def unknownSigmaGoodMoments (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (N : ℕ) (nu : ℝ)
    (ωp : Fin N → I) : Prop :=
  |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
      - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ≤ nu ∧
  |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
      - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)| ≤ nu

/-- The good-pilot moment event is exactly the complement of the bad-pilot moment event. -/
theorem unknownSigma_good_iff_not_bad
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (N : ℕ) (nu : ℝ)
    (ωp : Fin N → I) :
    unknownSigmaGoodMoments A j hA f N nu ωp
      ↔ ¬ unknownSigmaBadMoments A j hA f N nu ωp := by
  constructor
  · intro hg hb
    rcases hb with hb | hb
    · exact (not_le_of_gt hb) hg.1
    · exact (not_le_of_gt hb) hg.2
  · intro hnb
    constructor
    · exact le_of_not_gt (fun hb => hnb (Or.inl hb))
    · exact le_of_not_gt (fun hb => hnb (Or.inr hb))

/-- The layer grid size is nondecreasing in precision. -/
theorem unknownSigma_layerGrid_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    layerGrid k₁ ≤ layerGrid k₂ := by
  unfold layerGrid
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega)) (by omega)

/-- The number of layer repetitions is nondecreasing in precision. -/
theorem unknownSigma_layerRepetitions_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    layerRepetitions k₁ ≤ layerRepetitions k₂ := by
  unfold layerRepetitions
  omega

/-- The explicit resource ledger is componentwise nondecreasing in precision. -/
theorem unknownSigma_ledger_mono {N r k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    unknownSigmaLedgerLe (unknownSigmaLedger N r k₁) (unknownSigmaLedger N r k₂) := by
  have hrep := unknownSigma_layerRepetitions_mono h
  have hgrid := unknownSigma_layerGrid_mono h
  have hgrid1 : layerGrid k₁ - 1 ≤ layerGrid k₂ - 1 := Nat.sub_le_sub_right hgrid 1
  have hq : (k₁+2)*(2*layerRepetitions k₁+1) ≤ (k₂+2)*(2*layerRepetitions k₂+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2q : 2*((k₁+2)*(2*layerRepetitions k₁+1)) ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1)) :=
    Nat.mul_le_mul (le_refl 2) hq
  have h2qg : 2*((k₁+2)*(2*layerRepetitions k₁+1))*layerGrid k₁
      ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1))*layerGrid k₂ :=
    Nat.mul_le_mul h2q hgrid
  have h2qg1 : 2*((k₁+2)*(2*layerRepetitions k₁+1))*(layerGrid k₁-1)
      ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1))*(layerGrid k₂-1) :=
    Nat.mul_le_mul h2q hgrid1
  have hgate : 5*(layerGrid k₁-1)+3 ≤ 5*(layerGrid k₂-1)+3 := by omega
  have h2qg5 : 2*((k₁+2)*(2*layerRepetitions k₁+1))*(5*(layerGrid k₁-1)+3)
      ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1))*(5*(layerGrid k₂-1)+3) :=
    Nat.mul_le_mul h2q hgate
  unfold unknownSigmaLedgerLe unknownSigmaLedger
  (try dsimp only)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul_left (2*r+1) h2q
  · exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (2*r+1) (Nat.add_le_add_left h2q 1)) N
  · exact Nat.mul_le_mul_left (2*r+1) h2qg
  · exact Nat.mul_le_mul_left (2*r+1) h2qg1
  · exact Nat.mul_le_mul_left (2*r+1) h2qg1
  · exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (2*r+1) (Nat.add_le_add_left h2qg5 1)) N

/-- The access count of the explicit ledger is nondecreasing in precision. -/
theorem unknownSigma_ledgerAccesses_mono {N r k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    unknownSigmaLedgerAccesses N r k₁ ≤ unknownSigmaLedgerAccesses N r k₂ := by
  have hrep := unknownSigma_layerRepetitions_mono h
  have hgrid := unknownSigma_layerGrid_mono h
  have hgrid1 : layerGrid k₁ - 1 ≤ layerGrid k₂ - 1 := Nat.sub_le_sub_right hgrid 1
  have hq : (k₁+2)*(2*layerRepetitions k₁+1) ≤ (k₂+2)*(2*layerRepetitions k₂+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2q : 2*((k₁+2)*(2*layerRepetitions k₁+1)) ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1)) :=
    Nat.mul_le_mul (le_refl 2) hq
  have h2qg : 2*((k₁+2)*(2*layerRepetitions k₁+1))*layerGrid k₁
      ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1))*layerGrid k₂ := Nat.mul_le_mul h2q hgrid
  have h2qg1 : 2*((k₁+2)*(2*layerRepetitions k₁+1))*(layerGrid k₁-1)
      ≤ 2*((k₂+2)*(2*layerRepetitions k₂+1))*(layerGrid k₂-1) := Nat.mul_le_mul h2q hgrid1
  unfold unknownSigmaLedgerAccesses unknownSigmaAccesses unknownSigmaLedger
  (try dsimp only)
  exact Nat.add_le_add
    (Nat.add_le_add (by omega) (Nat.mul_le_mul_left (2*r+1) h2qg))
    (Nat.mul_le_mul_left (2*r+1) h2qg1)

/-- The pilot-only mean program uses `N` source preparations, `N` measurements, and `N` gates,
with every layer and query count zero. -/
theorem unknownSigma_pilot_ledger (A : Matrix I I ℂ) (N : ℕ) :
    meanProgramResources 0 N A [] = ⟨N, 0, N, 0, 0, 0, N⟩ := by
  have hl := meanProgramResources_labels 0 N A []
  have hsrc : GateCount (List.replicate N (Step.gate A)) = N := hl.1
  apply QuantumMeanResources.ext
  · exact hsrc
  · simp [meanProgramResources]
  · simp [meanProgramResources]
  · simpa using! hl.2.1
  · simpa using! hl.2.2
  · simp [meanProgramResources]
  · simp [meanProgramResources, hsrc]

/-- The resources of each full record equal the explicit ledger at the record's precision. -/
theorem unknownSigma_resources_eq
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (rec : unknownSigmaFullRecord I N K r) :
    unknownSigmaResources A j hA f nu eps N h K r hk rec
      = unknownSigmaLedger N r rec.1.val := by
  have htrials := signed_centered_fresh_full_resources rec.1.val r A j
    (fun i => (rec.2.2 i).1) (fun i => (f i : ℝ)) (pilotScale N h f nu rec.2.1)
  (try dsimp only at htrials)
  unfold unknownSigmaResources
  rw [unknownSigmaAddResources, unknownSigma_pilot_ledger A N, htrials]
  simp only [Nat.zero_add]
  rfl

/-- Under the stated boundedness and parameter conditions, a good pilot selects precision at
most `unknownSigmaGoodPrecision` evaluated at the true source variance. -/
theorem unknownSigma_good_precision_le
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (ωp : Fin N → I)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (hg : unknownSigmaGoodMoments A j hA f N (nu : ℝ) ωp) :
    pilotPrecision N h f nu eps ωp
      ≤ unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
        (nu : ℝ) h (eps : ℝ) := by
  have hcert := unknown_variance_pilot_good_moments_certificate I (signedMeanSource A j hA)
    N h f nu ωp hN hf hnu hnu1
    (by have hm := pilotMoments_cast_avg N f ωp; rw [hm.1]; exact hg.1)
    (by have hm := pilotMoments_cast_avg N f ωp; rw [hm.2]; exact hg.2)
  have hepsR : (0 : ℝ) < eps := by exact_mod_cast heps
  have hscale : (pilotScale N h f nu ωp : ℝ)
      ≤ unknownSigmaScaleBound ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
        (nu : ℝ) h :=
    by simpa [unknownSigmaScaleBound] using! hcert.2
  have hxy : (8*(pilotScale N h f nu ωp : ℝ))/(eps : ℝ)
      ≤ (8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
        (nu : ℝ) h)/(eps : ℝ) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 8)) hepsR.le
  have hyceil :
      (8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
        (nu : ℝ) h)/(eps : ℝ)
        ≤ Int.ceil ((8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance
          (fun i => (f i : ℝ))) (nu : ℝ) h)/(eps : ℝ)) :=
    Int.le_ceil _
  have hcast : (8*(pilotScale N h f nu ωp : ℝ))/(eps : ℝ)
      ≤ (Int.ceil ((8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance
        (fun i => (f i : ℝ))) (nu : ℝ) h)/(eps : ℝ)) : ℝ) :=
    hxy.trans hyceil
  have hq : (8*pilotScale N h f nu ωp/eps : ℚ)
      ≤ (Int.ceil ((8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance
        (fun i => (f i : ℝ))) (nu : ℝ) h)/(eps : ℝ)) : ℤ) := by
    exact_mod_cast hcast
  have hqceil : (Int.ceil ((8*pilotScale N h f nu ωp)/eps) : ℤ)
      ≤ Int.ceil ((8*unknownSigmaScaleBound ((signedMeanSource A j hA).variance
        (fun i => (f i : ℝ))) (nu : ℝ) h)/(eps : ℝ)) :=
    Int.ceil_le.mpr hq
  simp only [pilotPrecision, unknownSigmaGoodPrecision]
  refine max_le_max (le_refl 4) ?_
  refine Nat.clog_mono_right 2 ?_
  exact Nat.add_le_add_right (Int.toNat_le_toNat hqceil) 1

/-- Under the stated boundedness and parameter conditions, every execution using its
pilot-selected precision has resources bounded componentwise by the worst-precision ledger. -/
theorem unknownSigma_budget_worst_path
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (ωp : Fin N → I) (ωt : unknownSigmaTrialRecord I r (pilotPrecision N h f nu eps ωp)) :
    unknownSigmaLedgerLe
      (unknownSigmaResources A j hA f nu eps N h K r hk
        (⟨unknownSigmaPilotIndex N h f nu eps K hk ωp, (ωp, ωt)⟩ : unknownSigmaFullRecord I N K r))
      (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)) := by
  have hprec : pilotPrecision N h f nu eps ωp ≤ unknownSigmaWorstPrecision eps := by
    simpa [unknownSigmaWorstPrecision] using!
      (unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps ωp
        hN hf hnu hnu1 heps).2.2
  rw [unknownSigma_resources_eq A j hA f nu eps N h K r hk]
  exact unknownSigma_ledger_mono hprec

/-- Under the stated boundedness and parameter conditions, every pilot-selected ledger is
bounded componentwise by the worst-precision ledger. -/
theorem unknownSigma_budget_worst_path_pilot
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (ωp : Fin N → I) :
    unknownSigmaLedgerLe (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp))
      (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)) := by
  have hprec : pilotPrecision N h f nu eps ωp ≤ unknownSigmaWorstPrecision eps := by
    exact (unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps ωp
      hN hf hnu hnu1 heps).2.2
  exact unknownSigma_ledger_mono hprec

/-- The expected source and layer access count under the full pilot-and-trial law. -/
noncomputable def unknownSigmaExpectedAccesses
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K) : ℝ :=
  ∑ rec : unknownSigmaFullRecord I N K r,
    (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
      (unknownSigmaLedgerAccesses N r rec.1.val)

noncomputable instance unknownSigma_badMoments_decidable (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (N : ℕ) (nu : ℝ) :
    DecidablePred (unknownSigmaBadMoments A j hA f N nu) := by
  unfold unknownSigmaBadMoments
  infer_instance

/-- The expected access count can be computed from the pilot law alone by averaging the ledger
at its selected precision. -/
theorem unknownSigma_expected_accesses_eq_pilot
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K) :
    unknownSigmaExpectedAccesses A j hA f nu eps N h K r hk
      = ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp *
          unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp) := by
  classical
  unfold unknownSigmaExpectedAccesses
  have h1 : (∑ rec : unknownSigmaFullRecord I N K r,
        (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
          unknownSigmaLedgerAccesses N r rec.1.val)
      = ∑ k : Fin K, ∑ (ωp : Fin N → I), ∑ ωt : unknownSigmaTrialRecord I r k.val,
          unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
            unknownSigmaLedgerAccesses N r k.val := by
    rw [show (∑ rec : unknownSigmaFullRecord I N K r,
            (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec *
              unknownSigmaLedgerAccesses N r rec.1.val)
          = ∑ rec : unknownSigmaFullRecord I N K r,
            (unknownSigmaLaw A j hA f nu eps N h K r hk).prob ⟨rec.1, rec.2⟩ *
              unknownSigmaLedgerAccesses N r rec.1.val from rfl]
    rw [Fintype.sum_sigma' (fun k y =>
        (unknownSigmaLaw A j hA f nu eps N h K r hk).prob ⟨k, y⟩ *
          unknownSigmaLedgerAccesses N r k.val)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun ωp _ => Finset.sum_congr rfl fun ωt _ => rfl
  have h2 : (∑ k : Fin K, ∑ (ωp : Fin N → I), ∑ ωt : unknownSigmaTrialRecord I r k.val,
          unknownSigmaProbAt A j hA f nu eps N h K r hk k ωp ωt *
            unknownSigmaLedgerAccesses N r k.val)
      = ∑ ωp : Fin N → I, ∑ k : Fin K, (unknownSigmaPilotLaw A j hA N).prob ωp *
            (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
              (unknownSigmaLedgerAccesses N r k.val : ℝ) else (0 : ℝ)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin K)))
      (t := (Finset.univ : Finset (Fin N → I)))]
    refine Finset.sum_congr rfl fun ωp _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hc : k = unknownSigmaPilotIndex N h f nu eps K hk ωp
    · simp only [if_pos hc]
      unfold unknownSigmaProbAt
      simp only [if_pos hc]
      have hsum : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt *
              unknownSigmaLedgerAccesses N r k.val)
          = unknownSigmaLedgerAccesses N r k.val := by
        calc
          _ = (∑ ωt : unknownSigmaTrialRecord I r k.val,
              (unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).probOf ωt) *
              unknownSigmaLedgerAccesses N r k.val := by rw [Finset.sum_mul]
          _ = 1 * unknownSigmaLedgerAccesses N r k.val := by
            rw [(unknownSigmaTrialLaw A j hA f nu eps N h K r hk k ωp).sum_probOf (2*r+1)]
          _ = _ := by ring
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      rw [hsum]
    · simp only [if_neg hc]
      unfold unknownSigmaProbAt
      simp only [if_neg hc]
      have hz : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            ((unknownSigmaPilotLaw A j hA N).prob ωp * (0 : ℝ)) *
              unknownSigmaLedgerAccesses N r k.val) = 0 := by
        have hz' : (∑ ωt : unknownSigmaTrialRecord I r k.val,
            ((unknownSigmaPilotLaw A j hA N).prob ωp * (0 : ℝ)) *
              unknownSigmaLedgerAccesses N r k.val)
            = ∑ _ωt : unknownSigmaTrialRecord I r k.val, (0 : ℝ) := by
          refine Finset.sum_congr rfl fun ωt _ => ?_
          ring
        rw [hz']
        simp
      rw [hz]
      ring
  have h3 : (∑ ωp : Fin N → I, ∑ k : Fin K, (unknownSigmaPilotLaw A j hA N).prob ωp *
            (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
              (unknownSigmaLedgerAccesses N r k.val : ℝ) else (0 : ℝ)))
      = ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp *
            unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp) := by
    refine Finset.sum_congr rfl fun ωp _ => ?_
    have hstep : (∑ k : Fin K, (unknownSigmaPilotLaw A j hA N).prob ωp *
                (if k = unknownSigmaPilotIndex N h f nu eps K hk ωp then
                  (unknownSigmaLedgerAccesses N r k.val : ℝ) else (0 : ℝ)))
        = (unknownSigmaPilotLaw A j hA N).prob ωp *
            unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp) := by
      rw [← Finset.mul_sum]
      rw [Fintype.sum_ite_eq' (unknownSigmaPilotIndex N h f nu eps K hk ωp)
        (fun k => (unknownSigmaLedgerAccesses N r k.val : ℝ))]
      rfl
    rw [hstep]
  rw [h1, h2, h3]

/-- The bad-pilot mass is at most the sum of the second and fourth source moments divided by `N
* nu^2` for positive pilot size and tolerance. -/
theorem unknownSigma_pilot_bad_mass
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (N : ℕ) (nu : ℝ) (hN : 0 < N) (hnu : 0 < nu) :
    (∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N nu ωp then
        (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))
      ≤ (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
          / ((N : ℝ)*(nu : ℝ)^2) := by
  classical
  have h := unknownSigma_pilot_moment_failure_mass A j hA f N nu hN hnu
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent at h
  rw [Finset.sum_filter] at h
  have hconv : (∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N nu ωp then
        (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))
      = ∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N nu ωp then
        (signedMeanSource A j hA).probOf ωp else (0 : ℝ) := by
    refine Finset.sum_congr rfl fun ωp _ => ?_
    simp [unknownSigmaPilotLaw, independentSampleLaw,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  rw [hconv]
  exact h

/-- Under the stated boundedness and parameter conditions, expected accesses are at most the
good-precision ledger accesses plus the moment failure bound times the worst-precision
ledger accesses. -/
theorem unknownSigma_expected_accesses_le
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    unknownSigmaExpectedAccesses A j hA f nu eps N h K r hk
      ≤ unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
              (nu : ℝ) h (eps : ℝ))
        + ((unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
            / ((N : ℝ)*(nu : ℝ)^2)) *
          unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) := by
  classical
  rw [unknownSigma_expected_accesses_eq_pilot]
  have hpoint (ωp : Fin N → I) :
      (unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp) : ℝ)
        ≤ if unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp then
            (unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) : ℝ) else
            (unknownSigmaLedgerAccesses N r
              (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
                (nu : ℝ) h (eps : ℝ)) : ℝ) := by
    by_cases hb : unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp
    · rw [if_pos hb]
      exact Nat.cast_le.mpr (unknownSigma_ledgerAccesses_mono (N := N) (r := r) (by
        exact (unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps ωp
          hN hf hnu hnu1 heps).2.2))
    · rw [if_neg hb]
      have hgoodmom : unknownSigmaGoodMoments A j hA f N (nu : ℝ) ωp :=
        (unknownSigma_good_iff_not_bad A j hA f N (nu : ℝ) ωp).mpr hb
      exact Nat.cast_le.mpr (unknownSigma_ledgerAccesses_mono (N := N) (r := r)
        (unknownSigma_good_precision_le A j hA f nu eps N h ωp hN hf hnu hnu1 heps hgoodmom))
  have hbadmass := unknownSigma_pilot_bad_mass A j hA f N (nu : ℝ) hN (by exact_mod_cast hnu)
  have hgoodmass :
      (∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp then
          (0 : ℝ) else (unknownSigmaPilotLaw A j hA N).prob ωp) ≤ 1 := by
    calc
      _ ≤ ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp := by
        exact Finset.sum_le_sum fun ωp _ => by
          by_cases hb : unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp
          · rw [if_pos hb]
            exact (unknownSigmaPilotLaw A j hA N).nonneg ωp
          · rw [if_neg hb]
      _ = 1 := by simpa using! (unknownSigmaPilotLaw A j hA N).sum_one
  calc
    (∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp *
        (unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp) : ℝ))
        ≤ ∑ ωp : Fin N → I, (unknownSigmaPilotLaw A j hA N).prob ωp *
          (if unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp then
            (unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) : ℝ) else
            (unknownSigmaLedgerAccesses N r
              (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance
                (fun i => (f i : ℝ))) (nu : ℝ) h (eps : ℝ)) : ℝ)) := by
          exact Finset.sum_le_sum fun ωp _ =>
            mul_le_mul_of_nonneg_left (hpoint ωp)
              ((unknownSigmaPilotLaw A j hA N).nonneg ωp)
    _ = (unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) : ℝ) *
          (∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp then
            (unknownSigmaPilotLaw A j hA N).prob ωp else (0 : ℝ))
        + (unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance
              (fun i => (f i : ℝ))) (nu : ℝ) h (eps : ℝ)) : ℝ) *
          (∑ ωp : Fin N → I, if unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp then
            (0 : ℝ) else (unknownSigmaPilotLaw A j hA N).prob ωp) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ωp _ => ?_
          by_cases hb : unknownSigmaBadMoments A j hA f N (nu : ℝ) ωp
          · simp [hb]
            ring
          · simp [hb]
            ring
    _ ≤ (unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) : ℝ) *
          ((unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
            / ((N : ℝ)*(nu : ℝ)^2))
        + (unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance
              (fun i => (f i : ℝ))) (nu : ℝ) h (eps : ℝ)) : ℝ) * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hbadmass (by positivity))
            (mul_le_mul_of_nonneg_left hgoodmass (by positivity))
    _ = unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
              (nu : ℝ) h (eps : ℝ))
        + ((unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
            / ((N : ℝ)*(nu : ℝ)^2)) *
          unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) := by ring
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
