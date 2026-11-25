/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.CalibratedTranscript
public import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoal
public import Qatlib.Foundations.BornMetrics.EventProbability

@[expose] public section

/-!
# Fresh retries for conditioned tomography shots

A failed herald discards an attempted shot. Repeating from a fresh seed
leaves the retained label law equal to the conditional measurement law.
The basis success probability is that of the target preparation. The
interference success probability averages that probability and the
calibration, independently of the sampled reference. Geometric
expectation therefore bounds the expected charged preparation costs
using the same attempt bound for every reference.
These retries extend the tomography sampling in
[KerenidisLandmanPrakash2020], Appendix G, to heralded state preparation.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SearchStopping.RestartLaw (geometric_restart_expectation)
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_le_one)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket MeasureProb normalized_applyGate normalized_ket)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators Classical

/-- Summing the accepted label's joint weights over all possible numbers of
failed attempts recovers its conditional one-shot probability. -/
theorem retained_readout_mass_eq {O : Type} [Fintype O] (law : FinDist O) (label : O)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' r : ℕ, (1 - p) ^ r * p * law.prob label) = law.prob label := by
  have hg : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have hs := (hasSum_geometric_of_norm_lt_one hg).mul_right (p * law.prob label)
  simp_rw [mul_assoc]
  rw [hs.tsum_eq, show (1 : ℝ) - (1 - p) = p by ring, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

/-- The expected charge for fresh attempts preceding and including the first
successful shot, at a fixed charge per attempt. -/
def retainedShotExpectedCost (p attemptCost : ℝ) : ℝ :=
  ∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * attemptCost * ((1 - p) ^ r * p)

namespace TomographyPreparation

variable {depth : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Common success probability of one actual flagged interference attempt. -/
def interferenceSuccessProbability (P : TomographyPreparation depth I) (q : ℝ)
    (samples : List (Address depth)) : ℝ :=
  MeasureProb (ApplyGate (heraldedInterferencePreparation P.target P.decoder
    (embeddedReferencePreparation P.place P.seed samples) P.success q) (Ket (false, false, P.seed)))
    (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I)))

/-- The common success probability is independent of the empirical reference
and at least half the target's success probability. -/
theorem interference_success_probability_eq (P : TomographyPreparation depth I) (q : ℝ)
    (hq : 0 ≤ q) (samples : List (Address depth)) :
    P.interferenceSuccessProbability q samples = (P.successProbability + q) / 2 :=
  heralded_interference_success _ _ _ _ _ _ P.decoder_unitary
    (embedded_reference_preparation_unitary P.place P.seed samples) hq

/-- A lower bound on target success bounds the expected charge per retained
basis or interference shot. The interference bound is uniform in the first
record and uses the actual common success flag. -/
theorem retained_shot_expected_cost_le (P : TomographyPreparation depth I)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (samples : List (Address depth))
    (lower basisCost interferenceCost : ℝ) (hLower : 0 < lower)
    (hSuccess : lower ≤ P.successProbability)
    (hBasisCost : 0 ≤ basisCost) (hInterferenceCost : 0 ≤ interferenceCost) :
    retainedShotExpectedCost P.successProbability basisCost ≤ basisCost / lower ∧
      retainedShotExpectedCost (P.interferenceSuccessProbability q samples) interferenceCost ≤
        2 * interferenceCost / lower := by
  have hp : 0 < P.successProbability := P.success_pos
  have hp1 : P.successProbability ≤ 1 :=
    measureProb_le_one (normalized_applyGate P.target_unitary (normalized_ket P.seed)) P.success
  have hm : 0 < (P.successProbability + q) / 2 := half_pos (add_pos_of_pos_of_nonneg hp hq.1)
  have hm1 : (P.successProbability + q) / 2 ≤ 1 := by linarith [hq.2]
  constructor
  · unfold retainedShotExpectedCost
    rw [geometric_restart_expectation _ _ hp hp1]
    exact div_le_div_of_nonneg_left hBasisCost hLower hSuccess
  · rw [P.interference_success_probability_eq q hq.1 samples]
    unfold retainedShotExpectedCost
    rw [geometric_restart_expectation _ _ hm hm1]
    have hHalf : lower / 2 ≤ (P.successProbability + q) / 2 := by linarith [hq.1]
    calc
      interferenceCost / ((P.successProbability + q) / 2) ≤ interferenceCost / (lower / 2) :=
        div_le_div_of_nonneg_left hInterferenceCost (half_pos hLower) hHalf
      _ = _ := by ring

/-- Averaging the second-batch charge over the first record gives a
linear expected charge for the two batches. -/
theorem retained_transcript_expected_cost_le (P : TomographyPreparation depth I)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (basisShots interferenceShots : ℕ)
    (lower basisCost interferenceCost : ℝ) (hLower : 0 < lower)
    (hSuccess : lower ≤ P.successProbability)
    (hBasisCost : 0 ≤ basisCost) (hInterferenceCost : 0 ≤ interferenceCost) :
    let first := independentSampleLaw fun _ : Fin basisShots => P.basisShot
    (basisShots : ℝ) * retainedShotExpectedCost P.successProbability basisCost +
      (interferenceShots : ℝ) * first.expect (fun b =>
        retainedShotExpectedCost (P.interferenceSuccessProbability q (List.ofFn b)) interferenceCost) ≤
      (basisShots : ℝ) * (basisCost / lower) +
        (interferenceShots : ℝ) * (2 * interferenceCost / lower) := by
  intro first
  obtain ⟨hb, hi⟩ := P.retained_shot_expected_cost_le q hq [] lower basisCost interferenceCost hLower
    hSuccess hBasisCost hInterferenceCost
  have hExpected : first.expect (fun b => retainedShotExpectedCost
      (P.interferenceSuccessProbability q (List.ofFn b)) interferenceCost) =
      retainedShotExpectedCost (P.interferenceSuccessProbability q []) interferenceCost := by
    simp only [FinDist.expect, P.interference_success_probability_eq q hq.1,
      ← Finset.sum_mul, first.sum_one, one_mul]
  rw [hExpected]
  exact add_le_add (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _))

end TomographyPreparation
end Qatlib.Concepts.QRAM.SignedReadout
