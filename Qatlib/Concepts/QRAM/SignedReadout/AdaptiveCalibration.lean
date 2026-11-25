/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.CalibratedTranscript
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RelativeAeStopping
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout

@[expose] public section

/-!
# Amplitude estimates for calibrated tomography

A finite record of the fresh-block amplitude estimator of
[BrassardEtAl2002] supplies the first ready median. An unfinished
prefix returns zero and is charged to the pending probability. The
relative success-probability guarantee controls the interference
calibration error and, after taking a square root, the success
amplitude used for the physical scale. Costs count forward calls
to the same coherent preparation that defines the marked event.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw (adaptiveGrid)
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedAAState)
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono eventMass_or_le)
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_le_one)
open Qatlib.Foundations.PureStateMath (MeasureProb normalized_applyGate normalized_ket)
open scoped Classical

/-- Read the first ready median from a finite prefix, with zero as
the value assigned to an unfinished prefix. -/
def firstReadyEstimate (eps : ℝ) (r : ℕ → ℕ) {N : ℕ} (ω : FreshHistory r N) : ℝ :=
  if h : ∃ k, freshHistoryFirstStop eps r ω k then
    let k := Classical.choose h
    freshMedianEstimate (adaptiveGrid k.val) (r k.val) (ω k)
  else 0

/-- On a stopped prefix the reported estimate is the median at the
unique first ready stage. -/
theorem first_ready_estimate_eq (eps : ℝ) (r : ℕ → ℕ) {N : ℕ}
    (ω : FreshHistory r N) (k : Fin N) (hk : freshHistoryFirstStop eps r ω k) :
    firstReadyEstimate eps r ω = freshMedianEstimate (adaptiveGrid k.val) (r k.val) (ω k) := by
  let hex : ∃ j, freshHistoryFirstStop eps r ω j := ⟨k, hk⟩
  rw [firstReadyEstimate, dite_eq_left hex]
  exact congrArg (fun j : Fin N => freshMedianEstimate (adaptiveGrid j.val) (r j.val) (ω j))
    (freshHistoryFirstStop_unique eps r (Classical.choose_spec hex) hk)

/-- Both a reported median and the default estimate are probabilities. -/
theorem first_ready_estimate_mem (eps : ℝ) (r : ℕ → ℕ) {N : ℕ} (ω : FreshHistory r N) :
    firstReadyEstimate eps r ω ∈ Set.Icc 0 1 := by
  by_cases h : ∃ k, freshHistoryFirstStop eps r ω k
  · obtain ⟨k, hk⟩ := h
    rw [first_ready_estimate_eq eps r ω k hk, freshMedianLabel_spec]
    exact aeEstimate_mem _ _
  · simp [firstReadyEstimate, h]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A bad finite-prefix estimate either has a bad first ready median or
belongs to the unfinished prefixes. -/
theorem first_ready_relative_failure_le (eps : ℝ) (r : ℕ → ℕ) (N : ℕ)
    (A : Matrix I I ℂ) (seed : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let p := MeasureProb (preparedAAState A seed) S
    let law := freshHistoryLaw r N A seed S hA
    eventMass law (fun ω => eps * p < |firstReadyEstimate eps r ω - p|) ≤
      freshHistoryFailureMass eps r N A seed S hA + freshHistoryPendingMass eps r N A seed S hA := by
  intro p law
  let bad (ω : FreshHistory r N) := ∃ k, freshHistoryFirstStop eps r ω k ∧
    freshHistoryRelativeBad eps r A seed S ω k
  let pending := freshHistoryPending (N := N) eps r
  have hBad (ω : FreshHistory r N) (hω : eps * p < |firstReadyEstimate eps r ω - p|) :
      bad ω ∨ pending ω := by
    rcases freshHistory_pending_or_stop eps r ω with hPending | ⟨k, hk⟩
    · exact Or.inr hPending
    · rw [first_ready_estimate_eq eps r ω k hk] at hω
      exact Or.inl ⟨k, hk, hω⟩
  calc
    _ ≤ eventMass law (fun ω => bad ω ∨ pending ω) := eventMass_mono law _ _ hBad
    _ ≤ _ := eventMass_or_le law bad pending

/-- The stopped finite estimator has relative error failure at most the
requested budget plus the pending mass. Its expected forward accesses
have the adaptive positive-probability bound, and the pending mass
can be made arbitrarily small by extending the prefix. -/
theorem exists_first_ready_probability_schedule (eps δ : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hδ : 0 < δ)
    (A : Matrix I I ℂ) (seed : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hp : 0 < MeasureProb (preparedAAState A seed) S) :
    let p := MeasureProb (preparedAAState A seed) S
    ∃ r : ℕ,
      (∀ N, eventMass (freshHistoryLaw (fun _ => r) N A seed S hA)
        (fun ω => eps * p < |firstReadyEstimate eps (fun _ => r) ω - p|) ≤
          δ + freshHistoryPendingMass eps (fun _ => r) N A seed S hA) ∧
      (∀ N, freshHistoryExpectedForward eps (fun _ => r) N A seed S hA ≤
        (192 * Real.pi * (2 * (r : ℝ) + 1)) / (eps * Real.sqrt p)) ∧
      (∀ η : ℝ, 0 < η → ∃ B : ℕ, ∀ N, B < N →
        freshHistoryPendingMass eps (fun _ => r) N A seed S hA < η) := by
  intro p
  have hp1 : p ≤ 1 := measureProb_le_one (normalized_applyGate hA (normalized_ket seed)) S
  obtain ⟨r, hFail, hCost, hTail⟩ := exists_fixedFreshSchedule_failure_expected_tail
    eps δ heps heps1 hδ A seed S hA p hp hp1 rfl
  exact ⟨r, fun N => (first_ready_relative_failure_le eps (fun _ => r) N A seed S hA).trans
    (add_le_add (hFail N) le_rfl), hCost, hTail⟩

/-- Relative probability accuracy bounds the calibration imbalance of the
two interference branches. -/
theorem calibration_imbalance_le_of_relative {p q eps : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (heps : 0 ≤ eps) (hEstimate : |q - p| ≤ eps * p) :
    |p - q| / (p + q) ≤ eps := by
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hp hq)).mpr
  rw [abs_sub_comm p q]
  exact hEstimate.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hq) heps)

/-- Relative probability accuracy transfers to the same relative accuracy
for its nonnegative square root. -/
theorem success_amplitude_error_le_of_relative {p q eps : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hEstimate : |q - p| ≤ eps * p) :
    |Real.sqrt q - Real.sqrt p| ≤ eps * Real.sqrt p := by
  let a := Real.sqrt p
  let b := Real.sqrt q
  have ha : 0 < a := Real.sqrt_pos.2 hp
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hProd : |b - a| * (b + a) = |q - p| := by
    rw [← abs_of_nonneg (add_nonneg hb ha.le), ← abs_mul, mul_comm (b - a), ← sq_sub_sq,
      Real.sq_sqrt hq, Real.sq_sqrt hp.le]
  apply (mul_le_mul_iff_of_pos_right ha).mp
  calc
    |b - a| * a ≤ |b - a| * (b + a) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb) (abs_nonneg _)
    _ = _ := hProd
    _ ≤ eps * p := hEstimate
    _ = (eps * a) * a := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hp.le]

/-- Applying the finite-prefix estimator to the actual coherent target
bounds the failure probability of interference calibration. The same
schedule's forward access count and tail bounds remain available. -/
theorem TomographyPreparation.exists_calibration_schedule {depth : ℕ} (P : TomographyPreparation depth I)
    (eps δ : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hδ : 0 < δ) :
    let p := P.successProbability
    ∃ r : ℕ,
      (∀ N, eventMass (freshHistoryLaw (fun _ => r) N P.target P.seed P.success P.target_unitary)
        (fun ω => eps < |p - firstReadyEstimate eps (fun _ => r) ω| /
          (p + firstReadyEstimate eps (fun _ => r) ω)) ≤
          δ + freshHistoryPendingMass eps (fun _ => r) N P.target P.seed P.success P.target_unitary) ∧
      (∀ N, freshHistoryExpectedForward eps (fun _ => r) N P.target P.seed P.success P.target_unitary ≤
        (192 * Real.pi * (2 * (r : ℝ) + 1)) / (eps * Real.sqrt p)) ∧
      (∀ η : ℝ, 0 < η → ∃ B : ℕ, ∀ N, B < N →
        freshHistoryPendingMass eps (fun _ => r) N P.target P.seed P.success P.target_unitary < η) := by
  intro p
  obtain ⟨r, hFailure, hCost, hTail⟩ := exists_first_ready_probability_schedule eps δ heps heps1 hδ
    P.target P.seed P.success P.target_unitary P.success_pos
  refine ⟨r, fun N => ?_, hCost, hTail⟩
  refine (eventMass_mono _ _ _ ?_).trans (hFailure N)
  intro ω hBad
  refine lt_of_not_ge fun hGood => (not_lt_of_ge (calibration_imbalance_le_of_relative P.success_pos
    (first_ready_estimate_mem eps (fun _ => r) ω).1 heps.le hGood)) hBad

end Qatlib.Concepts.QRAM.SignedReadout
