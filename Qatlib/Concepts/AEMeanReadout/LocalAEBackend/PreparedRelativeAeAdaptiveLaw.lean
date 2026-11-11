/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined

/-!
# Adaptive laws for prepared relative amplitude estimation

This module builds certified amplitude intervals from recorded AE labels and defines a stopping
test on geometrically growing grids. The stage laws are the Born distributions of prepared AE
circuits, with the success-window mass supplied by [BrassardEtAl2002]. `adaptiveReady` compares
interval width with its lower endpoint, so an accurate stage sample yields a relative-error
guarantee when the test fires.

The module proves deterministic stopping criteria and cumulative access budgets under the stated
sample-window hypotheses. `adaptiveJointLaw` places finitely many independent stage outcomes on
a common sample space and preserves each stage's window probability.

## Main statements

* `certifiedStop_relative_band`: derive relative error from interval certification.
* `adaptiveStopsAt_total_budget`: bound accumulated accesses before a stopping stage.
* `adaptiveStopsAt_or_before`: obtain a stopping stage from a sufficiently fine accurate sample.
* `adaptiveJointLaw_window_mass`: transfer the stage window bound to the joint law.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The phase-grid correction `π / M`. -/
noncomputable def gridCorrection (M : ℕ) : ℝ := Real.pi / (M : ℝ)

/-- The phase-grid correction is positive for a positive grid size. -/
theorem gridCorrection_pos {M : ℕ} (hM : 0 < M) : 0 < gridCorrection M := by
  unfold gridCorrection
  exact div_pos Real.pi_pos (by exact_mod_cast hM)

/-- The phase-grid correction is nonnegative for a positive grid size. -/
theorem gridCorrection_nonneg {M : ℕ} (hM : 0 < M) : 0 ≤ gridCorrection M :=
  (gridCorrection_pos hM).le

/-- For nonnegative `a`, adding `nextWindowBound M a` completes the square `(√a + gridCorrection
M)²`. -/
private theorem windowBound_add_eq_square {M : ℕ} (hM : 0 < M) (a : ℝ) (ha0 : 0 ≤ a) :
    a + nextWindowBound M a = (Real.sqrt a + gridCorrection M) ^ 2 := by
  have hsq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha0
  have h1 : (Real.sqrt a) ^ 2 + nextWindowBound M a
      = (Real.sqrt a + gridCorrection M) ^ 2 := by
    unfold nextWindowBound gridCorrection
    ring
  calc a + nextWindowBound M a
      = (Real.sqrt a) ^ 2 + nextWindowBound M a := by rw [hsq]
    _ = (Real.sqrt a + gridCorrection M) ^ 2 := h1

/-- Express `nextWindowBound` as `2√a` times the grid correction plus the squared correction. -/
private theorem windowBound_eq_grid_form {M : ℕ} (hM : 0 < M) (a : ℝ) :
    nextWindowBound M a
      = 2 * Real.sqrt a * (gridCorrection M) + (gridCorrection M) ^ 2 := by
  unfold nextWindowBound gridCorrection
  ring

/-- The amplitude estimate associated with a recorded finite phase label. -/
noncomputable def recordEstimate (M : ℕ) (z : Fin M) : ℝ := aeEstimate M z

/-- Every recorded amplitude estimate is nonnegative. -/
theorem recordEstimate_nonneg (M : ℕ) (z : Fin M) : 0 ≤ recordEstimate M z := by
  unfold recordEstimate aeEstimate
  exact sq_nonneg _

/-- The squared nonnegative part of the recorded square-root estimate minus the grid correction. -/
noncomputable def certifiedLowerBound (M : ℕ) (z : Fin M) : ℝ :=
  (max 0 (Real.sqrt (recordEstimate M z) - gridCorrection M)) ^ 2

/-- The squared sum of the grid correction and the square root of the recorded estimate plus
twice the squared correction. -/
noncomputable def certifiedUpperBound (M : ℕ) (z : Fin M) : ℝ :=
  (gridCorrection M
    + Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2)) ^ 2

/-- For a positive grid size, the certified lower endpoint does not exceed the recorded
estimate. -/
theorem certifiedLowerBound_le_record {M : ℕ} (hM : 0 < M) (z : Fin M) :
    certifiedLowerBound M z ≤ recordEstimate M z := by
  have hpos : 0 ≤ Real.sqrt (recordEstimate M z) := Real.sqrt_nonneg _
  have hc : 0 ≤ gridCorrection M := gridCorrection_nonneg hM
  unfold certifiedLowerBound
  by_cases h : Real.sqrt (recordEstimate M z) - gridCorrection M ≤ 0
  · rw [max_eq_left h]
    simpa using! recordEstimate_nonneg M z
  · rw [max_eq_right (by linarith)]
    have h1 : gridCorrection M ≤ 2 * Real.sqrt (recordEstimate M z) := by linarith
    have h2 : (gridCorrection M) * (gridCorrection M)
        ≤ 2 * (gridCorrection M) * Real.sqrt (recordEstimate M z) := by
      have hmul := mul_le_mul_of_nonneg_left h1 hc
      simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
    have h3 : (Real.sqrt (recordEstimate M z) - gridCorrection M) ^ 2
        ≤ (Real.sqrt (recordEstimate M z)) ^ 2 := by nlinarith [h2]
    rwa [Real.sq_sqrt (recordEstimate_nonneg M z)] at h3

/-- For a positive grid size, the recorded estimate does not exceed the certified upper
endpoint. -/
theorem record_le_certifiedUpperBound {M : ℕ} (hM : 0 < M) (z : Fin M) :
    recordEstimate M z ≤ certifiedUpperBound M z := by
  have hpos : 0 ≤ recordEstimate M z := recordEstimate_nonneg M z
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hc : 0 ≤ gridCorrection M := gridCorrection_nonneg hM
  have hnonneg : 0 ≤ recordEstimate M z + 2 * (gridCorrection M) ^ 2 := by
    have hsq2 : 0 ≤ (gridCorrection M) ^ 2 := sq_nonneg (R := ℝ) (gridCorrection M)
    linarith [hsq2, recordEstimate_nonneg M z]
  unfold certifiedUpperBound
  have h3 : Real.sqrt (recordEstimate M z) ≤ gridCorrection M
      + Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2) := by
    have hpos2 : 0 ≤ (gridCorrection M) ^ 2 := sq_nonneg (R := ℝ) (gridCorrection M)
    have h := Real.sqrt_le_sqrt
      (show recordEstimate M z ≤ recordEstimate M z + 2 * (gridCorrection M) ^ 2
        from by linarith)
    linarith [h, hc]
  have h4 : (Real.sqrt (recordEstimate M z)) ^ 2
      ≤ (gridCorrection M
          + Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2)) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h3
  rwa [Real.sq_sqrt (recordEstimate_nonneg M z)] at h4

/-- If the recorded estimate lies in the AE success window, its certified lower endpoint is at
most the prepared marked probability. -/
theorem certifiedLowerBound_le_amplitude {M : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin M) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |recordEstimate M z - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S)) :
    certifiedLowerBound M z ≤ MeasureProb (preparedAAState A j) S := by
  have ha0 : 0 ≤ MeasureProb (preparedAAState A j) S := measureProb_nonneg _ _
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hwin : nextAeWindow M (MeasureProb (preparedAAState A j) S)
      ≤ nextWindowBound M (MeasureProb (preparedAAState A j) S) :=
    nextAeWindow_le_bound M _ ha0 ha1
  have hsq : recordEstimate M z
      ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S) + gridCorrection M) ^ 2 := by
    have h1 : recordEstimate M z ≤ MeasureProb (preparedAAState A j) S
        + nextAeWindow M (MeasureProb (preparedAAState A j) S) := by
      rw [abs_le] at hw
      linarith
    have h2 : MeasureProb (preparedAAState A j) S
        + nextAeWindow M (MeasureProb (preparedAAState A j) S)
        ≤ MeasureProb (preparedAAState A j) S
          + nextWindowBound M (MeasureProb (preparedAAState A j) S) := by linarith [hwin]
    have h3 := windowBound_add_eq_square hM _ ha0
    linarith
  have hsqrt : Real.sqrt (recordEstimate M z)
      ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) + gridCorrection M := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by linarith [Real.sqrt_nonneg (MeasureProb (preparedAAState A j) S),
      gridCorrection_nonneg hM])] at h
    exact h
  unfold certifiedLowerBound
  by_cases h : Real.sqrt (recordEstimate M z) - gridCorrection M ≤ 0
  · rw [max_eq_left h]
    simpa using! measureProb_nonneg (preparedAAState A j) S
  · rw [max_eq_right (by linarith)]
    have h3 : 0 ≤ Real.sqrt (recordEstimate M z) - gridCorrection M := by linarith
    have h4 : Real.sqrt (recordEstimate M z) - gridCorrection M
        ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) := by linarith [hsqrt]
    have h5 : (Real.sqrt (recordEstimate M z) - gridCorrection M) ^ 2
        ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 :=
      (sq_le_sq₀ h3 (Real.sqrt_nonneg _)).mpr h4
    rwa [Real.sq_sqrt ha0] at h5

/-- If the recorded estimate lies in the AE success window, its certified upper endpoint is at
least the prepared marked probability. -/
theorem certifiedUpperBound_ge_amplitude {M : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin M) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |recordEstimate M z - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S)) :
    MeasureProb (preparedAAState A j) S ≤ certifiedUpperBound M z := by
  have ha0 : 0 ≤ MeasureProb (preparedAAState A j) S := measureProb_nonneg _ _
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hwin : nextAeWindow M (MeasureProb (preparedAAState A j) S)
      ≤ nextWindowBound M (MeasureProb (preparedAAState A j) S) :=
    nextAeWindow_le_bound M _ ha0 ha1
  have h1 : MeasureProb (preparedAAState A j) S ≤ recordEstimate M z
      + nextAeWindow M (MeasureProb (preparedAAState A j) S) := by
    rw [abs_le] at hw
    linarith
  have hsq : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      = MeasureProb (preparedAAState A j) S := Real.sq_sqrt ha0
  have h2 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      ≤ recordEstimate M z + nextWindowBound M (MeasureProb (preparedAAState A j) S) := by
    rw [hsq]
    linarith [hwin]
  have hb : nextWindowBound M (MeasureProb (preparedAAState A j) S)
      = 2 * Real.sqrt (MeasureProb (preparedAAState A j) S) * (gridCorrection M)
        + (gridCorrection M) ^ 2 :=
    windowBound_eq_grid_form hM _
  have hstep : (Real.sqrt (MeasureProb (preparedAAState A j) S) - gridCorrection M) ^ 2
      ≤ recordEstimate M z + 2 * (gridCorrection M) ^ 2 := by
    nlinarith [h2, hb]
  have hle : Real.sqrt (MeasureProb (preparedAAState A j) S) - gridCorrection M
      ≤ Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2) :=
    Real.le_sqrt_of_sq_le hstep
  have hnonneg : 0 ≤ recordEstimate M z + 2 * (gridCorrection M) ^ 2 := by
    have hsq2 : 0 ≤ (gridCorrection M) ^ 2 := sq_nonneg (R := ℝ) (gridCorrection M)
    linarith [hsq2, recordEstimate_nonneg M z]
  unfold certifiedUpperBound
  have h5 : Real.sqrt (MeasureProb (preparedAAState A j) S) ≤ gridCorrection M
      + Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2) := by linarith [hle]
  have h6 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      ≤ (gridCorrection M
          + Real.sqrt (recordEstimate M z + 2 * (gridCorrection M) ^ 2)) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg (MeasureProb (preparedAAState A j) S))
      (by linarith [gridCorrection_nonneg hM,
        Real.sqrt_nonneg (recordEstimate M z + 2 * (gridCorrection M) ^ 2)])).mpr h5
  rwa [Real.sq_sqrt ha0] at h6

/-- An estimate in the AE success window yields a certified interval containing the prepared
marked probability. -/
theorem certifiedInterval_contains {M : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin M) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |recordEstimate M z - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S)) :
    certifiedLowerBound M z ≤ MeasureProb (preparedAAState A j) S
      ∧ MeasureProb (preparedAAState A j) S ≤ certifiedUpperBound M z :=
  ⟨certifiedLowerBound_le_amplitude hM A j S hA z ha1 hw,
   certifiedUpperBound_ge_amplitude hM A j S hA z ha1 hw⟩

/-- The dyadic grid size `2^(k + 1)` at adaptive stage `k`. -/
def adaptiveGrid (k : ℕ) : ℕ := 2 ^ (k + 1)

/-- Every adaptive grid has at least two labels. -/
theorem adaptiveGrid_two (k : ℕ) : 2 ≤ adaptiveGrid k := by
  unfold adaptiveGrid
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The adaptive grid size doubles at each successor stage. -/
theorem adaptiveGrid_succ (k : ℕ) :
    adaptiveGrid (k + 1) = 2 * adaptiveGrid k := by
  unfold adaptiveGrid
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ, pow_succ]
  ring

/-- Reduce a natural-number record modulo the grid size at stage `k`. -/
def adaptiveLabel (k w : ℕ) : Fin (adaptiveGrid k) :=
  ⟨w % adaptiveGrid k, Nat.mod_lt _ (by unfold adaptiveGrid; positivity)⟩

/-- The amplitude estimate obtained from the record at adaptive stage `k`. -/
noncomputable def adaptiveEstimate (k w : ℕ) : ℝ :=
  recordEstimate (adaptiveGrid k) (adaptiveLabel k w)

/-- The certified lower endpoint obtained from the record at adaptive stage `k`. -/
noncomputable def adaptiveLower (k w : ℕ) : ℝ :=
  certifiedLowerBound (adaptiveGrid k) (adaptiveLabel k w)

/-- The certified upper endpoint obtained from the record at adaptive stage `k`. -/
noncomputable def adaptiveUpper (k w : ℕ) : ℝ :=
  certifiedUpperBound (adaptiveGrid k) (adaptiveLabel k w)

/-- The stopping condition that the certified interval width is at most `eps` times its lower
endpoint. -/
def adaptiveReady (eps : ℝ) (k w : ℕ) : Prop :=
  adaptiveUpper k w - adaptiveLower k w ≤ eps * adaptiveLower k w

/-- A ready adaptive stage has a strictly positive certified lower endpoint. -/
theorem adaptiveReady_pos {eps : ℝ} {k w : ℕ} (hM : 0 < adaptiveGrid k)
    (h : adaptiveReady eps k w) : 0 < adaptiveLower k w := by
  have hM' : (0:ℝ) < (adaptiveGrid k : ℝ) := by positivity
  have hU : 0 < adaptiveUpper k w := by
    unfold adaptiveUpper certifiedUpperBound
    have hc : 0 < gridCorrection (adaptiveGrid k) := div_pos Real.pi_pos hM'
    positivity
  unfold adaptiveReady at h
  by_contra hn
  have hLe : adaptiveLower k w ≤ 0 := le_of_not_gt hn
  have hnonneg : 0 ≤ adaptiveLower k w := by
    unfold adaptiveLower certifiedLowerBound
    exact sq_nonneg (R := ℝ) (max 0 (Real.sqrt (recordEstimate (adaptiveGrid k)
        (adaptiveLabel k w)) - gridCorrection (adaptiveGrid k)))
  have hL : adaptiveLower k w = 0 := le_antisymm hLe hnonneg
  rw [hL] at h
  linarith

/-- An AE-window sample whose certified interval width is at most `eps` times its lower endpoint
has relative error at most `eps` for positive `eps`. -/
theorem certifiedStop_relative_band {M : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin M) (eps : ℝ) (heps : 0 < eps)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |recordEstimate M z - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S))
    (hready : certifiedUpperBound M z - certifiedLowerBound M z
        ≤ eps * certifiedLowerBound M z) :
    |recordEstimate M z - MeasureProb (preparedAAState A j) S|
      ≤ eps * MeasureProb (preparedAAState A j) S := by
  have ha0 : 0 ≤ MeasureProb (preparedAAState A j) S := measureProb_nonneg _ _
  obtain ⟨hL, hU⟩ := certifiedInterval_contains hM A j S hA z ha1 hw
  have hrec : certifiedLowerBound M z ≤ recordEstimate M z :=
    certifiedLowerBound_le_record hM z
  have hrec' : recordEstimate M z ≤ certifiedUpperBound M z :=
    record_le_certifiedUpperBound hM z
  have hwidth : certifiedUpperBound M z - certifiedLowerBound M z
      ≤ eps * certifiedLowerBound M z := hready
  have hscale : eps * certifiedLowerBound M z
      ≤ eps * MeasureProb (preparedAAState A j) S :=
    mul_le_mul_of_nonneg_left hL (le_of_lt heps)
  rw [abs_le]
  constructor
  · have h1 : recordEstimate M z - MeasureProb (preparedAAState A j) S
        ≤ certifiedUpperBound M z - certifiedLowerBound M z := by linarith
    linarith
  · have h1 : MeasureProb (preparedAAState A j) S - recordEstimate M z
        ≤ certifiedUpperBound M z - certifiedLowerBound M z := by linarith
    linarith

/-- At an adaptive stage, an AE-window sample satisfying `adaptiveReady` has relative error at
most `eps` for positive `eps`. -/
theorem certifiedStop_relative_band_at_stage {k w : ℕ} (eps : ℝ) (heps : 0 < eps)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |adaptiveEstimate k w - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S))
    (hready : adaptiveReady eps k w) :
    |adaptiveEstimate k w - MeasureProb (preparedAAState A j) S|
      ≤ eps * MeasureProb (preparedAAState A j) S := by
  have hM : 0 < adaptiveGrid k := by
    unfold adaptiveGrid
    positivity
  exact certifiedStop_relative_band hM A j S hA (adaptiveLabel k w) eps heps ha1 hw hready

/-- If `8π ≤ M√a` and `a ≥ 0`, the grid correction is at most `√a / 8`. -/
theorem gridCorrection_le_eighth {M : ℕ} (hM : 0 < M) (a : ℝ) (ha0 : 0 ≤ a)
    (hscale : 8 * Real.pi ≤ (M : ℝ) * Real.sqrt a) :
    gridCorrection M ≤ Real.sqrt a / 8 := by
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h6 : Real.pi ≤ ((M : ℝ) * Real.sqrt a) / 8 :=
    (le_div_iff₀ (by norm_num : (0:ℝ) < 8)).2 (by simpa [mul_comm] using! hscale)
  have h8 : Real.pi / (M : ℝ) ≤ ((M : ℝ) * Real.sqrt a) / 8 / (M : ℝ) :=
    div_le_div_of_nonneg_right h6 hM'.le
  have h9 : ((M : ℝ) * Real.sqrt a) / 8 / (M : ℝ) = Real.sqrt a / 8 := by
    field_simp
  unfold gridCorrection
  rw [h9] at h8
  exact h8

/-- An accurate AE-window sample with grid correction at most `√a / 8` has certified lower
endpoint at least `a / 4`. -/
theorem certifiedLowerBound_ge_quarter {M : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin M) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hscale : gridCorrection M ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 8)
    (hw : |recordEstimate M z - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S)) :
    MeasureProb (preparedAAState A j) S / 4 ≤ certifiedLowerBound M z := by
  have ha0 : 0 ≤ MeasureProb (preparedAAState A j) S := measureProb_nonneg _ _
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hc : 0 < gridCorrection M := gridCorrection_pos hM
  have hu : 0 < Real.sqrt (MeasureProb (preparedAAState A j) S) := by
    have h1 : 0 ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) := Real.sqrt_nonneg _
    by_contra hn
    have h2 : Real.sqrt (MeasureProb (preparedAAState A j) S) ≤ 0 := le_of_not_gt hn
    have h3 : Real.sqrt (MeasureProb (preparedAAState A j) S) = 0 := le_antisymm h2 h1
    have h4 : gridCorrection M ≤ 0 := by linarith [hscale]
    linarith
  have hwin : nextAeWindow M (MeasureProb (preparedAAState A j) S)
      ≤ nextWindowBound M (MeasureProb (preparedAAState A j) S) :=
    nextAeWindow_le_bound M _ ha0 ha1
  have h1 : MeasureProb (preparedAAState A j) S ≤ recordEstimate M z
      + nextAeWindow M (MeasureProb (preparedAAState A j) S) := by
    rw [abs_le] at hw
    linarith
  have h2 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      ≤ recordEstimate M z + nextWindowBound M (MeasureProb (preparedAAState A j) S) := by
    have hsq : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
        = MeasureProb (preparedAAState A j) S := Real.sq_sqrt ha0
    rw [hsq]
    linarith [hwin]
  have hb : nextWindowBound M (MeasureProb (preparedAAState A j) S)
      = 2 * Real.sqrt (MeasureProb (preparedAAState A j) S) * (gridCorrection M)
        + (gridCorrection M) ^ 2 :=
    windowBound_eq_grid_form hM _
  have hsq : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      = MeasureProb (preparedAAState A j) S := Real.sq_sqrt ha0
  have hsq2 : (Real.sqrt (recordEstimate M z)) ^ 2 = recordEstimate M z :=
    Real.sq_sqrt (recordEstimate_nonneg M z)
  have hest : (Real.sqrt (recordEstimate M z)) ^ 2
      ≥ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
        - 2 * Real.sqrt (MeasureProb (preparedAAState A j) S) * (gridCorrection M)
        - (gridCorrection M) ^ 2 := by
    nlinarith [h2, hb]
  have hc1 : Real.sqrt (MeasureProb (preparedAAState A j) S) * gridCorrection M
      ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hscale
      (Real.sqrt_nonneg (MeasureProb (preparedAAState A j) S))
    nlinarith
  have hc2 : (gridCorrection M) ^ 2
      ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 / 64 := by
    have h1 : gridCorrection M * Real.sqrt (MeasureProb (preparedAAState A j) S)
        ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 / 8 := by
      have hmul := mul_le_mul_of_nonneg_right hscale
        (Real.sqrt_nonneg (MeasureProb (preparedAAState A j) S))
      nlinarith
    have h2 : gridCorrection M * gridCorrection M
        ≤ gridCorrection M * (Real.sqrt (MeasureProb (preparedAAState A j) S) / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc)
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) := Real.sqrt_nonneg _
  have hw2 : 0 ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 := sq_nonneg _
  have hcore : (max 0 (Real.sqrt (recordEstimate M z) - gridCorrection M)) ^ 2
      ≥ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 / 4 := by
    have hv : 0 ≤ Real.sqrt (recordEstimate M z) := Real.sqrt_nonneg _
    have hc3 : 2 * Real.sqrt (MeasureProb (preparedAAState A j) S) * (gridCorrection M)
        ≤ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 / 4 := by
      have h2sqrt : 0 ≤ (2:ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hscale h2sqrt
      nlinarith
    have h1 : (Real.sqrt (recordEstimate M z)) ^ 2
        ≥ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 * 47 / 64 := by
      nlinarith [hest, hc3, hc2, hw2]
    have h2' : (Real.sqrt (recordEstimate M z)) ^ 2
        ≥ (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2 * 9 / 16 := by
      nlinarith [h1, hw2]
    have h3 : 3 * Real.sqrt (MeasureProb (preparedAAState A j) S) / 4
        ≤ Real.sqrt (recordEstimate M z) := by
      have h4 : (3 * Real.sqrt (MeasureProb (preparedAAState A j) S) / 4) ^ 2
          ≤ (Real.sqrt (recordEstimate M z)) ^ 2 := by nlinarith [h2']
      have hA : 0 ≤ 3 * Real.sqrt (MeasureProb (preparedAAState A j) S) / 4 := by
        positivity
      have hB : 0 ≤ Real.sqrt (recordEstimate M z) := Real.sqrt_nonneg _
      have hmp : (3 * Real.sqrt (MeasureProb (preparedAAState A j) S) / 4) ^ 2
          ≤ (Real.sqrt (recordEstimate M z)) ^ 2
          → 3 * Real.sqrt (MeasureProb (preparedAAState A j) S) / 4
            ≤ Real.sqrt (recordEstimate M z) := (sq_le_sq₀ hA hB).mp
      exact hmp h4
    have h5 : Real.sqrt (MeasureProb (preparedAAState A j) S) / 2
        ≤ Real.sqrt (recordEstimate M z) - gridCorrection M := by linarith
    have h6 : 0 ≤ Real.sqrt (recordEstimate M z) - gridCorrection M := by linarith
    rw [max_eq_right h6]
    have hW : 0 ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 2 :=
      div_nonneg hsqrt0 (by norm_num)
    have h7 : (Real.sqrt (recordEstimate M z) - gridCorrection M) ^ 2
        ≥ (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ^ 2 :=
      (sq_le_sq₀ hW h6).mpr h5
    nlinarith [h7]
  have hsq3 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
      = MeasureProb (preparedAAState A j) S := Real.sq_sqrt ha0
  unfold certifiedLowerBound
  nlinarith [hcore]

/-- Every adaptive amplitude estimate is nonnegative. -/
theorem adaptiveEstimate_nonneg (k w : ℕ) : 0 ≤ adaptiveEstimate k w :=
  recordEstimate_nonneg _ _

/-- Every adaptive amplitude estimate is at most one. -/
theorem adaptiveEstimate_le_one (k w : ℕ) : adaptiveEstimate k w ≤ 1 := by
  unfold adaptiveEstimate recordEstimate aeEstimate
  have h : |Real.sin (Real.pi * (adaptiveLabel k w).val / (adaptiveGrid k : ℝ))| ≤ 1 :=
    Real.abs_sin_le_one _
  have h' := abs_le.mp h
  nlinarith [sq_nonneg (R := ℝ)
    (Real.sin (Real.pi * (adaptiveLabel k w).val / (adaptiveGrid k : ℝ)))]

/-- Every adaptive certified lower endpoint is nonnegative. -/
theorem adaptiveLower_nonneg (k w : ℕ) : 0 ≤ adaptiveLower k w := by
  unfold adaptiveLower certifiedLowerBound
  exact sq_nonneg (R := ℝ) _

/-- Every adaptive certified upper endpoint is strictly positive. -/
theorem adaptiveUpper_pos {k : ℕ} (w : ℕ) : 0 < adaptiveUpper k w := by
  have hM : 0 < adaptiveGrid k := by unfold adaptiveGrid; positivity
  unfold adaptiveUpper certifiedUpperBound
  have hc : 0 < gridCorrection (adaptiveGrid k) := gridCorrection_pos hM
  positivity

/-- Readiness implies `4π ≤ eps` times the grid size times the square root of the recorded
estimate. -/
theorem adaptiveReady_grid_lower {k w : ℕ} (eps : ℝ)
    (h : adaptiveReady eps k w) :
    4 * Real.pi ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt (adaptiveEstimate k w) := by
  have hM : 0 < adaptiveGrid k := by unfold adaptiveGrid; positivity
  have hc : 0 < gridCorrection (adaptiveGrid k) := gridCorrection_pos hM
  have hv0 : 0 ≤ Real.sqrt (adaptiveEstimate k w) := Real.sqrt_nonneg _
  have hL : adaptiveLower k w
      = (max 0 (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k))) ^ 2 := by
    unfold adaptiveLower certifiedLowerBound adaptiveEstimate recordEstimate
    rfl
  have hU : adaptiveUpper k w
      = (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w
              + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2 := by
    unfold adaptiveUpper certifiedUpperBound adaptiveEstimate recordEstimate
    rfl
  have hvc : gridCorrection (adaptiveGrid k) < Real.sqrt (adaptiveEstimate k w) := by
    unfold adaptiveReady at h
    by_contra hn
    have hle : Real.sqrt (adaptiveEstimate k w) ≤ gridCorrection (adaptiveGrid k) :=
      le_of_not_gt hn
    have hL0 : adaptiveLower k w = 0 := by
      rw [hL, max_eq_left (by linarith)]
      simp
    have hUpos : 0 < adaptiveUpper k w := by rw [hU]; positivity
    rw [hL0] at h
    linarith
  have hL1 : adaptiveLower k w
      = (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
    rw [hL, max_eq_right (by linarith)]
  have hs2 : (Real.sqrt (adaptiveEstimate k w
        + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
      = adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2 := by
    exact Real.sq_sqrt (add_nonneg (adaptiveEstimate_nonneg k w)
      (mul_nonneg (by norm_num) (sq_nonneg (R := ℝ) (gridCorrection (adaptiveGrid k)))))
  have hsge : Real.sqrt (adaptiveEstimate k w)
      ≤ Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2) := by
    apply Real.sqrt_le_sqrt
    have h2 : 0 ≤ 2 * (gridCorrection (adaptiveGrid k)) ^ 2 := by positivity
    linarith
  have hvsq : (Real.sqrt (adaptiveEstimate k w)) ^ 2 = adaptiveEstimate k w :=
    Real.sq_sqrt (adaptiveEstimate_nonneg k w)
  have hdiff : (gridCorrection (adaptiveGrid k)
        + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
      - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
      = 2 * gridCorrection (adaptiveGrid k)
        * (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
          + Real.sqrt (adaptiveEstimate k w)) := by
    nlinarith [hs2, hvsq]
  have hwidth : 4 * gridCorrection (adaptiveGrid k) * Real.sqrt (adaptiveEstimate k w)
      ≤ (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
        - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
    rw [hdiff]
    have hc0 : 0 ≤ gridCorrection (adaptiveGrid k) := gridCorrection_nonneg hM
    have hsum : 2 * Real.sqrt (adaptiveEstimate k w)
        ≤ gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
          + Real.sqrt (adaptiveEstimate k w) := by
      nlinarith [hsge]
    have hmul : 2 * gridCorrection (adaptiveGrid k) * (2 * Real.sqrt (adaptiveEstimate k w))
        ≤ 2 * gridCorrection (adaptiveGrid k)
          * (gridCorrection (adaptiveGrid k)
            + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
            + Real.sqrt (adaptiveEstimate k w)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * gridCorrection (adaptiveGrid k))
    nlinarith [hmul]
  have hrule : (gridCorrection (adaptiveGrid k)
        + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
      - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
      ≤ eps * (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
    unfold adaptiveReady at h
    rw [hL1, hU] at h
    linarith
  have hkey : 4 * gridCorrection (adaptiveGrid k) * Real.sqrt (adaptiveEstimate k w)
      ≤ eps * (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 :=
    hwidth.trans hrule
  have heps0 : 0 ≤ eps := by
    by_contra hn
    have hneg : eps < 0 := lt_of_not_ge hn
    have hsqpos : 0 < (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
      have hdiff : 0 < Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k) := by
        linarith
      exact sq_pos_of_pos hdiff
    nlinarith
  have hsqle : (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
      ≤ (Real.sqrt (adaptiveEstimate k w)) ^ 2 := by
    have h1 : Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)
        ≤ Real.sqrt (adaptiveEstimate k w) := by
      linarith [gridCorrection_nonneg hM]
    have h2 : 0 ≤ Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k) := by
      linarith
    have h3 : 0 ≤ Real.sqrt (adaptiveEstimate k w) := hv0
    exact (sq_le_sq₀ h2 h3).mpr h1
  have hmain : 4 * gridCorrection (adaptiveGrid k) ≤ eps * Real.sqrt (adaptiveEstimate k w) := by
    have hvpos : 0 < Real.sqrt (adaptiveEstimate k w) := by linarith
    nlinarith [hkey, hsqle]
  have h1 : (4 * Real.pi) / (adaptiveGrid k : ℝ)
      ≤ eps * Real.sqrt (adaptiveEstimate k w) := by
    have := hmain
    unfold gridCorrection at this
    convert! this using 1; ring
  have hM' : (0:ℝ) < (adaptiveGrid k : ℝ) := by positivity
  have h2 : 4 * Real.pi ≤ (eps * Real.sqrt (adaptiveEstimate k w)) * (adaptiveGrid k : ℝ) :=
    (div_le_iff₀ hM').mp h1
  convert! h2 using 1; ring

/-- Under the stated positive-parameter and width inequalities with `eps ≤ 1`, the product `eps
* v` is at most `8 * c`. -/
private theorem notReady_algebra {eps v c : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hc : 0 < c) (hv : c < v) (h : eps * (v - c) ^ 2 < 4 * c * (v + c)) :
    eps * v ≤ 8 * c := by
  have hvpos : 0 < v := lt_trans hc hv
  let t : ℝ := c / v
  have htv : t * v = c := by
    dsimp [t]
    field_simp
  have hscaled : eps * (v ^ 2 * (1 - t) ^ 2) < 4 * t * v ^ 2 * (1 + t) := by
    have h2 : (v - t * v) ^ 2 = v ^ 2 * (1 - t) ^ 2 := by ring
    have h3 : (t * v) * (v + t * v) = t * v ^ 2 * (1 + t) := by ring
    have hh := h
    rw [← htv] at hh
    rw [h2] at hh
    nlinarith [hh]
  have hgoal : eps ≤ 8 * t := by
    by_contra hn
    have h8t : 8 * t < eps := lt_of_not_ge hn
    have ht8 : t < 1 / 8 := by
      have : eps / 8 ≤ 1 / 8 := by linarith
      linarith
    have hone : 7 / 8 < 1 - t := by linarith
    have hsq : 49 / 64 < (1 - t) ^ 2 := by
      have h2 : 0 ≤ (7/8:ℝ) := by norm_num
      have h3 : 0 < 1 - t := by linarith
      have h4 : (7/8:ℝ) * (7/8) < (1 - t) * (1 - t) :=
        mul_lt_mul hone (le_of_lt hone) (by norm_num : (0:ℝ) < 7 / 8) (le_of_lt h3)
      nlinarith [h4]
    have hupp : 4 * t * (1 + t) < 9 * eps / 16 := by
      have hstep1 : 4 * (1 + t) * t < 4 * (1 + t) * (eps / 8) := by
        have hmul := mul_lt_mul_of_pos_left (show t < eps / 8 by linarith)
          (by positivity : 0 < 4 * (1 + t))
        exact hmul
      have hstep2 : 4 * (eps / 8) * (1 + t) < 4 * (eps / 8) * (1 + eps / 8) := by
        have hmul := mul_lt_mul_of_pos_left (show 1 + t < 1 + eps / 8 by linarith)
          (by positivity : 0 < 4 * (eps / 8))
        exact hmul
      have hstep3 : 4 * (eps / 8) * (1 + eps / 8) ≤ 9 * eps / 16 := by
        have hle : 4 * (eps / 8) * (1 + eps / 8) ≤ (eps / 2) * (1 + 1 / 8) := by
          have hmul := mul_le_mul_of_nonneg_left (show 1 + eps / 8 ≤ 1 + 1 / 8 by linarith)
            (by positivity : 0 ≤ eps / 2)
          nlinarith [hmul]
        nlinarith
      nlinarith
    have hsq' : eps * (v ^ 2 * (49 / 64)) < eps * (v ^ 2 * (1 - t) ^ 2) := by
      have hmul := mul_lt_mul_of_pos_left hsq (by positivity : 0 < eps * v ^ 2)
      nlinarith [hmul]
    have hupp' : 4 * t * v ^ 2 * (1 + t) < 9 * eps * v ^ 2 / 16 := by
      have hmul := mul_lt_mul_of_pos_left hupp (by positivity : 0 < v ^ 2)
      nlinarith [hmul]
    have h2' : eps * (v ^ 2 * (49 / 64)) < 4 * t * v ^ 2 * (1 + t) := hsq'.trans hscaled
    have h3' : eps * (v ^ 2 * (49 / 64)) < 9 * eps * v ^ 2 / 16 := h2'.trans hupp'
    have hpos : 0 < eps * v ^ 2 := mul_pos heps (sq_pos_of_pos hvpos)
    linarith
  have hfin : eps * v ≤ 8 * t * v := by
    have hmul := mul_le_mul_of_nonneg_left hgoal (le_of_lt hvpos)
    nlinarith [hmul]
  nlinarith [htv, hfin]

/-- For `0 < eps ≤ 1`, a stage that is not ready satisfies `eps` times the grid size times the
square root of its estimate at most `8π`. -/
theorem adaptiveNotReady_grid_upper {k w : ℕ} (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (h : ¬ adaptiveReady eps k w) :
    eps * (adaptiveGrid k : ℝ) * Real.sqrt (adaptiveEstimate k w) ≤ 8 * Real.pi := by
  have hM : 0 < adaptiveGrid k := by unfold adaptiveGrid; positivity
  have hc : 0 < gridCorrection (adaptiveGrid k) := gridCorrection_pos hM
  have hL : adaptiveLower k w
      = (max 0 (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k))) ^ 2 := by
    unfold adaptiveLower certifiedLowerBound adaptiveEstimate recordEstimate
    rfl
  have hU : adaptiveUpper k w
      = (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w
              + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2 := by
    unfold adaptiveUpper certifiedUpperBound adaptiveEstimate recordEstimate
    rfl
  have hprod : (adaptiveGrid k : ℝ) * gridCorrection (adaptiveGrid k) = Real.pi := by
    unfold gridCorrection
    field_simp
  by_cases hvc : Real.sqrt (adaptiveEstimate k w) ≤ gridCorrection (adaptiveGrid k)
  · have h1 : eps * (adaptiveGrid k : ℝ) * Real.sqrt (adaptiveEstimate k w)
        ≤ eps * (adaptiveGrid k : ℝ) * gridCorrection (adaptiveGrid k) := by
      have hmul := mul_le_mul_of_nonneg_left hvc
        (by positivity : 0 ≤ eps * (adaptiveGrid k : ℝ))
      nlinarith
    have h2 : eps * (adaptiveGrid k : ℝ) * gridCorrection (adaptiveGrid k) ≤ eps * Real.pi := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_eq hprod) (le_of_lt heps)
      nlinarith
    have h3 : eps * Real.pi ≤ 8 * Real.pi := by
      have hpi : 0 < Real.pi := Real.pi_pos
      have : eps ≤ 8 := by linarith
      nlinarith
    nlinarith
  · have hvc' : gridCorrection (adaptiveGrid k) < Real.sqrt (adaptiveEstimate k w) :=
      lt_of_not_ge hvc
    have hL1 : adaptiveLower k w
        = (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
      rw [hL, max_eq_right (by linarith)]
    have hs2 : (Real.sqrt (adaptiveEstimate k w
          + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
        = adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2 := by
      exact Real.sq_sqrt (add_nonneg (adaptiveEstimate_nonneg k w)
        (mul_nonneg (by norm_num) (sq_nonneg (R := ℝ) (gridCorrection (adaptiveGrid k)))))
    have hvsq : (Real.sqrt (adaptiveEstimate k w)) ^ 2 = adaptiveEstimate k w :=
      Real.sq_sqrt (adaptiveEstimate_nonneg k w)
    have hsle : Real.sqrt (adaptiveEstimate k w
          + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
        ≤ Real.sqrt (adaptiveEstimate k w) + gridCorrection (adaptiveGrid k) := by
      have hcv : gridCorrection (adaptiveGrid k) ≤ 2 * Real.sqrt (adaptiveEstimate k w) := by
        linarith
      have h2 : (Real.sqrt (adaptiveEstimate k w) + gridCorrection (adaptiveGrid k)) ^ 2
          ≥ adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2 := by
        have hsq : (Real.sqrt (adaptiveEstimate k w) + gridCorrection (adaptiveGrid k)) ^ 2
            = adaptiveEstimate k w
              + 2 * Real.sqrt (adaptiveEstimate k w) * gridCorrection (adaptiveGrid k)
              + (gridCorrection (adaptiveGrid k)) ^ 2 := by
          nlinarith [hvsq]
        nlinarith
      have hx := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq (by positivity)] at hx
      exact hx
    have hwidth : (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
        - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
        ≤ 4 * gridCorrection (adaptiveGrid k)
            * (Real.sqrt (adaptiveEstimate k w) + gridCorrection (adaptiveGrid k)) := by
      have hd : (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
        - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
        = 2 * gridCorrection (adaptiveGrid k)
            * (gridCorrection (adaptiveGrid k)
              + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
              + Real.sqrt (adaptiveEstimate k w)) := by
        nlinarith [hs2, hvsq]
      rw [hd]
      have hstep1 : 2 * gridCorrection (adaptiveGrid k)
            * (gridCorrection (adaptiveGrid k)
              + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)
              + Real.sqrt (adaptiveEstimate k w))
          ≤ 2 * gridCorrection (adaptiveGrid k)
            * (2 * Real.sqrt (adaptiveEstimate k w)
              + 2 * gridCorrection (adaptiveGrid k)) := by
        have hmul := mul_le_mul_of_nonneg_left hsle
          (by positivity : 0 ≤ 2 * gridCorrection (adaptiveGrid k))
        nlinarith
      nlinarith
    have hfail : eps * (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
        < (gridCorrection (adaptiveGrid k)
          + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
          - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 := by
      unfold adaptiveReady at h
      rw [hL1, hU] at h
      by_contra hn
      have hle : (gridCorrection (adaptiveGrid k)
            + Real.sqrt (adaptiveEstimate k w + 2 * (gridCorrection (adaptiveGrid k)) ^ 2)) ^ 2
            - (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
          ≤ eps * (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2 :=
        le_of_not_gt hn
      exact h hle
    have hkey : eps * (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k)) ^ 2
        < 4 * gridCorrection (adaptiveGrid k)
            * (Real.sqrt (adaptiveEstimate k w) + gridCorrection (adaptiveGrid k)) :=
      hfail.trans_le hwidth
    have hres : eps * Real.sqrt (adaptiveEstimate k w) ≤ 8 * gridCorrection (adaptiveGrid k) :=
      notReady_algebra heps heps1 hc hvc' hkey
    have hmul := mul_le_mul_of_nonneg_left hres
      ((by positivity : 0 < (adaptiveGrid k : ℝ)).le)
    have h2 : eps * (adaptiveGrid k : ℝ) * Real.sqrt (adaptiveEstimate k w) ≤ 8 * Real.pi := by
      nlinarith [hmul, hprod]
    exact h2

/-- For `eps ≤ 1`, no record satisfies the readiness test at stage zero. -/
theorem adaptiveReady_zero_stage {w : ℕ} (eps : ℝ) (heps1 : eps ≤ 1) :
    ¬ adaptiveReady eps 0 w := by
  intro h
  have hlow := adaptiveReady_grid_lower eps h
  have hv : Real.sqrt (adaptiveEstimate 0 w) ≤ 1 := by
    have h1 := adaptiveEstimate_le_one 0 w
    have h2 := adaptiveEstimate_nonneg 0 w
    have h3 := Real.sqrt_le_sqrt h1
    have hsqrt1 : √1 = 1 := by norm_num
    nlinarith
  have hgrid : (adaptiveGrid 0 : ℝ) = 2 := by
    unfold adaptiveGrid
    norm_num
  rw [hgrid] at hlow
  have hmul : eps * Real.sqrt (adaptiveEstimate 0 w) ≤ 1 := by
    have h1 : eps * Real.sqrt (adaptiveEstimate 0 w)
        ≤ 1 * Real.sqrt (adaptiveEstimate 0 w) := by
      have hmm := mul_le_mul_of_nonneg_right heps1
        (Real.sqrt_nonneg (adaptiveEstimate 0 w))
      nlinarith
    have h2 : 1 * Real.sqrt (adaptiveEstimate 0 w) ≤ 1 * 1 := by
      have hmm := mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 1)
      nlinarith
    nlinarith
  have hpi : 2 < 4 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hcontra : 4 * Real.pi ≤ 2 := by nlinarith [hlow, hmul]
  linarith

/-- Every adaptive grid size is positive. -/
theorem adaptiveGrid_pos (k : ℕ) : 0 < adaptiveGrid k := by
  unfold adaptiveGrid
  positivity

/-- The natural-number record selected from a run at stage `k`. -/
def adaptiveRun (w : ℕ → ℕ) (k : ℕ) : ℕ := w k

/-- The condition that stage `k` is ready and every earlier stage is not ready. -/
def adaptiveStopsAt (eps : ℝ) (w : ℕ → ℕ) (k : ℕ) : Prop :=
  adaptiveReady eps k (w k) ∧ ∀ j < k, ¬ adaptiveReady eps j (w j)

/-- For `eps ≤ 1`, an adaptive stopping stage has positive index. -/
theorem adaptiveStopsAt_pos {eps : ℝ} {w : ℕ → ℕ} {k : ℕ} (heps1 : eps ≤ 1)
    (h : adaptiveStopsAt eps w k) : 0 < k := by
  by_contra hn
  have hk0 : k = 0 := by omega
  subst hk0
  exact adaptiveReady_zero_stage eps heps1 h.1

/-- A ready stage has a nonzero recorded amplitude estimate. -/
theorem adaptiveReady_estimate_pos {k w : ℕ} (eps : ℝ)
    (h : adaptiveReady eps k w) : adaptiveEstimate k w ≠ 0 := by
  intro hn
  have hz : Real.sqrt (adaptiveEstimate k w) = 0 := by
    rw [Real.sqrt_eq_zero (adaptiveEstimate_nonneg k w)]
    exact hn
  have hc : 0 < gridCorrection (adaptiveGrid k) := gridCorrection_pos (adaptiveGrid_pos k)
  have hL : adaptiveLower k w
      = (max 0 (Real.sqrt (adaptiveEstimate k w) - gridCorrection (adaptiveGrid k))) ^ 2 := by
    unfold adaptiveLower certifiedLowerBound adaptiveEstimate recordEstimate
    rfl
  have hL0 : adaptiveLower k w = 0 := by
    rw [hL, max_eq_left (by linarith)]
    simp
  have hUpos : 0 < adaptiveUpper k w := adaptiveUpper_pos w
  unfold adaptiveReady at h
  rw [hL0] at h
  linarith

/-- For `0 < eps ≤ 1`, the stopping-stage grid size times `eps√v`, using the preceding estimate
`v`, is at most `16π`. -/
theorem adaptiveStopsAt_grid_budget {eps : ℝ} {w : ℕ → ℕ} {k : ℕ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (h : adaptiveStopsAt eps w k) :
    (adaptiveGrid k : ℝ)
      * (eps * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ≤ 16 * Real.pi := by
  have hk : 0 < k := adaptiveStopsAt_pos heps1 h
  have hprev : k - 1 < k := by omega
  have hnot : ¬ adaptiveReady eps (k - 1) (w (k - 1)) := h.2 (k - 1) hprev
  have hup := adaptiveNotReady_grid_upper eps heps heps1 hnot
  have hM1 : (adaptiveGrid (k - 1) : ℝ)
      * (eps * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ≤ 8 * Real.pi := by
    nlinarith [hup]
  have hM2 : (2:ℝ) * (adaptiveGrid (k - 1) : ℝ)
      * (eps * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ≤ 16 * Real.pi := by
    nlinarith [hM1]
  have hgrid : adaptiveGrid k = 2 * adaptiveGrid (k - 1) := by
    have h1 : adaptiveGrid ((k - 1) + 1) = 2 * adaptiveGrid (k - 1) := adaptiveGrid_succ (k - 1)
    have h2 : (k - 1) + 1 = k := Nat.sub_add_cancel (m := 1) (by omega)
    rw [h2] at h1
    exact h1
  have hcast : ((2 * adaptiveGrid (k - 1) : ℕ) : ℝ) = 2 * (adaptiveGrid (k - 1) : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hgrid, hcast]
  nlinarith [hM2]

/-- If the preceding sample is accurate and sufficiently fine, the stopping-stage grid size
times `eps√a` is at most `32π`. -/
theorem adaptiveStopsAt_grid_budget_amplitude {eps : ℝ} {w : ℕ → ℕ} {k : ℕ}
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (h : adaptiveStopsAt eps w k)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |adaptiveEstimate (k - 1) (w (k - 1)) - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid (k - 1)) (MeasureProb (preparedAAState A j) S))
    (hfine : 8 * Real.pi
        ≤ (adaptiveGrid (k - 1) : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    (adaptiveGrid k : ℝ) * (eps * Real.sqrt (MeasureProb (preparedAAState A j) S))
      ≤ 32 * Real.pi := by
  have hk : 0 < k := adaptiveStopsAt_pos heps1 h
  have hprev : k - 1 < k := by omega
  have hnot : ¬ adaptiveReady eps (k - 1) (w (k - 1)) := h.2 (k - 1) hprev
  have hup := adaptiveNotReady_grid_upper eps heps heps1 hnot

  have hM0 : 0 < adaptiveGrid (k - 1) := adaptiveGrid_pos (k - 1)
  have hscale : gridCorrection (adaptiveGrid (k - 1))
      ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 8 :=
    gridCorrection_le_eighth hM0 _ (measureProb_nonneg _ _) hfine
  have hlow : MeasureProb (preparedAAState A j) S / 4
      ≤ adaptiveLower (k - 1) (w (k - 1)) := by
    have h1 : MeasureProb (preparedAAState A j) S / 4
        ≤ certifiedLowerBound (adaptiveGrid (k - 1)) (adaptiveLabel (k - 1) (w (k - 1))) :=
      certifiedLowerBound_ge_quarter hM0 A j S hA (adaptiveLabel (k - 1) (w (k - 1)))
        ha1 hscale hw
    unfold adaptiveLower
    exact h1
  have hrec : adaptiveLower (k - 1) (w (k - 1))
      ≤ adaptiveEstimate (k - 1) (w (k - 1)) := by
    have h1 := certifiedLowerBound_le_record hM0 (adaptiveLabel (k - 1) (w (k - 1)))
    unfold adaptiveLower
    exact h1
  have hvsq : (Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ^ 2
      = adaptiveEstimate (k - 1) (w (k - 1)) :=
    Real.sq_sqrt (adaptiveEstimate_nonneg (k - 1) (w (k - 1)))
  have hva : Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))
      ≥ Real.sqrt (MeasureProb (preparedAAState A j) S) / 2 := by
    have hsq : (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ^ 2
        = MeasureProb (preparedAAState A j) S / 4 := by
      have h1 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
          = MeasureProb (preparedAAState A j) S := Real.sq_sqrt (measureProb_nonneg _ _)
      nlinarith [h1]
    have h1 : (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ^ 2
        ≤ (Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ^ 2 := by
      nlinarith [hlow, hrec, hvsq]
    have h2 : 0 ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 2 :=
      div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    have h3 : 0 ≤ Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1))) := Real.sqrt_nonneg _
    have h4 := (sq_le_sq₀ h2 h3).mp h1
    nlinarith

  have hM1 : (adaptiveGrid (k - 1) : ℝ)
      * (eps * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ≤ 8 * Real.pi := by
    nlinarith [hup]
  have hM1' : (adaptiveGrid (k - 1) : ℝ)
      * (eps * Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ≤ 8 * Real.pi := by
    have hstep : eps * (adaptiveGrid (k - 1) : ℝ)
        * (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2)
        ≤ eps * (adaptiveGrid (k - 1) : ℝ)
          * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1))) := by
      have hmul := mul_le_mul_of_nonneg_left hva
        (by positivity : 0 ≤ eps * (adaptiveGrid (k - 1) : ℝ))
      nlinarith
    nlinarith
  have hM2 : (2:ℝ) * (adaptiveGrid (k - 1) : ℝ)
      * (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) ≤ 32 * Real.pi := by
    nlinarith [hM1']
  have hgrid : adaptiveGrid k = 2 * adaptiveGrid (k - 1) := by
    have h1 : adaptiveGrid ((k - 1) + 1) = 2 * adaptiveGrid (k - 1) := adaptiveGrid_succ (k - 1)
    have h2 : (k - 1) + 1 = k := Nat.sub_add_cancel (m := 1) (by omega)
    rw [h2] at h1
    exact h1
  have hcast : ((2 * adaptiveGrid (k - 1) : ℕ) : ℝ) = 2 * (adaptiveGrid (k - 1) : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hgrid, hcast]
  nlinarith [hM2]

/-- The finite Born distribution of the prepared AE phase label at adaptive stage `k`. -/
noncomputable def adaptiveStageLaw (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : FinDist (Fin (adaptiveGrid k)) :=
  aeLaw (adaptiveGrid k) A j S hA (adaptiveGrid_two k)

/-- Each adaptive stage probability equals the corresponding frozen prepared AE-law probability. -/
theorem adaptiveStageLaw_eq_frozen (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (z : Fin (adaptiveGrid k)) :
    (adaptiveStageLaw k A j S hA).prob z
      = (aeLaw (adaptiveGrid k) A j S hA (adaptiveGrid_two k)).prob z := rfl

/-- An adaptive stage label's probability is its phase-register Born probability in the counted
AE circuit. -/
theorem adaptiveStageLaw_prob_eq_born (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (z : Fin (adaptiveGrid k)) :
    (adaptiveStageLaw k A j S hA).prob z
      = MeasureProb
          (Run (aeControlledGate (adaptiveGrid k) (preparedMark S))
            (countedAECircuit (adaptiveGrid k) A j)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, adaptiveGrid_pos k⟩ : Fin (adaptiveGrid k)))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
          (Finset.univ.filter (fun p => p.1 = z)) := rfl

/-- The adaptive stage label probabilities sum to one. -/
theorem adaptiveStageLaw_sum_one (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ z : Fin (adaptiveGrid k), (adaptiveStageLaw k A j S hA).prob z) = 1 :=
  (adaptiveStageLaw k A j S hA).sum_one

/-- The AE success window has probability at least `8/π²` under every adaptive stage law
[BrassardEtAl2002]. -/
theorem adaptiveStageLaw_window_mass (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
        |aeEstimate (adaptiveGrid k) z - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S)),
      (adaptiveStageLaw k A j S hA).prob z) ≥ 8 / Real.pi ^ 2 := by
  have h := (prepared_ae_bhmt_error_and_endpoints (adaptiveGrid k) (adaptiveGrid_two k)
    A j S hA).1
  simpa only [nextAeWindow, adaptiveStageLaw] using! h

/-- The AE success window has probability at least `2/3` under every adaptive stage law. -/
theorem adaptiveStageLaw_failure_le_third (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
        |aeEstimate (adaptiveGrid k) z - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S)),
      (adaptiveStageLaw k A j S hA).prob z) ≥ 2 / 3 := by
  have h := adaptiveStageLaw_window_mass k A j S hA
  have hpi : Real.pi ^ 2 ≤ 12 := by
    have hlt : Real.pi < 3.1416 := Real.pi_lt_d4
    nlinarith [Real.pi_pos]
  have hpos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hfrac : (2 / 3 : ℝ) ≤ 8 / Real.pi ^ 2 := by
    rw [le_div_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hpi (by norm_num : (0:ℝ) ≤ 2 / 3)
    linarith
  linarith

/-- At zero marked probability, label zero has probability one, its estimate is zero, and it
satisfies the relative-error inequality for any `eps`. -/
theorem adaptiveStageLaw_zero (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (eps : ℝ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    (adaptiveStageLaw k A j S hA).prob ⟨0, adaptiveGrid_pos k⟩ = 1 ∧
      aeEstimate (adaptiveGrid k) ⟨0, adaptiveGrid_pos k⟩ = 0 ∧
      |aeEstimate (adaptiveGrid k) ⟨0, adaptiveGrid_pos k⟩ - 0| ≤ eps * 0 := by
  have h := (prepared_ae_bhmt_error_and_endpoints (adaptiveGrid k) (adaptiveGrid_two k)
    A j S hA).2.1 ha
  refine ⟨?_, ?_, ?_⟩
  · simpa only [adaptiveStageLaw] using! h
  · have hz : ((⟨0, adaptiveGrid_pos k⟩ : Fin (adaptiveGrid k)).val : ℝ) = 0 := by simp
    unfold aeEstimate
    rw [hz, mul_zero, zero_div, Real.sin_zero]
    norm_num
  · have hz0 : aeEstimate (adaptiveGrid k) ⟨0, adaptiveGrid_pos k⟩ = 0 := by
      have hz : ((⟨0, adaptiveGrid_pos k⟩ : Fin (adaptiveGrid k)).val : ℝ) = 0 := by simp
      unfold aeEstimate
      rw [hz, mul_zero, zero_div, Real.sin_zero]
      norm_num
    rw [hz0]
    norm_num

/-- At marked probability one, estimates equal to one have total stage probability one. -/
theorem adaptiveStageLaw_one (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 1) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
        aeEstimate (adaptiveGrid k) z = 1),
      (adaptiveStageLaw k A j S hA).prob z) = 1 := by
  have hdiv : 2 ∣ adaptiveGrid k := by
    unfold adaptiveGrid
    rw [pow_succ]
    exact ⟨2 ^ k, by ring⟩
  have h := (prepared_ae_bhmt_error_and_endpoints (adaptiveGrid k) (adaptiveGrid_two k)
    A j S hA).2.2 ha hdiv
  simpa only [adaptiveStageLaw] using! h

/-- Compute the stage's forward and backward preparation accesses, marking queries, ordinary
gates, and fixed flag and Fourier macro counts. -/
theorem adaptiveStage_access_counts (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid k)) = adaptiveGrid k ∧
      aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid k)) = adaptiveGrid k - 1 ∧
      QueryCount (countedAECircuit (adaptiveGrid k) A j) = adaptiveGrid k - 1 ∧
      GateCount (countedAECircuit (adaptiveGrid k) A j) = 5 * (adaptiveGrid k - 1) + 3 ∧
      aeFixedMacros (aeFlagAccessWord (I := I) (adaptiveGrid k)) = 2 * (adaptiveGrid k - 1) ∧
      aeFixedMacros (aeFourierAccessWord (I := I) (adaptiveGrid k)) = 2 :=
  nextRelative_access_counts (adaptiveGrid k) (adaptiveGrid_two k) A j S hA

/-- The sum of adaptive grid sizes at stages below `k`, plus two, equals the grid size at stage
`k`. -/
theorem adaptiveGrid_sum_lt (k : ℕ) :
    (∑ j ∈ Finset.range k, adaptiveGrid j) + 2 = adaptiveGrid k := by
  induction k with
  | zero => simp [adaptiveGrid]
  | succ k ih =>
      have hsucc := adaptiveGrid_succ k
      have hsum : (∑ j ∈ Finset.range (k + 1), adaptiveGrid j)
          = (∑ j ∈ Finset.range k, adaptiveGrid j) + adaptiveGrid k := by
        rw [Finset.sum_range_succ]
      rw [hsum, hsucc]
      omega

/-- The sum of forward preparation accesses at stages below `k`, plus two, equals the stage-`k`
grid size. -/
theorem adaptiveStage_forward_sum (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ j ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j)))
      + 2 = adaptiveGrid k := by
  simp_rw [(adaptiveStage_access_counts _ A j S hA).1]
  exact adaptiveGrid_sum_lt k

/-- The stage-`k` adaptive grid size is at least `k + 2`. -/
theorem adaptiveGrid_ge_two_add_k (k : ℕ) : k + 2 ≤ adaptiveGrid k := by
  induction k with
  | zero => simp [adaptiveGrid]
  | succ k ih =>
      have hsucc := adaptiveGrid_succ k
      omega

/-- The total forward preparation accesses at stages below `k` equal `adaptiveGrid k - 2`. -/
theorem adaptiveTotal_forward_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j)))
      = adaptiveGrid k - 2 := by
  induction k with
  | zero => simp [adaptiveGrid]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h1 : aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid k)) = adaptiveGrid k :=
        (prepared_ae_separate_access_counts (adaptiveGrid k) (adaptiveGrid_pos k)).1
      rw [h1, ih]
      have hsucc := adaptiveGrid_succ k
      have htwo := adaptiveGrid_two k
      omega

/-- The total forward preparation accesses at stages below `k`, plus two, equal `adaptiveGrid
k`. -/
theorem adaptiveTotal_forward (k : ℕ) :
    (∑ j ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j))) + 2
      = adaptiveGrid k := by
  have h := adaptiveTotal_forward_sum (I := I) k
  have htwo := adaptiveGrid_two k
  omega

/-- The total backward preparation accesses at stages below `k` equal `adaptiveGrid k - 2 - k`. -/
theorem adaptiveTotal_backward_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j)))
      = adaptiveGrid k - 2 - k := by
  induction k with
  | zero => simp [adaptiveGrid]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h1 : aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid k))
          = adaptiveGrid k - 1 :=
        (prepared_ae_separate_access_counts (adaptiveGrid k) (adaptiveGrid_pos k)).2.1
      rw [h1, ih]
      have hsucc := adaptiveGrid_succ k
      have htwo := adaptiveGrid_two k
      have hdom := adaptiveGrid_ge_two_add_k k
      omega

/-- The total backward preparation accesses at stages below `k`, plus `k + 2`, equal
`adaptiveGrid k`. -/
theorem adaptiveTotal_backward (k : ℕ) :
    (∑ j ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j))) + (k + 2)
      = adaptiveGrid k := by
  have h := adaptiveTotal_backward_sum (I := I) k
  have htwo := adaptiveGrid_two k
  have hdom := adaptiveGrid_ge_two_add_k k
  omega

/-- The total marking queries at stages below `k` equal `adaptiveGrid k - 2 - k`. -/
theorem adaptiveTotal_mark_sum (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) :
    (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j))
      = adaptiveGrid k - 2 - k := by
  induction k with
  | zero => simp [adaptiveGrid]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h1 : QueryCount (countedAECircuit (adaptiveGrid k) A j) = adaptiveGrid k - 1 :=
        (adaptiveStage_access_counts k A j S hA).2.2.1
      rw [h1, ih]
      have hsucc := adaptiveGrid_succ k
      have htwo := adaptiveGrid_two k
      have hdom := adaptiveGrid_ge_two_add_k k
      omega

/-- The total marking queries at stages below `k`, plus `k + 2`, equal `adaptiveGrid k`. -/
theorem adaptiveTotal_mark (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) :
    (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j)) + (k + 2)
      = adaptiveGrid k := by
  have h := adaptiveTotal_mark_sum (I := I) A j S hA k
  have htwo := adaptiveGrid_two k
  have hdom := adaptiveGrid_ge_two_add_k k
  omega

/-- For positive marked probability `a` and `0 < eps ≤ 1`, stopping with an accurate preceding
sample bounds each accumulated forward, backward, and marking count before stage `k` by `32π
/ (eps√a)`. -/
theorem adaptiveStopsAt_total_budget {eps : ℝ} {w : ℕ → ℕ} {k : ℕ}
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (h : adaptiveStopsAt eps w k)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |adaptiveEstimate (k - 1) (w (k - 1)) - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid (k - 1)) (MeasureProb (preparedAAState A j) S)) :
    (∑ j' ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
        ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) ∧
    (∑ j' ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
        ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) ∧
    (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j))
        ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) := by
  have hk : 0 < k := adaptiveStopsAt_pos heps1 h
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtpos : 0 < Real.sqrt (MeasureProb (preparedAAState A j) S) :=
    Real.sqrt_pos.2 ha0
  have hgrid : adaptiveGrid k = 2 * adaptiveGrid (k - 1) := by
    have h1 : adaptiveGrid ((k - 1) + 1) = 2 * adaptiveGrid (k - 1) := adaptiveGrid_succ (k - 1)
    have h2 : (k - 1) + 1 = k := Nat.sub_add_cancel (m := 1) (by omega)
    rw [h2] at h1
    exact h1
  have hM : (adaptiveGrid k : ℝ) * (eps * Real.sqrt (MeasureProb (preparedAAState A j) S))
      ≤ 32 * Real.pi := by
    by_cases hfine : 8 * Real.pi
        ≤ (adaptiveGrid (k - 1) : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S)
    · exact adaptiveStopsAt_grid_budget_amplitude A j S hA heps heps1 h ha1 hw hfine
    · have hcoarse : (adaptiveGrid (k - 1) : ℝ)
          * Real.sqrt (MeasureProb (preparedAAState A j) S) < 8 * Real.pi :=
        lt_of_not_ge hfine
      have hcast : ((2 * adaptiveGrid (k - 1) : ℕ) : ℝ)
          = 2 * (adaptiveGrid (k - 1) : ℝ) := by
        rw [Nat.cast_mul]
        norm_num
      rw [hgrid, hcast]
      have hmul : (2 * (adaptiveGrid (k - 1) : ℝ))
          * (eps * Real.sqrt (MeasureProb (preparedAAState A j) S))
          ≤ 2 * eps * (8 * Real.pi) := by
        have h2 : 0 ≤ 2 * eps := by positivity
        have h3 : (adaptiveGrid (k - 1) : ℝ)
            * Real.sqrt (MeasureProb (preparedAAState A j) S) ≤ 8 * Real.pi :=
          le_of_lt hcoarse
        have h4 := mul_le_mul_of_nonneg_left h3 h2
        nlinarith
      have hsmall : 2 * eps * (8 * Real.pi) ≤ 32 * Real.pi := by nlinarith
      nlinarith [hmul, hsmall]
  have hMbudget : (adaptiveGrid k : ℝ)
      ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) := by
    have hden : 0 < eps * Real.sqrt (MeasureProb (preparedAAState A j) S) := mul_pos heps hsqrtpos
    have h1 := (le_div_iff₀ hden).mpr hM
    exact h1
  have hfwd : (∑ j' ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
      ≤ (adaptiveGrid k : ℝ) := by
    have h := adaptiveTotal_forward (I := I) k
    have h2 : (∑ j' ∈ Finset.range k,
        aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) + 2 ≤ adaptiveGrid k := by
      rw [h]
    have h3 : (∑ j' ∈ Finset.range k,
        aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) ≤ adaptiveGrid k := by omega
    exact Nat.cast_le.mpr h3
  have hbwd : (∑ j' ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
      ≤ (adaptiveGrid k : ℝ) := by
    have h := adaptiveTotal_backward (I := I) k
    have h2 : (∑ j' ∈ Finset.range k,
        aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) + (k + 2) ≤ adaptiveGrid k := by
      rw [h]
    have h3 : (∑ j' ∈ Finset.range k,
        aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) ≤ adaptiveGrid k := by omega
    exact Nat.cast_le.mpr h3
  have hmark : (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j))
      ≤ (adaptiveGrid k : ℝ) := by
    have h := adaptiveTotal_mark (I := I) A j S hA k
    have h2 : (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j)) + (k + 2)
        ≤ adaptiveGrid k := by
      rw [h]
    have h3 : (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j))
        ≤ adaptiveGrid k := by omega
    exact Nat.cast_le.mpr h3
  exact ⟨hfwd.trans hMbudget, hbwd.trans hMbudget, hmark.trans hMbudget⟩

/-- For `a > 0` and `0 < eps ≤ 1`, an accurate stage sample is ready whenever `32π ≤ eps` times
its grid size times `√a`. -/
theorem adaptiveFires_at_fine_stage {k w : ℕ} (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |adaptiveEstimate k w - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S))
    (hfine : 32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ)
        * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    adaptiveReady eps k w := by
  by_contra hn
  have hnot : ¬ adaptiveReady eps k w := hn
  have hup := adaptiveNotReady_grid_upper eps heps heps1 hnot
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < adaptiveGrid k := adaptiveGrid_pos k

  have hscale : gridCorrection (adaptiveGrid k)
      ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 8 := by
    have h1 : 8 * Real.pi
        ≤ (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S) := by
      have h2 : 8 * Real.pi ≤ 32 * Real.pi := by nlinarith [Real.pi_pos]
      have h3 : 32 * Real.pi
          ≤ eps * (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S) := hfine
      have h4 : eps * (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S)
          ≤ (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S) := by
        have hmul := mul_le_mul_of_nonneg_right heps1
          (by positivity : 0 ≤ (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S))
        nlinarith
      nlinarith
    exact gridCorrection_le_eighth hM0 _ (measureProb_nonneg _ _) h1
  have hlow : MeasureProb (preparedAAState A j) S / 4 ≤ adaptiveLower k w := by
    have h1 := certifiedLowerBound_ge_quarter hM0 A j S hA (adaptiveLabel k w) ha1 hscale hw
    unfold adaptiveLower
    exact h1
  have hrec : adaptiveLower k w ≤ adaptiveEstimate k w := by
    have h1 := certifiedLowerBound_le_record hM0 (adaptiveLabel k w)
    unfold adaptiveLower
    exact h1
  have hvsq : (Real.sqrt (adaptiveEstimate k w)) ^ 2 = adaptiveEstimate k w :=
    Real.sq_sqrt (adaptiveEstimate_nonneg k w)
  have hva : Real.sqrt (MeasureProb (preparedAAState A j) S) / 2
      ≤ Real.sqrt (adaptiveEstimate k w) := by
    have hsq : (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ^ 2
        = MeasureProb (preparedAAState A j) S / 4 := by
      have h1 : (Real.sqrt (MeasureProb (preparedAAState A j) S)) ^ 2
          = MeasureProb (preparedAAState A j) S := Real.sq_sqrt (measureProb_nonneg _ _)
      nlinarith [h1]
    have h1 : (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2) ^ 2
        ≤ (Real.sqrt (adaptiveEstimate k w)) ^ 2 := by
      rw [hsq]
      nlinarith [hlow, hrec, hvsq]
    have h2 : 0 ≤ Real.sqrt (MeasureProb (preparedAAState A j) S) / 2 :=
      div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    have h3 : 0 ≤ Real.sqrt (adaptiveEstimate k w) := Real.sqrt_nonneg _
    have h4 := (sq_le_sq₀ h2 h3).mp h1
    nlinarith

  have h1 : eps * (adaptiveGrid k : ℝ) * (Real.sqrt (MeasureProb (preparedAAState A j) S) / 2)
      ≤ 8 * Real.pi := by
    have hmul := mul_le_mul_of_nonneg_left hva
      (by positivity : 0 ≤ eps * (adaptiveGrid k : ℝ))
    nlinarith
  have h2 : eps * (adaptiveGrid k : ℝ) * Real.sqrt (MeasureProb (preparedAAState A j) S)
      ≤ 16 * Real.pi := by nlinarith
  nlinarith [hfine]

/-- An accurate sufficiently fine stage is a stopping stage if every earlier stage is not ready. -/
theorem adaptiveStopsAt_fine_stage {k : ℕ} {w : ℕ → ℕ} (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |adaptiveEstimate k (w k) - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S))
    (hfine : 32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ)
        * Real.sqrt (MeasureProb (preparedAAState A j) S))
    (hprior : ∀ j < k, ¬ adaptiveReady eps j (w j)) :
    adaptiveStopsAt eps w k :=
  ⟨adaptiveFires_at_fine_stage eps heps heps1 A j S hA ha0 ha1 hw hfine, hprior⟩

/-- An accurate sufficiently fine sample at stage `J` ensures that some stage at or before `J`
is the first ready stage. -/
theorem adaptiveStopsAt_or_before {J : ℕ} {w : ℕ → ℕ} (eps : ℝ) (heps : 0 < eps)
    (heps1 : eps ≤ 1)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hwJ : |adaptiveEstimate J (w J) - MeasureProb (preparedAAState A j) S|
        ≤ nextAeWindow (adaptiveGrid J) (MeasureProb (preparedAAState A j) S))
    (hfineJ : 32 * Real.pi ≤ eps * (adaptiveGrid J : ℝ)
        * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    ∃ k ≤ J, adaptiveStopsAt eps w k := by
  have hreadyJ : adaptiveReady eps J (w J) :=
    adaptiveFires_at_fine_stage eps heps heps1 A j S hA ha0 ha1 hwJ hfineJ
  have hex : ∃ n, adaptiveReady eps n (w n) := ⟨J, hreadyJ⟩
  have hk : adaptiveReady eps (Nat.find hex) (w (Nat.find hex)) := Nat.find_spec hex
  have hkJ : Nat.find hex ≤ J := by
    by_contra hn
    have hlt : J < Nat.find hex := by omega
    have hnot := Nat.find_min hex hlt
    exact hnot hreadyJ
  refine ⟨Nat.find hex, hkJ, hk, fun m hm => Nat.find_min hex hm⟩

/-- Combine stage success-window mass, conditional relative accuracy, readiness scale bounds,
the zero endpoint, and stopping-stage resources for prepared AE [BrassardEtAl2002]. -/
theorem frontier1 (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (w : ℕ → ℕ) (k : ℕ) :
    (∀ j' : ℕ,

      (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid j') =>
          |aeEstimate (adaptiveGrid j') z - MeasureProb (preparedAAState A j) S|
            ≤ nextAeWindow (adaptiveGrid j') (MeasureProb (preparedAAState A j) S)),
          (adaptiveStageLaw j' A j S hA).prob z) ≥ 8 / Real.pi ^ 2 ∧

      (|adaptiveEstimate j' (w j') - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid j') (MeasureProb (preparedAAState A j) S) →
        adaptiveReady eps j' (w j') →
        |adaptiveEstimate j' (w j') - MeasureProb (preparedAAState A j) S|
          ≤ eps * MeasureProb (preparedAAState A j) S) ∧

      (adaptiveReady eps j' (w j') →
          4 * Real.pi ≤ eps * (adaptiveGrid j' : ℝ) * Real.sqrt (adaptiveEstimate j' (w j'))) ∧
      (¬ adaptiveReady eps j' (w j') →
          eps * (adaptiveGrid j' : ℝ) * Real.sqrt (adaptiveEstimate j' (w j'))
            ≤ 8 * Real.pi))
    ∧

    (MeasureProb (preparedAAState A j) S = 0 →
      ∀ j' : ℕ, (adaptiveStageLaw j' A j S hA).prob ⟨0, adaptiveGrid_pos j'⟩ = 1 ∧
        aeEstimate (adaptiveGrid j') ⟨0, adaptiveGrid_pos j'⟩ = 0 ∧
        |aeEstimate (adaptiveGrid j') ⟨0, adaptiveGrid_pos j'⟩ - 0| ≤ eps * 0)
    ∧

    (adaptiveStopsAt eps w k →
      (∑ j' ∈ Finset.range k, adaptiveGrid j') + 2 = adaptiveGrid k ∧
        aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid k)) = adaptiveGrid k ∧
        aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid k)) = adaptiveGrid k - 1 ∧
        QueryCount (countedAECircuit (adaptiveGrid k) A j) = adaptiveGrid k - 1 ∧
        GateCount (countedAECircuit (adaptiveGrid k) A j) = 5 * (adaptiveGrid k - 1) + 3 ∧
        (adaptiveGrid k : ℝ)
          * (eps * Real.sqrt (adaptiveEstimate (k - 1) (w (k - 1)))) ≤ 16 * Real.pi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j'
    refine ⟨adaptiveStageLaw_window_mass j' A j S hA, ?_, ?_, ?_⟩
    · intro hw hready
      exact certifiedStop_relative_band_at_stage eps heps A j S hA ha1 hw hready
    · intro hready
      exact adaptiveReady_grid_lower eps hready
    · intro hnot
      exact adaptiveNotReady_grid_upper eps heps heps1 hnot
  · intro ha j'
    exact adaptiveStageLaw_zero j' A j S hA eps ha
  · intro hst
    refine ⟨adaptiveGrid_sum_lt k, ?_, ?_, ?_, ?_, ?_⟩
    · exact (adaptiveStage_access_counts k A j S hA).1
    · exact (adaptiveStage_access_counts k A j S hA).2.1
    · exact (adaptiveStage_access_counts k A j S hA).2.2.1
    · exact (adaptiveStage_access_counts k A j S hA).2.2.2.1
    · exact adaptiveStopsAt_grid_budget heps heps1 hst

/-- Combine exact cumulative access identities, conditional stopping budgets, and readiness and
stopping at sufficiently fine accurate stages for positive marked probability. -/
theorem frontier2 (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (w : ℕ → ℕ) (k : ℕ) :

    ((∑ j' ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) + 2
        = adaptiveGrid k ∧
      (∑ j' ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j'))) + (k + 2)
        = adaptiveGrid k ∧
      (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j)) + (k + 2)
        = adaptiveGrid k) ∧

    (adaptiveStopsAt eps w k →
      |adaptiveEstimate (k - 1) (w (k - 1)) - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid (k - 1)) (MeasureProb (preparedAAState A j) S) →
      (∑ j' ∈ Finset.range k, aeForwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
          ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) ∧
        (∑ j' ∈ Finset.range k, aeBackwardAccesses (aeAccessWord (I := I) (adaptiveGrid j')))
          ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S)) ∧
        (∑ j' ∈ Finset.range k, QueryCount (countedAECircuit (adaptiveGrid j') A j))
          ≤ 32 * Real.pi / (eps * Real.sqrt (MeasureProb (preparedAAState A j) S))) ∧

    ((∀ k' w',
        |adaptiveEstimate k' w' - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid k') (MeasureProb (preparedAAState A j) S) →
        32 * Real.pi ≤ eps * (adaptiveGrid k' : ℝ)
          * Real.sqrt (MeasureProb (preparedAAState A j) S) →
        adaptiveReady eps k' w') ∧
      (∀ J,
        |adaptiveEstimate J (w J) - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid J) (MeasureProb (preparedAAState A j) S) →
        32 * Real.pi ≤ eps * (adaptiveGrid J : ℝ)
          * Real.sqrt (MeasureProb (preparedAAState A j) S) →
        ∃ k' ≤ J, adaptiveStopsAt eps w k')) := by
  refine ⟨⟨adaptiveTotal_forward k, adaptiveTotal_backward k,
    adaptiveTotal_mark A j S hA k⟩, ?_, ?_⟩
  · intro hst hw
    exact adaptiveStopsAt_total_budget A j S hA heps heps1 hst ha0 ha1 hw
  · refine ⟨?_, ?_⟩
    · intro k' w' hw hfine
      exact adaptiveFires_at_fine_stage eps heps heps1 A j S hA ha0 ha1 hw hfine
    · intro J hw hfine
      exact adaptiveStopsAt_or_before eps heps heps1 A j S hA ha0 ha1 hw hfine

/-- The adaptive estimate of record zero is zero at every stage. -/
theorem adaptiveEstimate_zero (k : ℕ) : adaptiveEstimate k 0 = 0 := by
  simp only [adaptiveEstimate, recordEstimate, aeEstimate]
  have hval : ((adaptiveLabel k 0 : Fin (adaptiveGrid k)).val : ℝ) = 0 := by
    unfold adaptiveLabel adaptiveGrid
    simp
  rw [hval, mul_zero, zero_div, Real.sin_zero]
  norm_num

/-- The condition that a stage's recorded amplitude estimate is zero. -/
def adaptiveZeroReady (k w : ℕ) : Prop := adaptiveEstimate k w = 0

/-- Record zero satisfies `adaptiveZeroReady` at every stage. -/
theorem adaptiveZeroReady_zero (k : ℕ) : adaptiveZeroReady k 0 := by
  unfold adaptiveZeroReady
  exact adaptiveEstimate_zero k

/-- A zero recorded amplitude estimate gives a zero adaptive certified lower endpoint. -/
theorem adaptiveLower_of_estimate_zero {k w : ℕ}
    (h : recordEstimate (adaptiveGrid k) (adaptiveLabel k w) = 0) :
    adaptiveLower k w = 0 := by
  unfold adaptiveLower certifiedLowerBound
  rw [h, Real.sqrt_zero]
  have hc : 0 ≤ gridCorrection (adaptiveGrid k) := gridCorrection_nonneg (adaptiveGrid_pos k)
  rw [max_eq_left (by linarith)]
  norm_num

/-- For positive `eps`, a zero adaptive estimate fails the positive relative-readiness test. -/
theorem adaptiveNotReady_zero {k w : ℕ} (eps : ℝ) (heps : 0 < eps)
    (h : adaptiveEstimate k w = 0) : ¬ adaptiveReady eps k w := by
  intro hready
  have hU : 0 < adaptiveUpper k w := adaptiveUpper_pos w
  have hL : adaptiveLower k w = 0 := by
    apply adaptiveLower_of_estimate_zero
    exact h
  unfold adaptiveReady at hready
  rw [hL] at hready
  linarith

/-- At zero marked probability, record zero has probability one, satisfies the zero branch and
relative-error inequality, and fails the positive-readiness test. -/
theorem adaptiveStageLaw_zero_branch (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (eps : ℝ) (heps : 0 < eps)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    (adaptiveStageLaw k A j S hA).prob ⟨0, adaptiveGrid_pos k⟩ = 1 ∧
      adaptiveEstimate k 0 = 0 ∧
      adaptiveZeroReady k 0 ∧
      |adaptiveEstimate k 0 - 0| ≤ eps * 0 ∧
      ¬ adaptiveReady eps k 0 := by
  have h := adaptiveStageLaw_zero k A j S hA eps ha
  have hest : adaptiveEstimate k 0 = 0 := adaptiveEstimate_zero k
  refine ⟨h.1, hest, adaptiveZeroReady_zero k, ?_, ?_⟩
  · rw [hest]
    norm_num
  · exact adaptiveNotReady_zero eps heps hest

/-- Package the deterministic zero-amplitude stage law, zero-branch certification, exact
estimate, and failure of positive readiness. -/
theorem frontier3 (k : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (eps : ℝ) (heps : 0 < eps)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    (adaptiveStageLaw k A j S hA).prob ⟨0, adaptiveGrid_pos k⟩ = 1 ∧
      adaptiveEstimate k 0 = 0 ∧
      adaptiveZeroReady k 0 ∧
      |adaptiveEstimate k 0 - 0| ≤ eps * 0 ∧
      ¬ adaptiveReady eps k 0 :=
  adaptiveStageLaw_zero_branch k A j S hA eps heps ha

/-- An earlier adaptive grid is no larger than the grid at stage `N`. -/
theorem adaptiveGrid_le (N k : ℕ) (hk : k < N) : adaptiveGrid k ≤ adaptiveGrid N := by
  unfold adaptiveGrid
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Reduce a label from the common stage-`N` grid modulo the grid at stage `k`. -/
def adaptiveRunLabel {N : ℕ} (k : ℕ) (z : Fin (adaptiveGrid N)) : Fin (adaptiveGrid k) :=
  ⟨z.val % adaptiveGrid k, Nat.mod_lt _ (by unfold adaptiveGrid; positivity)⟩

/-- A common-grid label already smaller than the stage grid keeps its natural-number value under
`adaptiveRunLabel`. -/
theorem adaptiveRunLabel_of_lt {N : ℕ} (k : ℕ) (z : Fin (adaptiveGrid N))
    (h : z.val < adaptiveGrid k) : adaptiveRunLabel k z = ⟨z.val, h⟩ := by
  apply Fin.ext
  simp [adaptiveRunLabel, Nat.mod_eq_of_lt h]

/-- Embed an earlier stage label into the common stage-`N` grid without changing its value. -/
def adaptiveGridEmbed {N k : ℕ} (hk : k < N) (z : Fin (adaptiveGrid k)) : Fin (adaptiveGrid N) :=
  ⟨z.val, Nat.lt_of_lt_of_le z.isLt (adaptiveGrid_le N k hk)⟩

/-- Extend the stage-`k` probability mass to the common stage-`N` grid by assigning zero outside
the stage grid. -/
noncomputable def adaptiveStageProbAt (N k : ℕ) (hk : k < N)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin (adaptiveGrid N)) : ℝ :=
  if z.val < adaptiveGrid k then
    (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z)
  else 0

/-- Every extended stage probability is nonnegative. -/
theorem adaptiveStageProbAt_nonneg (N k : ℕ) (hk : k < N)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (z : Fin (adaptiveGrid N)) : 0 ≤ adaptiveStageProbAt N k hk A j S hA z := by
  unfold adaptiveStageProbAt
  split
  · exact (adaptiveStageLaw k A j S hA).nonneg _
  · exact le_rfl

/-- A weighted sum against the extended stage law equals the corresponding weighted sum on the
original grid after label embedding. -/
theorem adaptiveStageProbAt_weighted (N k : ℕ) (hk : k < N)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (g : Fin (adaptiveGrid N) → ℝ) :
    (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z * g z)
      = ∑ z : Fin (adaptiveGrid k), (adaptiveStageLaw k A j S hA).prob z
          * g (adaptiveGridEmbed hk z) := by
  classical
  have hle : adaptiveGrid k ≤ adaptiveGrid N := adaptiveGrid_le N k hk

  have h1 : (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z * g z)
      = ∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
          (fun z => z.val < adaptiveGrid k),
          (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z := by
    have h1' : (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z * g z)
        = ∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))),
            (if z.val < adaptiveGrid k then
              (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z else 0) := by
      unfold adaptiveStageProbAt
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : z.val < adaptiveGrid k
      · simp only [if_pos h]
      · simp only [if_neg h, zero_mul]
    have hpart := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin (adaptiveGrid N)))
      (fun z => z.val < adaptiveGrid k)
      (fun z => (if z.val < adaptiveGrid k then
        (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z else 0))
    have hA' : (∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
          (fun z => z.val < adaptiveGrid k),
          (if z.val < adaptiveGrid k then
            (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z else 0))
        = ∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
          (fun z => z.val < adaptiveGrid k),
          (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [if_pos (Finset.mem_filter.mp hz).2]
    have hB' : (∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
          (fun z => ¬ (z.val < adaptiveGrid k)),
          (if z.val < adaptiveGrid k then
            (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z else 0)) = 0 := by
      rw [Finset.sum_eq_zero]
      intro z hz
      simp only [if_neg (Finset.mem_filter.mp hz).2]
    rw [h1', hpart.symm, hA', hB', add_zero]

  have h2 : (∑ z ∈ (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
        (fun z => z.val < adaptiveGrid k),
        (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z)
      = ∑ z : Fin (adaptiveGrid k), (adaptiveStageLaw k A j S hA).prob z
          * g (adaptiveGridEmbed hk z) := by
    refine (Finset.sum_nbij' (s := (Finset.univ : Finset (Fin (adaptiveGrid k))))
      (t := (Finset.univ : Finset (Fin (adaptiveGrid N))).filter
        (fun z => z.val < adaptiveGrid k))
      (f := fun z => (adaptiveStageLaw k A j S hA).prob z * g (adaptiveGridEmbed hk z))
      (g := fun z => (adaptiveStageLaw k A j S hA).prob (adaptiveRunLabel k z) * g z)
      (i := adaptiveGridEmbed hk) (j := adaptiveRunLabel k) ?_ ?_ ?_ ?_ ?_).symm
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isLt⟩
    · intro a ha
      exact Finset.mem_univ _
    · intro a ha
      apply Fin.ext
      simp [adaptiveRunLabel, adaptiveGridEmbed, Nat.mod_eq_of_lt a.isLt]
    · intro a ha
      have hmem : a.val < adaptiveGrid k := (Finset.mem_filter.mp ha).2
      apply Fin.ext
      simp [adaptiveRunLabel, adaptiveGridEmbed, Nat.mod_eq_of_lt hmem]
    · intro a ha
      have hmem : a.val < adaptiveGrid k := a.isLt
      have hlab : adaptiveRunLabel k (adaptiveGridEmbed hk a) = a := by
        apply Fin.ext
        simp [adaptiveRunLabel, adaptiveGridEmbed, Nat.mod_eq_of_lt hmem]
      simp only [hlab]
  rw [h1, h2]

/-- The stage law extended to the common grid has total mass one. -/
theorem adaptiveStageProbAt_sum_one (N k : ℕ) (hk : k < N)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z) = 1 := by
  have h := adaptiveStageProbAt_weighted N k hk A j S hA (fun _ => 1)
  have h' : (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z * 1)
      = ∑ z : Fin (adaptiveGrid k), (adaptiveStageLaw k A j S hA).prob z * 1 := h
  have h'' : (∑ z : Fin (adaptiveGrid N), adaptiveStageProbAt N k hk A j S hA z * 1)
      = 1 := by
    rw [h']
    simp only [mul_one]
    exact (adaptiveStageLaw k A j S hA).sum_one
  simpa using! h''

/-- The finite product distribution of independent stage labels represented in a common
stage-`N` grid. -/
noncomputable def adaptiveJointLaw (N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : FinDist (Fin N → Fin (adaptiveGrid N)) where
  prob ω := ∏ k : Fin N, adaptiveStageProbAt N k.val (k.isLt) A j S hA (ω k)
  nonneg ω :=
    Finset.prod_nonneg fun k _ =>
      adaptiveStageProbAt_nonneg N k.val (k.isLt) A j S hA (ω k)
  sum_one := by
    have hsplit : (∑ ω : Fin N → Fin (adaptiveGrid N),
          ∏ k : Fin N, adaptiveStageProbAt N k.val (k.isLt) A j S hA (ω k))
        = ∏ k : Fin N, (∑ z : Fin (adaptiveGrid N),
            adaptiveStageProbAt N k.val (k.isLt) A j S hA z) := by
      have hswap : (∑ ω : Fin N → Fin (adaptiveGrid N),
            ∏ k : Fin N, adaptiveStageProbAt N k.val (k.isLt) A j S hA (ω k))
          = ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin N => (Finset.univ : Finset (Fin (adaptiveGrid N)))),
            ∏ k : Fin N, adaptiveStageProbAt N k.val (k.isLt) A j S hA (ω k) :=
        Finset.sum_congr rfl (fun ω _ => rfl)
      rw [hswap, ← Finset.prod_univ_sum]
    rw [hsplit]
    have hfinal : (∏ k : Fin N, (∑ z : Fin (adaptiveGrid N),
          adaptiveStageProbAt N k.val (k.isLt) A j S hA z))
        = ∏ k : Fin N, (1 : ℝ) := by
      refine Finset.prod_congr rfl (fun k _ => ?_)
      exact adaptiveStageProbAt_sum_one N k.val (k.isLt) A j S hA
    simpa using! hfinal

/-- The expectation of any function of one stage coordinate under the joint law equals its
expectation under that coordinate's extended stage law. -/
theorem adaptiveJointLaw_marginal (N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : Fin N) (g : Fin (adaptiveGrid N) → ℝ) :
    (∑ ω : Fin N → Fin (adaptiveGrid N),
        (adaptiveJointLaw N A j S hA).prob ω * g (ω k))
      = ∑ z : Fin (adaptiveGrid N),
          adaptiveStageProbAt N k.val (k.isLt) A j S hA z * g z := by
  classical
  have hsplit : (∀ ω : Fin N → Fin (adaptiveGrid N),
      g (ω k) = ∏ m : Fin N, (if m = k then g (ω m) else 1)) := by
    intro ω
    rw [Finset.prod_eq_single k]
    · rw [if_pos rfl]
    · intro m _ hm
      simp [hm]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  have hmain : (∑ ω : Fin N → Fin (adaptiveGrid N),
        (adaptiveJointLaw N A j S hA).prob ω * g (ω k))
      = ∑ ω : Fin N → Fin (adaptiveGrid N),
        ∏ m : Fin N, (adaptiveStageProbAt N m.val (m.isLt) A j S hA (ω m)
          * (if m = k then g (ω m) else 1)) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [show (adaptiveJointLaw N A j S hA).prob ω
        = ∏ m : Fin N, adaptiveStageProbAt N m.val (m.isLt) A j S hA (ω m) from rfl]
    rw [hsplit ω, ← Finset.prod_mul_distrib]
  rw [hmain]
  have hFub : (∑ ω : Fin N → Fin (adaptiveGrid N),
        ∏ m : Fin N, (adaptiveStageProbAt N m.val (m.isLt) A j S hA (ω m)
          * (if m = k then g (ω m) else 1)))
      = ∏ m : Fin N, (∑ z : Fin (adaptiveGrid N),
          adaptiveStageProbAt N m.val (m.isLt) A j S hA z
            * (if m = k then g z else 1)) := by
    have hswap : (∑ ω : Fin N → Fin (adaptiveGrid N),
        ∏ m : Fin N, (adaptiveStageProbAt N m.val (m.isLt) A j S hA (ω m)
          * (if m = k then g (ω m) else 1)))
      = ∑ ω ∈ Fintype.piFinset
          (fun _ : Fin N => (Finset.univ : Finset (Fin (adaptiveGrid N)))),
        ∏ m : Fin N, (adaptiveStageProbAt N m.val (m.isLt) A j S hA (ω m)
          * (if m = k then g (ω m) else 1)) :=
      Finset.sum_congr rfl (fun ω _ => rfl)
    rw [hswap]
    exact (Finset.prod_univ_sum
      (t := fun _ : Fin N => (Finset.univ : Finset (Fin (adaptiveGrid N))))
      (f := fun m ω => adaptiveStageProbAt N m.val (m.isLt) A j S hA ω
        * (if m = k then g ω else 1))).symm
  rw [hFub]
  rw [Finset.prod_eq_single k]
  · simp only [if_true]
  · intro m _ hm
    simp only [if_neg hm]
    have h1 : (∑ z : Fin (adaptiveGrid N),
        adaptiveStageProbAt N m.val (m.isLt) A j S hA z * 1) = 1 := by
      have := adaptiveStageProbAt_sum_one N m.val (m.isLt) A j S hA
      simpa using! this
    exact h1
  · intro hcon
    exact absurd (Finset.mem_univ k) hcon

/-- Weighting a finite sum by a predicate's indicator equals restricting the sum to the
predicate's filter. -/
private theorem sum_indicator_eq_filter {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℝ) (p : X → Prop) :
    (∑ z : X, f z * (if p z then 1 else 0))
      = ∑ z ∈ (Finset.univ : Finset X).filter p, f z := by
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X) p
    (fun z => f z * (if p z then 1 else 0))
  rw [hpart.symm]
  have hA' : (∑ z ∈ (Finset.univ : Finset X).filter p, f z * (if p z then 1 else 0))
      = ∑ z ∈ (Finset.univ : Finset X).filter p, f z := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos (Finset.mem_filter.mp hz).2]
    simp
  have hB' : (∑ z ∈ (Finset.univ : Finset X).filter (fun z => ¬ p z),
      f z * (if p z then 1 else 0)) = 0 := by
    rw [Finset.sum_eq_zero]
    intro z hz
    rw [if_neg (Finset.mem_filter.mp hz).2]
    simp
  rw [hA', hB', add_zero]

/-- Every stage coordinate of the joint law satisfies its AE success window with probability at
least `8/π²` [BrassardEtAl2002]. -/
theorem adaptiveJointLaw_window_mass (N : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : Fin N) :
    (∑ ω : Fin N → Fin (adaptiveGrid N),
        (adaptiveJointLaw N A j S hA).prob ω *
          (if |aeEstimate (adaptiveGrid k.val) (adaptiveRunLabel k.val (ω k))
                - MeasureProb (preparedAAState A j) S|
              ≤ nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S)
            then 1 else 0))
      ≥ 8 / Real.pi ^ 2 := by
  have hk : k.val < N := k.isLt
  have hstep : (∑ ω : Fin N → Fin (adaptiveGrid N),
        (adaptiveJointLaw N A j S hA).prob ω *
          (if |aeEstimate (adaptiveGrid k.val) (adaptiveRunLabel k.val (ω k))
                - MeasureProb (preparedAAState A j) S|
              ≤ nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S)
            then 1 else 0))
      = ∑ z : Fin (adaptiveGrid k.val),
          (adaptiveStageLaw k.val A j S hA).prob z *
            (if |aeEstimate (adaptiveGrid k.val) z
                  - MeasureProb (preparedAAState A j) S|
              ≤ nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S)
            then 1 else 0) := by
    have hmarg := adaptiveJointLaw_marginal N A j S hA k
      (fun z => (if |aeEstimate (adaptiveGrid k.val) (adaptiveRunLabel k.val z)
            - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S)
        then 1 else 0))
    have htrans := adaptiveStageProbAt_weighted N k.val hk A j S hA
      (fun z => (if |aeEstimate (adaptiveGrid k.val) (adaptiveRunLabel k.val z)
            - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (adaptiveGrid k.val) (MeasureProb (preparedAAState A j) S)
        then 1 else 0))
    rw [hmarg, htrans]
    apply Finset.sum_congr rfl
    intro z _
    have hlab : adaptiveRunLabel k.val (adaptiveGridEmbed hk z) = z := by
      apply Fin.ext
      simp [adaptiveRunLabel, adaptiveGridEmbed, Nat.mod_eq_of_lt z.isLt]
    rw [hlab]
  rw [hstep]
  rw [sum_indicator_eq_filter]
  simpa using! adaptiveStageLaw_window_mass k.val A j S hA

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw
