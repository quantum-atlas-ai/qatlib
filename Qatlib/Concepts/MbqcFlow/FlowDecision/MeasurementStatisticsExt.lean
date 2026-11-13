/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.BiasedPauliShadowConsumers

/-!
# POVM moments and counted Pauli measurement campaigns

Proves snapshot reconstruction and the first two moment identities for finite POVM statistics.
The module constructs the six-outcome Pauli POVM, proves its measurement map is bijective, and
records costs for measurement campaigns, table scans, rational accumulation, and median-of-means
processing.

The inverse-measurement construction is related to classical shadow estimation as developed in
[HuangKuengPreskill2020].

## Main statements

* `povmSnapshot_reconstruction`: the mean snapshot equals the measured density operator.
* `povm_variance`: trace formula for the statistic variance.
* `pauliPOVMCampaignLedger_spec`: quantum and classical operation counts.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementStatisticsExt

open Matrix
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {O : Type} [Fintype O] {D : ℕ}

/-- The measurement frame map of a density operator is the Born-probability-weighted sum of POVM
effects. -/
theorem povmMeasurementMap_rho (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    povmMeasurementMap E ρ
      = ∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ) • E.effect o := by
  rw [povmMeasurementMap_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [povmBorn_trace_real E ρ hρ o, povmRecordLaw_prob E ρ hρ o]

/-- Applying the measurement frame map to a reconstruction snapshot recovers its outcome effect. -/
theorem povmMeasurementMap_snapshot (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (o : O) :
    povmMeasurementMap E (povmSnapshot E hM o) = E.effect o :=
  (povmMeasurementEquiv E hM).apply_symm_apply _

/-- For a bijective measurement frame map, the Born-weighted mean of the snapshots equals the
density operator. -/
theorem povmSnapshot_reconstruction (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    ∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ) • povmSnapshot E hM o = ρ := by
  apply hM.1
  simp only [map_sum, map_smul, povmMeasurementMap_snapshot]
  exact (povmMeasurementMap_rho E ρ hρ).symm

/-- The mean reconstruction statistic equals the real trace pairing of the observable with the
density operator. -/
theorem povm_expect_statistic (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) = (Matrix.trace (A * ρ)).re := by
  show ∑ o : O, (povmRecordLaw E ρ hρ).prob o
      * (Matrix.trace (A * povmSnapshot E hM o)).re = _
  rw [show (Matrix.trace (A * ρ)).re = (Matrix.trace (A * (∑ o : O,
        ((povmRecordLaw E ρ hρ).prob o : ℂ) • povmSnapshot E hM o))).re from by
      rw [povmSnapshot_reconstruction E hM ρ hρ],
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The sum of POVM effects weighted by the squares of their real reconstruction statistics. -/
noncomputable def povmMomentEffect (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (A : Operator D) : Operator D :=
  ∑ o : O, ((povmStatistic E hM A o) ^ 2 : ℂ) • E.effect o

/-- The second moment of the reconstruction statistic equals the real trace pairing of its
moment effect with the density operator. -/
theorem povm_expect_statistic_sq (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ 2)
      = (Matrix.trace (povmMomentEffect E hM A * ρ)).re := by
  have hcomplex :
      (∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ) * ((povmStatistic E hM A o) ^ 2 : ℂ))
        = Matrix.trace (povmMomentEffect E hM A * ρ) := by
    rw [povmMomentEffect, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [povmRecordLaw_prob_complex E ρ hρ o]
    ring
  have hreal :
      (∑ o : O, (povmRecordLaw E ρ hρ).prob o * (povmStatistic E hM A o) ^ 2)
        = (∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ) * ((povmStatistic E hM A o) ^ 2 : ℂ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im]
    ring
  show ∑ o : O, (povmRecordLaw E ρ hρ).prob o * (povmStatistic E hM A o) ^ 2 = _
  rw [hreal, hcomplex]

/-- The variance centered at the statistic mean equals its moment-effect trace minus the square
of that mean. -/
theorem povm_variance_centered (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (povmRecordLaw E ρ hρ).expect
        (fun o => (povmStatistic E hM A o
          - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A)) ^ 2)
      = (Matrix.trace (povmMomentEffect E hM A * ρ)).re
        - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) ^ 2 := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinDist.expect_centered_sq,
      povm_expect_statistic_sq]

/-- The variance centered at the real observable trace equals the moment-effect trace minus the
square of the observable trace. -/
theorem povm_variance (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (povmRecordLaw E ρ hρ).expect
        (fun o => (povmStatistic E hM A o - (Matrix.trace (A * ρ)).re) ^ 2)
      = (Matrix.trace (povmMomentEffect E hM A * ρ)).re - (Matrix.trace (A * ρ)).re ^ 2 := by
  have hmean : (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A)
      = (Matrix.trace (A * ρ)).re := povm_expect_statistic E hM ρ hρ A
  calc (povmRecordLaw E ρ hρ).expect
        (fun o => (povmStatistic E hM A o - (Matrix.trace (A * ρ)).re) ^ 2)
      = (povmRecordLaw E ρ hρ).expect
        (fun o => (povmStatistic E hM A o
          - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A)) ^ 2) := by
        rw [hmean]
      _ = (Matrix.trace (povmMomentEffect E hM A * ρ)).re
        - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) ^ 2 :=
        povm_variance_centered E hM ρ hρ A
      _ = (Matrix.trace (povmMomentEffect E hM A * ρ)).re - (Matrix.trace (A * ρ)).re ^ 2 := by
        rw [hmean]

/-- The uniform finite distribution on the three Pauli axes. -/
noncomputable def uniformPauliAxes : FinDist (Fin 3) where
  prob := fun _ => 1 / 3
  nonneg := fun _ => by norm_num
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ]
    norm_num

/-- Every Pauli axis has strictly positive probability under `uniformPauliAxes`. -/
theorem uniformPauliAxes_pos : ∀ a : Fin 3, 0 < uniformPauliAxes.prob a := by
  intro a
  norm_num [uniformPauliAxes]

/-- The six-outcome qubit POVM with effects equal to one third of the Pauli basis projectors. -/
noncomputable def pauliEnsemblePOVM : FinitePOVM (Fin 3 × Fin 2) 2 where
  effect := fun o => (1 / 3 : ℂ) • ensembleProjector pauliBasisMatrix o
  effect_sum := by
    calc (∑ o : Fin 3 × Fin 2, (1 / 3 : ℂ) • ensembleProjector pauliBasisMatrix o)
        = ∑ a : Fin 3, ∑ b : Fin 2, (1 / 3 : ℂ) • ensembleProjector pauliBasisMatrix (a, b) := by
            rw [Fintype.sum_prod_type' (fun a b =>
              (1 / 3 : ℂ) • ensembleProjector pauliBasisMatrix (a, b))]
      _ = ∑ a : Fin 3, (1 / 3 : ℂ) • (∑ b : Fin 2, ensembleProjector pauliBasisMatrix (a, b)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.smul_sum]
      _ = ∑ a : Fin 3, (1 / 3 : ℂ) • (1 : Operator 2) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [ensembleProjector_sum_axis pauliBasisMatrix pauliBasisMatrix_unitary]
      _ = (∑ a : Fin 3, (1 / 3 : ℂ)) • (1 : Operator 2) := Finset.sum_smul.symm
      _ = 1 := by
            have hsum : (∑ a : Fin 3, (1 / 3 : ℂ)) = 1 := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              norm_num
            rw [hsum]
            ext i j
            simp [Matrix.smul_apply, Matrix.one_apply]
  weight := fun _ => 1 / 3
  weight_nonneg := fun _ => by norm_num
  factor := fun o => Projector {o.2} * pauliBasisMatrix o.1
  effect_eq_factor := by
    intro o
    have hPP : ∀ (M : Operator 2),
        Projector {o.2} * (Projector {o.2} * M) = Projector {o.2} * M := by
      intro M
      rw [← Matrix.mul_assoc, projector_mul_self]
    have key : (Projector {o.2} * pauliBasisMatrix o.1)ᴴ
          * (Projector {o.2} * pauliBasisMatrix o.1)
        = ensembleProjector pauliBasisMatrix o := by
      rw [ensembleProjector, Matrix.conjTranspose_mul]
      simp only [projector_conjTranspose]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_assoc]
    rw [key]
    congr 2
    norm_num

/-- Each Pauli ensemble POVM effect is one third of its corresponding basis projector. -/
theorem pauliEnsemblePOVM_effect (o : Fin 3 × Fin 2) :
    pauliEnsemblePOVM.effect o = (1 / 3 : ℂ) • ensembleProjector pauliBasisMatrix o := rfl

/-- The complex embedding of each uniform Pauli axis probability equals one third. -/
theorem uniformPauliAxes_prob (o : Fin 3 × Fin 2) :
    (uniformPauliAxes.prob o.1 : ℂ) = (1 / 3 : ℂ) := by
  norm_num [uniformPauliAxes]

/-- The Pauli POVM frame map equals one third of the corresponding uniformly weighted ensemble
measurement map. -/
theorem povmMeasurementMap_pauliEnsemble (A : Operator 2) :
    povmMeasurementMap pauliEnsemblePOVM A
      = (1 / 3 : ℂ) • ensembleMeasurementMap uniformPauliAxes pauliBasisMatrix A := by
  rw [povmMeasurementMap_apply, ensembleMeasurementMap_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hprob : (uniformPauliAxes.prob o.1 : ℂ) = (1 / 3 : ℂ) := uniformPauliAxes_prob o
  rw [hprob, pauliEnsemblePOVM_effect]
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ext i j
  simp only [Matrix.smul_apply]
  ring

/-- Scaling three copies of a qubit operator by one third recovers the operator. -/
theorem pauliScale : ∀ (X : Operator 2), (1 / 3 : ℂ) • (3 • X) = X := by
  intro X
  ext i j
  simp only [Matrix.smul_apply]
  ring

/-- The frame map of the six-outcome Pauli POVM is bijective. -/
theorem pauliEnsemblePOVM_bijective :
    Function.Bijective (povmMeasurementMap pauliEnsemblePOVM) := by
  have hinv := pauliInverseMap_inverse uniformPauliAxes uniformPauliAxes_pos
  have hleft : ∀ (A : Operator 2),
      pauliInverseMap uniformPauliAxes uniformPauliAxes_pos
          (3 • povmMeasurementMap pauliEnsemblePOVM A) = A := by
    intro A
    rw [povmMeasurementMap_pauliEnsemble]
    have h1 : 3 • ((1 / 3 : ℂ) • ensembleMeasurementMap uniformPauliAxes pauliBasisMatrix A)
        = ensembleMeasurementMap uniformPauliAxes pauliBasisMatrix A := by
      ext i j
      simp only [Matrix.smul_apply]
      ring
    rw [h1]
    exact hinv.left A
  have hright : ∀ (B : Operator 2),
      povmMeasurementMap pauliEnsemblePOVM
        (pauliInverseMap uniformPauliAxes uniformPauliAxes_pos (3 • B)) = B := by
    intro B
    rw [povmMeasurementMap_pauliEnsemble]
    have h1 : ensembleMeasurementMap uniformPauliAxes pauliBasisMatrix
        (pauliInverseMap uniformPauliAxes uniformPauliAxes_pos (3 • B)) = 3 • B :=
      hinv.right (3 • B)
    rw [h1, pauliScale]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hz : pauliInverseMap uniformPauliAxes uniformPauliAxes_pos
        (3 • povmMeasurementMap pauliEnsemblePOVM x)
        = pauliInverseMap uniformPauliAxes uniformPauliAxes_pos
          (3 • povmMeasurementMap pauliEnsemblePOVM y) := by
      rw [hxy]
    rw [hleft x, hleft y] at hz
    exact hz
  · intro B
    exact ⟨pauliInverseMap uniformPauliAxes uniformPauliAxes_pos (3 • B), hright B⟩

/-- The observed Kraus leaf associated with a Pauli axis and its binary measurement outcome. -/
noncomputable def pauliPOVMOutcomeLeaf (o : Fin 3 × Fin 2) : ObservedKrausLeaf 2 :=
  ensembleAxisLeaf (pauliBasisMatrix o.1) o.2

/-- Expands the Pauli outcome leaf into its conjugated projector, success flag, operation
counts, and recorded outcome. -/
theorem pauliPOVMOutcomeLeaf_eq (o : Fin 3 × Fin 2) :
    pauliPOVMOutcomeLeaf o
      = ⟨(pauliBasisMatrix o.1)ᴴ * Projector {o.2} * pauliBasisMatrix o.1, true, 0, 2, 1,
        [(2, o.2.val)]⟩ := by
  rw [pauliPOVMOutcomeLeaf, ensembleAxisLeaf_eq]

/-- The accumulated copy, gate, measurement, and query counts of a Pauli outcome sequence. -/
noncomputable def pauliPOVMCampaignCounts {m : ℕ} (ω : Fin m → (Fin 3 × Fin 2)) :
    ℕ × ℕ × ℕ × ℕ :=
  ensembleFreshResourceCounts pauliBasisMatrix ω

/-- A length-`m` Pauli campaign uses `m` copies, `2 * m` gates, `m` measurements, and zero
queries in the specified ledger. -/
theorem pauliPOVMCampaignCounts_spec {m : ℕ} (ω : Fin m → (Fin 3 × Fin 2)) :
    pauliPOVMCampaignCounts ω = (m, 2 * m, m, 0) :=
  ensembleFreshResourceCounts_spec pauliBasisMatrix ω

/-- Counts comparisons in a sequential table search, stopping at the first matching key. -/
def tableScanCost {X : Type} [DecidableEq X] : List X → X → ℕ
  | [], _ => 0
  | x :: xs, key => if x = key then 1 else 1 + tableScanCost xs key

/-- A sequential table scan uses at most one comparison per list entry. -/
theorem tableScanCost_le {X : Type} [DecidableEq X] (tab : List X) (key : X) :
    tableScanCost tab key ≤ tab.length := by
  induction tab with
  | nil => simp [tableScanCost]
  | cons x xs ih =>
    by_cases h : x = key
    · simp [tableScanCost, h]
    · simp only [tableScanCost, if_neg h]
      calc 1 + tableScanCost xs key ≤ 1 + xs.length := Nat.add_le_add_left ih 1
        _ = (x :: xs).length := by simp [Nat.add_comm]

/-- The ordered table of the three Pauli axes. -/
def pauliPOVMAxisTable : List (Fin 3) := [0, 1, 2]

/-- The comparison count for selecting an outcome's axis by scanning the Pauli axis table. -/
def pauliPOVMSelectionCost (o : Fin 3 × Fin 2) : ℕ :=
  tableScanCost pauliPOVMAxisTable o.1

/-- Selecting a Pauli axis costs its zero-based index plus one comparisons. -/
theorem pauliPOVMSelectionCost_spec (o : Fin 3 × Fin 2) :
    pauliPOVMSelectionCost o = o.1.val + 1 := by
  rcases o with ⟨a, b⟩
  fin_cases a <;> simp [pauliPOVMSelectionCost, pauliPOVMAxisTable, tableScanCost]

/-- The constant rational table weight of one third for every Pauli outcome. -/
def pauliPOVMTableWeight : (Fin 3 × Fin 2) → ℚ := fun _ => 1 / 3

/-- Accumulates rational Pauli table weights together with the number of entries read. -/
def pauliPOVMRationalFold : List (Fin 3 × Fin 2) → ℚ × ℕ
  | [] => (0, 0)
  | o :: os =>
    let s := pauliPOVMRationalFold os
    (pauliPOVMTableWeight o + s.1, s.2 + 1)

/-- The rational fold returns the sum of the table weights and the length of the outcome list. -/
theorem pauliPOVMRationalFold_spec (os : List (Fin 3 × Fin 2)) :
    (pauliPOVMRationalFold os).1 = (os.map pauliPOVMTableWeight).sum ∧
    (pauliPOVMRationalFold os).2 = os.length := by
  induction os with
  | nil => simp [pauliPOVMRationalFold]
  | cons o os ih => simp [pauliPOVMRationalFold, ih]

/-- For `m` Pauli outcomes, the rational fold returns total weight `m / 3` and read count `m`. -/
theorem pauliPOVMRationalFold_campaign {m : ℕ} (ω : Fin m → (Fin 3 × Fin 2)) :
    (pauliPOVMRationalFold (List.ofFn ω)).1 = (m : ℚ) / 3 ∧
    (pauliPOVMRationalFold (List.ofFn ω)).2 = m := by
  have h := pauliPOVMRationalFold_spec (List.ofFn ω)
  constructor
  · rw [h.1, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, pauliPOVMTableWeight]
    have h1 : (∑ i : Fin m, (1 / 3 : ℚ)) = (m : ℚ) * (1 / 3 : ℚ) := by
      simp
    rw [h1]
    ring
  · rw [h.2, List.length_ofFn]

/-- Computes a median-of-means statistic together with statistic-read and sorting-comparison
counts. -/
noncomputable def pauliPOVMMedianOfMeansCounted (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (A : Operator D) {L K : ℕ}
    (ω : Fin K → Fin L → O) : ℝ × ℕ × ℕ :=
  ensembleMedianOfMeansCounted (povmStatistic E hM A) ω

/-- The counted procedure returns the median-of-means value, reads `K * L` statistics, and uses
at most `K * K` comparisons. -/
theorem pauliPOVMMedianOfMeansCounted_spec (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (q : FinDist O) (A : Operator D)
    {L K : ℕ} (ω : Fin K → Fin L → O) [DecidableEq O] :
    (pauliPOVMMedianOfMeansCounted E hM A ω).1
        = q.medianOfMeans (povmStatistic E hM A) ω ∧
    (pauliPOVMMedianOfMeansCounted E hM A ω).2.1 = K * L ∧
    (pauliPOVMMedianOfMeansCounted E hM A ω).2.2 ≤ K * K :=
  ensembleMedianOfMeansCounted_spec q (povmStatistic E hM A) ω

/-- The value returned by the counted procedure equals the median-of-means statistic under the
POVM record law. -/
theorem pauliPOVMMedianOfMeansCounted_recordLaw (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) {L K : ℕ} (ω : Fin K → Fin L → O)
    [DecidableEq O] :
    (pauliPOVMMedianOfMeansCounted E hM A ω).1
        = (povmRecordLaw E ρ hρ).medianOfMeans (povmStatistic E hM A) ω :=
  (pauliPOVMMedianOfMeansCounted_spec E hM (povmRecordLaw E ρ hρ) A ω).1

/-- The uniform distribution on the six Pauli axis-outcome pairs. -/
noncomputable def uniformPauliPOVMOutcomes : FinDist (Fin 3 × Fin 2) where
  prob := fun _ => 1 / 6
  nonneg := fun _ => by norm_num
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ]
    norm_num

/-- A ledger of copy, gate, measurement, query, selection-comparison, table-read,
statistic-read, and median-comparison counts. -/
structure MeasurementCampaignLedger where

  copies : ℕ

  gates : ℕ

  measurements : ℕ

  queries : ℕ

  selectionComparisons : ℕ

  tableReads : ℕ

  statisticReads : ℕ

  medianComparisons : ℕ

/-- Combines Pauli measurement counts with axis-selection, table-accumulation, and
median-of-means processing counts. -/
noncomputable def pauliPOVMCampaignLedger {m L K : ℕ}
    (A : Operator 2) (hM : Function.Bijective (povmMeasurementMap pauliEnsemblePOVM))
    (ω : Fin m → (Fin 3 × Fin 2)) (samples : Fin K → Fin L → (Fin 3 × Fin 2))
    : MeasurementCampaignLedger where
  copies := (pauliPOVMCampaignCounts ω).1
  gates := (pauliPOVMCampaignCounts ω).2.1
  measurements := (pauliPOVMCampaignCounts ω).2.2.1
  queries := (pauliPOVMCampaignCounts ω).2.2.2
  selectionComparisons := ∑ i : Fin m, pauliPOVMSelectionCost (ω i)
  tableReads := (pauliPOVMRationalFold (List.ofFn ω)).2
  statisticReads := (pauliPOVMMedianOfMeansCounted pauliEnsemblePOVM hM A samples).2.1
  medianComparisons := (pauliPOVMMedianOfMeansCounted pauliEnsemblePOVM hM A samples).2.2

/-- Gives the exact measurement, query, table-read, and statistic-read counts and the quadratic
median-comparison bound for a Pauli campaign. -/
theorem pauliPOVMCampaignLedger_spec {m L K : ℕ}
    (A : Operator 2) (hM : Function.Bijective (povmMeasurementMap pauliEnsemblePOVM))
    (ω : Fin m → (Fin 3 × Fin 2)) (samples : Fin K → Fin L → (Fin 3 × Fin 2)) :
    (pauliPOVMCampaignLedger A hM ω samples).copies = m ∧
    (pauliPOVMCampaignLedger A hM ω samples).gates = 2 * m ∧
    (pauliPOVMCampaignLedger A hM ω samples).measurements = m ∧
    (pauliPOVMCampaignLedger A hM ω samples).queries = 0 ∧
    (pauliPOVMCampaignLedger A hM ω samples).tableReads = m ∧
    (pauliPOVMCampaignLedger A hM ω samples).statisticReads = K * L ∧
    (pauliPOVMCampaignLedger A hM ω samples).medianComparisons ≤ K * K := by
  have hcount := pauliPOVMCampaignCounts_spec ω
  have hfold := pauliPOVMRationalFold_campaign ω
  have hmed := pauliPOVMMedianOfMeansCounted_spec pauliEnsemblePOVM hM
    uniformPauliPOVMOutcomes A samples
  simp only [pauliPOVMCampaignLedger]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcount]
  · rw [hcount]
  · rw [hcount]
  · rw [hcount]
  · rw [hfold.2]
  · rw [hmed.2.1]
  · exact hmed.2.2

/-- Collects nonnegative outcome probabilities, snapshot reconstruction, unbiasedness, and the
second-moment and variance formulas for a finite POVM with bijective frame map. -/
theorem g6 (O : Type) [Fintype O] (D : ℕ) (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (∀ o : O, 0 ≤ (povmRecordLaw E ρ hρ).prob o) ∧
    (∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ) • povmSnapshot E hM o = ρ) ∧
    ((povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) = (Matrix.trace (A * ρ)).re) ∧
    ((povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ 2)
      = (Matrix.trace (povmMomentEffect E hM A * ρ)).re) ∧
    ((povmRecordLaw E ρ hρ).expect
        (fun o => (povmStatistic E hM A o - (Matrix.trace (A * ρ)).re) ^ 2)
      = (Matrix.trace (povmMomentEffect E hM A * ρ)).re - (Matrix.trace (A * ρ)).re ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o
    exact povmBorn_nonneg E ρ hρ o
  · exact povmSnapshot_reconstruction E hM ρ hρ
  · exact povm_expect_statistic E hM ρ hρ A
  · exact povm_expect_statistic_sq E hM ρ hρ A
  · exact povm_variance E hM ρ hρ A

/-- Collects Pauli campaign operation counts, the rational weight total, and the read and
comparison bounds for median-of-means processing. -/
theorem thresholdGoal (m L K : ℕ) (A : Operator 2)
    (hM : Function.Bijective (povmMeasurementMap pauliEnsemblePOVM))
    (ω : Fin m → (Fin 3 × Fin 2)) (samples : Fin K → Fin L → (Fin 3 × Fin 2)) :
    pauliPOVMCampaignCounts ω = (m, 2 * m, m, 0) ∧
    (pauliPOVMRationalFold (List.ofFn ω)).1 = (m : ℚ) / 3 ∧
    (pauliPOVMRationalFold (List.ofFn ω)).2 = m ∧
    (pauliPOVMCampaignLedger A hM ω samples).statisticReads = K * L ∧
    (pauliPOVMCampaignLedger A hM ω samples).medianComparisons ≤ K * K := by
  have hcount := pauliPOVMCampaignCounts_spec ω
  have hfold := pauliPOVMRationalFold_campaign ω
  have hmed := pauliPOVMMedianOfMeansCounted_spec pauliEnsemblePOVM hM
    uniformPauliPOVMOutcomes A samples
  have hledger := pauliPOVMCampaignLedger_spec A hM ω samples
  refine ⟨hcount, hfold.1, hfold.2, hledger.2.2.2.2.2.1, hledger.2.2.2.2.2.2⟩

end MeasurementStatisticsExt
end Qatlib.Concepts.MbqcFlow.FlowDecision
