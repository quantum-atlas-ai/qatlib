/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchDefs
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadoutConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.LayeredMean.NativeComposedMean
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase

/-!
# Search backend correctness and finite gate implementations

This module proves correctness and comparison bounds for the rational median stages defined in
`SearchDefs`, and collects amplitude-estimation and mean-estimation guarantees in `clause24`.
These statistical guarantees use the amplitude-estimation framework of [BrassardEtAl2002].

It also compiles reversible Boolean blocks into finite gate words, verifies table loading and
resource ledgers, and records the numerical precision guarantees available for the local
backend. `not_clause3` rules out the full conjunction that includes finite implementation of
every unitary under the stated operator error requirement.

## Main statements

* `stageOutput_eq_nativeRationalMedian`: counted sorting computes the specified median.
* `clause24`: combined estimation, median amplification, stage accounting, and stopping
  properties.
* `run_blocksWord_ket` and `hasTableLoad`: finite gate correctness for Boolean blocks and table
  loading.
* `tunableGoal_success_event`: counted amplitude-estimation circuit semantics and probability
  guarantees.
* `not_clause3`: failure of the conjunction containing universal finite implementation.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped BigOperators Classical

/-- Inserting a rational value with `insertSortedRat` increases the output list length by one. -/
theorem insertSortedRat_length (x : ℚ) (l : List ℚ) :
    (insertSortedRat x l).1.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertSortedRat]
    split
    · rfl
    · show (insertSortedRat x ys).1.length + 1 = (y :: ys).length + 1
      rw [ih]
      simp

/-- The comparison count of `insertSortedRat` is at most the length of the input list. -/
theorem insertSortedRat_cost_le (x : ℚ) (l : List ℚ) :
    (insertSortedRat x l).2 ≤ l.length := by
  induction l with
  | nil => simp [insertSortedRat]
  | cons y ys ih =>
    simp only [insertSortedRat]
    split
    · simp
    · show (insertSortedRat x ys).2 + 1 ≤ (y :: ys).length
      have hlen : (y :: ys).length = ys.length + 1 := rfl
      omega

/-- The output of `insertSortedRat` is a permutation of the inserted value followed by the input
list. -/
theorem insertSortedRat_perm (x : ℚ) (l : List ℚ) :
    (insertSortedRat x l).1.Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertSortedRat]
    split
    · exact List.Perm.refl _
    · exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

/-- Inserting a rational value with `insertSortedRat` preserves nondecreasing order. -/
theorem insertSortedRat_sorted {x : ℚ} {l : List ℚ} (hl : l.SortedLE) :
    (insertSortedRat x l).1.SortedLE := by
  induction l with
  | nil =>
    exact List.sortedLE_iff_pairwise.mpr
      (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil (a := b))) List.Pairwise.nil)
  | cons y ys ih =>
    simp only [insertSortedRat]
    rw [List.sortedLE_iff_pairwise] at hl ⊢
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
    split
    · next hxy =>
      refine List.Pairwise.cons (fun b hb => ?_) hl
      rcases List.mem_cons.mp hb with rfl | hbys
      · exact hxy
      · exact le_trans hxy (hhead b hbys)
    · next hnxy =>
      have hyx : y ≤ x := le_of_lt (lt_of_not_ge hnxy)
      refine List.Pairwise.cons (fun b hb => ?_)
        (List.sortedLE_iff_pairwise.mp (ih (List.sortedLE_iff_pairwise.mpr htail)))
      have hmem : b ∈ x :: ys := List.Perm.subset (insertSortedRat_perm x ys) hb
      rcases List.mem_cons.mp hmem with rfl | hbys
      · exact hyx
      · exact hhead b hbys

/-- Counted rational sorting preserves the length of its input list. -/
theorem sortCountedRat_length (l : List ℚ) : (sortCountedRat l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show ((insertSortedRat x (sortCountedRat xs).1).1).length = (x :: xs).length
    rw [insertSortedRat_length, ih]
    simp

/-- The list produced by `sortCountedRat` is a permutation of the input list. -/
theorem sortCountedRat_perm (l : List ℚ) : (sortCountedRat l).1.Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    show ((insertSortedRat x (sortCountedRat xs).1).1).Perm (x :: xs)
    exact List.Perm.trans (insertSortedRat_perm x _) (List.Perm.cons x ih)

/-- Counted rational sorting uses at most the square of the input length in comparisons. -/
theorem sortCountedRat_cost_le (l : List ℚ) :
    (sortCountedRat l).2 ≤ l.length * l.length := by
  induction l with
  | nil => simp [sortCountedRat]
  | cons x xs ih =>
    show (sortCountedRat xs).2 + (insertSortedRat x (sortCountedRat xs).1).2
      ≤ (x :: xs).length * (x :: xs).length
    have h1 := insertSortedRat_cost_le x (sortCountedRat xs).1
    have h2 := sortCountedRat_length xs
    have h3 : (x :: xs).length = xs.length + 1 := rfl
    have h4 : xs.length * xs.length + xs.length
        ≤ (x :: xs).length * (x :: xs).length := by
      rw [h3, Nat.succ_mul_succ]
      omega
    omega

/-- The list produced by `sortCountedRat` is in nondecreasing order. -/
theorem sortCountedRat_sorted (l : List ℚ) : (sortCountedRat l).1.SortedLE := by
  induction l with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons x xs ih =>
    show ((insertSortedRat x (sortCountedRat xs).1).1).SortedLE
    exact insertSortedRat_sorted ih

/-- The list produced by counted rational sorting equals the result of merge sorting with the
nondecreasing comparison. -/
theorem sortCountedRat_eq_mergeSort (l : List ℚ) :
    (sortCountedRat l).1 = l.mergeSort (fun a b => a ≤ b) :=
  ((sortCountedRat_perm l).trans (List.mergeSort_perm l (fun a b => a ≤ b)).symm).eq_of_sortedLE
    (sortCountedRat_sorted l) (List.sortedLE_mergeSort (l := l))

/-- The counted stage output equals `nativeRationalMedian` of its rational labels. -/
theorem stageOutput_eq_nativeRationalMedian (p : StageParams) (ys : StageLabels p) :
    stageOutput p ys = nativeRationalMedian p.mid ys := by
  show (sortCountedRat (List.ofFn ys)).1.getD p.mid 0 =
    ((List.ofFn ys).mergeSort (fun a b => a ≤ b)).getD p.mid 0
  rw [sortCountedRat_eq_mergeSort]

/-- A stage with 2m + 1 labels uses at most (2m + 1)² comparisons to compute its median. -/
theorem stageComparisons_le (p : StageParams) (ys : StageLabels p) :
    stageComparisons p ys ≤ (2 * p.mid + 1) * (2 * p.mid + 1) := by
  show (sortCountedRat (List.ofFn ys)).2 ≤ (2 * p.mid + 1) * (2 * p.mid + 1)
  have hlen : (List.ofFn ys).length = 2 * p.mid + 1 := List.length_ofFn
  have h := sortCountedRat_cost_le (List.ofFn ys)
  rw [hlen] at h
  exact h

/-- The window stopping test is true exactly when the history contains a stage whose window is
at most the target. -/
theorem windowStops_iff (target : ℚ) (h : List (StageParams × ℚ)) :
    windowStops target h = true ↔ ∃ p y, (p, y) ∈ h ∧ p.win ≤ target := by
  induction h with
  | nil =>
    constructor
    · intro hh
      simp [windowStops] at hh
    · intro hh
      obtain ⟨p, y, hm, _⟩ := hh
      simp at hm
  | cons hd tl ih =>
    rcases hd with ⟨p, y⟩
    have hcons : windowStops target ((p, y) :: tl)
        = (decide (p.win ≤ target) || windowStops target tl) := rfl
    constructor
    · intro hh
      rw [hcons] at hh
      have hor : (decide (p.win ≤ target) = true) ∨ (windowStops target tl = true) := by
        rw [← Bool.or_eq_true_eq_eq_true_or_eq_true]
        exact hh
      rcases hor with h | h
      · refine ⟨p, y, List.mem_cons.mpr (Or.inl rfl), ?_⟩
        simpa using! h
      · obtain ⟨p', y', hm, hw⟩ := ih.mp h
        exact ⟨p', y', List.mem_cons.mpr (Or.inr hm), hw⟩
    · intro hh
      obtain ⟨p', y', hm, hw⟩ := hh
      rw [hcons]
      rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      rcases List.mem_cons.mp hm with he | hm
      · rcases Prod.eq_iff_fst_eq_snd_eq.mp he with ⟨rfl, rfl⟩
        exact Or.inl (by simpa using! hw)
      · exact Or.inr (ih.mpr ⟨p', y', hm, hw⟩)

/-- Collects finite-precision amplitude and counting guarantees, bounded and relative mean
estimates, median amplification, stage costs, layer composition, and history-based stopping
identities. The amplitude-estimation guarantees include the success bound 8/π² from
[BrassardEtAl2002]. -/
theorem clause24 :

  (∀ (I : Type) [Fintype I] [DecidableEq I] (M k : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |(nativeAEDecode M k z : ℝ) - a| ≤
        2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
          Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (M k N : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |((N : ℚ) * nativeAEDecode M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) *
        (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
          Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k)),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 ∧
      (∀ z : Fin M, (a = 0 ∧ z.val = 0) → nativeAEDecode M k z = 0)) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1),
    let μ := ∑ i, BornProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j)) i * f i
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |aeEstimate M z - μ| ≤
        2 * Real.pi * Real.sqrt (μ * (1 - μ)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2),
      (meanLaw M A j f hA hf hM).prob z) ≥ 8 / Real.pi ^ 2) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (M r : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1),
    let μ := ∑ i, BornProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j)) i * f i
    (meanLaw M A j f hA hf hM).probEvent (fun ω =>
      2 * Real.pi * Real.sqrt (μ * (1 - μ)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 <
        |meanMedian r M ω - μ|) ≤
      (2 : ℝ) ^ (2 * r + 1) * (1 - 8 / Real.pi ^ 2) ^ (r + 1)) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (B k : ℕ) (A : Matrix I I ℂ)
      (j : I) (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i)
      (_hB : 1 ≤ B) (_hk : 4 ≤ k),
    let μ := ∑ i, BornProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j)) i * f i
    0 < μ → (∑ i, BornProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i - μ) ^ 2) ≤ (B : ℝ) * μ ^ 2 →
      (∑ ω with |relativeMeanEstimate B k f ω - μ| ≤
          3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ,
        (relativeMeanLaw B k A j f hA hf).prob ω) ≥ 2 / 3) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (p : StageParams) (_hp : 0 < p.grid)
      (A : Matrix I I ℂ) (j : I),
    (stageLaunches p A j).length = 2 * p.mid + 1 ∧
      ((stageLaunches p A j).map QueryCount).sum = stageMarkQueries p ∧
      ((stageLaunches p A j).map GateCount).sum =
        (2 * p.mid + 1) * (5 * (p.grid - 1) + 3) ∧
      stagePreparationCalls p = (2 * p.mid + 1) * (2 * (p.grid - 1) + 1) ∧
      stageDecodeTerms p = (2 * p.mid + 1) * (8 * (p.prec + 8)) ∧
      (∀ x : ℚ, (nativeAESinCounted x p.prec).2 = 8 * (p.prec + 8))) ∧

  (∀ (p : StageParams) (ys : StageLabels p),
    stageOutput p ys = nativeRationalMedian p.mid ys ∧
      stageComparisons p ys ≤ (2 * p.mid + 1) * (2 * p.mid + 1) ∧
      stageOutput p ys = (sortCountedRat (List.ofFn ys)).1.getD p.mid 0 ∧
      stageComparisons p ys = (sortCountedRat (List.ofFn ys)).2) ∧

  (∀ (k : ℕ) (ω : LayerRecord k),
    composedOutput (nativeStageWeights k) (fun _ : Fin (k + 2) => nativeStageParams k)
        (nativeStageLabels k ω) = nativeLayerOutput k ω ∧
      composedComparisons (fun _ : Fin (k + 2) => nativeStageParams k) (nativeStageLabels k ω)
        = ∑ l : Fin (k + 2), stageComparisons (nativeStageParams k) (nativeStageLabels k ω l)) ∧

  (∀ (target : ℚ) (budget fuel : ℕ) (next : ℕ → StageParams)
      (source : (p : StageParams) → StageLabels p),
    let hist := runStages (windowChooser target budget next) source fuel []
    hist.length ≤ fuel ∧
      (hist = [] ∨ windowStops target hist = true ∨ budget ≤ hist.length ∨
        hist.length = fuel) ∧
      (∀ h : List (StageParams × ℚ), windowStops target h = true ↔
        ∃ p y, (p, y) ∈ h ∧ p.win ≤ target) ∧
      runOutput [] = 0 ∧
      (∀ (h : List (StageParams × ℚ)) (p : StageParams) (y : ℚ),
        runOutput (h ++ [(p, y)]) = y) ∧
      runLedger source [] = StageLedger.zero ∧
      (∀ (h : List (StageParams × ℚ)) (p : StageParams),
        runLedger source (h ++ [(p, stageOutput p (source p))]) =
          (runLedger source h).add (stageLedger p (source p))) ∧
      windowChooser target budget next =
        (fun h => if windowStops target h = true ∨ budget ≤ h.length then none
          else some (next h.length))) :=
by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact native_ae_same_record_bhmt_success
  · exact native_ae_counting_relative_output_consumer
  · intro I _ _ M hM A j f hA hf
    exact quantum_mean_actual_ae_accuracy M hM A j f hA hf
  · intro I _ _ M r hM A j f hA hf
    exact quantum_mean_sorted_median_amplification M r hM A j f hA hf
  · intro I _ _ B k A j f hA hf _hB _hk
    exact relative_variance_actual_conditional_estimator I B k A j f hA hf _hB _hk
  · intro I _ _ p hp A j
    have hq := (prepared_ae_access_ledger p.grid hp A j).1
    have hg := (prepared_ae_access_ledger p.grid hp A j).2.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [stageLaunches]
    · show ((stageLaunches p A j).map QueryCount).sum = stageMarkQueries p
      simp only [stageLaunches, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      rw [hq]
      rfl
    · show ((stageLaunches p A j).map GateCount).sum = (2 * p.mid + 1) * (5 * (p.grid - 1) + 3)
      simp only [stageLaunches, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      rw [hg]
      rfl
    · show stagePreparationCalls p = (2 * p.mid + 1) * (2 * (p.grid - 1) + 1)
      have h : 2 * p.grid - 1 = 2 * (p.grid - 1) + 1 := by omega
      simp only [stagePreparationCalls, h]
    · show stageDecodeTerms p = (2 * p.mid + 1) * (8 * (p.prec + 8))
      rfl
    · intro x
      exact congrArg Prod.snd (nativeAESin_value_and_terms x p.prec)
  · intro p ys
    refine ⟨stageOutput_eq_nativeRationalMedian p ys, stageComparisons_le p ys, ?_, ?_⟩
    · rfl
    · rfl
  · intro k ω
    refine ⟨?_, rfl⟩
    show composedOutput (nativeStageWeights k) (fun _ : Fin (k + 2) => nativeStageParams k)
        (nativeStageLabels k ω) = nativeLayerOutput k ω
    simp only [composedOutput, nativeStageWeights, nativeLayerOutput]
    apply Finset.sum_congr rfl
    intro l _
    show (2 : ℚ) ^ l.val * stageOutput (nativeStageParams k) (nativeStageLabels k ω l) = _
    rw [stageOutput_eq_nativeRationalMedian (nativeStageParams k) (nativeStageLabels k ω l)]
    rfl
  · intro target budget fuel next source
    have hstop := windowStops_iff target
    have hkey : ∀ (n : ℕ) (hist : List (StageParams × ℚ)),
        (runStages (windowChooser target budget next) source n hist).length ≤ hist.length + n ∧
          (windowStops target (runStages (windowChooser target budget next) source n hist) = true ∨
            budget ≤ (runStages (windowChooser target budget next) source n hist).length ∨
            (runStages (windowChooser target budget next) source n hist).length = hist.length + n) := by
      intro n
      induction n with
      | zero =>
        intro hist
        refine ⟨?_, ?_⟩
        · show hist.length ≤ hist.length + 0
          omega
        · exact Or.inr (Or.inr rfl)
      | succ n ih =>
        intro hist
        cases hch : windowChooser target budget next hist with
        | none =>
          have hc : windowStops target hist = true ∨ budget ≤ hist.length := by
            by_contra hnc
            simp only [windowChooser, if_neg hnc] at hch
            exact absurd hch (by simp)
          have heq : runStages (windowChooser target budget next) source (n + 1) hist = hist := by
            simp only [runStages, hch]
          refine ⟨?_, ?_⟩
          · rw [heq]
            omega
          · rw [heq]
            rcases hc with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
        | some q =>
          have heq : runStages (windowChooser target budget next) source (n + 1) hist =
              runStages (windowChooser target budget next) source n
                (hist ++ [(q, stageOutput q (source q))]) := by
            simp only [runStages, hch]
          rw [heq]
          have hlen1 : (hist ++ [(q, stageOutput q (source q))]).length = hist.length + 1 := by
            simp
          have ih' := ih (hist ++ [(q, stageOutput q (source q))])
          refine ⟨by omega, ?_⟩
          rcases ih' with ⟨_, h | h | h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (by omega))
    intro hist
    have hlen := (hkey fuel []).1
    have hstop' := (hkey fuel []).2
    have hhist : hist = runStages (windowChooser target budget next) source fuel [] := rfl
    refine ⟨?_, ?_, hstop, rfl, ?_, rfl, ?_, ?_⟩
    · rw [hhist]
      simpa using! hlen
    · rw [hhist]
      have hstop'' : windowStops target (runStages (windowChooser target budget next) source fuel []) = true ∨
          budget ≤ (runStages (windowChooser target budget next) source fuel []).length ∨
          (runStages (windowChooser target budget next) source fuel []).length = fuel := by
        simpa using! hstop'
      rcases hstop'' with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · intro h p y
      show (h ++ [(p, y)]).foldl (fun _ s => s.2) (0 : ℚ) = y
      rw [List.foldl_append]
      rfl
    · intro h p
      show (h ++ [(p, stageOutput p (source p))]).foldl
          (fun d s => d.add (stageLedger s.1 (source s.1))) StageLedger.zero =
        (runLedger source h).add (stageLedger p (source p))
      rw [List.foldl_append]
      rfl
    · rfl

/-- The fifteen-gate H, T, inverse T, and CNOT word for a Toffoli gate on two control wires and
a target wire. -/
def toffoliWord {n : ℕ} (a b t : Fin n) : List FiniteGateCode :=
  [.h t.val, .cx b.val t.val, .tdg t.val, .cx a.val t.val, .t t.val, .cx b.val t.val,
    .tdg t.val, .cx a.val t.val, .t b.val, .t t.val, .h t.val, .cx a.val b.val,
    .t a.val, .tdg b.val, .cx a.val b.val]

/-- Decoding a Hadamard gate code on an in-range wire gives the corresponding wire Hadamard
matrix. -/
theorem finiteCodeMatrix_h (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (FiniteGateCode.h w.val) = wireGate n w Hadamard := by
  show (if h : w.val < n then wireGate n ⟨w.val, h⟩ Hadamard else 1) = wireGate n w Hadamard
  rw [dif_pos w.isLt]

/-- Decoding an X gate code on an in-range wire gives the corresponding wire Pauli X matrix. -/
theorem finiteCodeMatrix_x (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (FiniteGateCode.x w.val) = wireGate n w PauliX := by
  show (if h : w.val < n then wireGate n ⟨w.val, h⟩ PauliX else 1) = wireGate n w PauliX
  rw [dif_pos w.isLt]

/-- Decoding a T gate code on an in-range wire gives the corresponding wire T matrix. -/
theorem finiteCodeMatrix_t (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (FiniteGateCode.t w.val) = wireGate n w tGate := by
  show (if h : w.val < n then wireGate n ⟨w.val, h⟩ tGate else 1) = wireGate n w tGate
  rw [dif_pos w.isLt]

/-- Decoding an inverse T gate code on an in-range wire gives the corresponding wire adjoint T
matrix. -/
theorem finiteCodeMatrix_tdg (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (FiniteGateCode.tdg w.val) = wireGate n w tGateAdj := by
  show (if h : w.val < n then wireGate n ⟨w.val, h⟩ tGateAdj else 1) = wireGate n w tGateAdj
  rw [dif_pos w.isLt]

/-- Decoding a controlled X code on distinct in-range wires gives the corresponding CNOT matrix. -/
theorem finiteCodeMatrix_cx (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    finiteCodeMatrix n (FiniteGateCode.cx c.val t.val) = cnotGate n c t := by
  have hct' : ¬(c.val = t.val) := fun h => hct (Fin.ext h)
  show (if h : c.val < n ∧ t.val < n ∧ ¬(c.val = t.val) then
      cnotGate n ⟨c.val, h.1⟩ ⟨t.val, h.2.1⟩ else 1) = cnotGate n c t
  rw [dif_pos ⟨c.isLt, t.isLt, hct'⟩]

/-- A Hadamard gate code on an in-range wire passes the legality test. -/
theorem finiteCodeLegal_h (n : ℕ) (w : Fin n) : finiteCodeLegal n (FiniteGateCode.h w.val) = true := by
  show decide (w.val < n) = true
  simp [w.isLt]

/-- An X gate code on an in-range wire passes the legality test. -/
theorem finiteCodeLegal_x (n : ℕ) (w : Fin n) : finiteCodeLegal n (FiniteGateCode.x w.val) = true := by
  show decide (w.val < n) = true
  simp [w.isLt]

/-- A T gate code on an in-range wire passes the legality test. -/
theorem finiteCodeLegal_t (n : ℕ) (w : Fin n) : finiteCodeLegal n (FiniteGateCode.t w.val) = true := by
  show decide (w.val < n) = true
  simp [w.isLt]

/-- An inverse T gate code on an in-range wire passes the legality test. -/
theorem finiteCodeLegal_tdg (n : ℕ) (w : Fin n) :
    finiteCodeLegal n (FiniteGateCode.tdg w.val) = true := by
  show decide (w.val < n) = true
  simp [w.isLt]

/-- A controlled X code with distinct in-range control and target wires passes the legality
test. -/
theorem finiteCodeLegal_cx (n : ℕ) (c t : Fin n) (h : c ≠ t) :
    finiteCodeLegal n (FiniteGateCode.cx c.val t.val) = true := by
  show decide (c.val < n ∧ t.val < n ∧ c.val ≠ t.val) = true
  simp only [decide_eq_true_eq]
  exact ⟨c.isLt, t.isLt, fun he => h (Fin.ext he)⟩

/-- Applying a wire Pauli X gate to a computational basis state flips exactly that wire's bit. -/
theorem wireGate_X_ket' (n : ℕ) (w : Fin n) (x : Reg n) :
    ApplyGate (wireGate n w PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!(x w))) := by
  rw [applyGate_wireGate_ket]
  cases hx : x w <;> simp [PauliX, permMatrix]

/-- On pairwise distinct wires, decoding the compiled Toffoli word gives the same gate-step list
as the local Toffoli construction. -/
theorem toffoliWord_map (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    (toffoliWord a b t).map (fun g => Step.gate (finiteCodeMatrix n g)) =
      (toffoliLocalSteps a b t).map (fun g => Step.gate (reflectionGateMatrix g)) := by
  simp only [toffoliWord, toffoliLocalSteps, List.map_cons, List.map_nil, reflectionGateMatrix,
    finiteCodeMatrix_h n t, finiteCodeMatrix_cx n b t hbt, finiteCodeMatrix_tdg n t,
    finiteCodeMatrix_cx n a t hat, finiteCodeMatrix_t n t, finiteCodeMatrix_t n b,
    finiteCodeMatrix_cx n a b hab, finiteCodeMatrix_t n a, finiteCodeMatrix_tdg n b]

/-- On pairwise distinct wires, the compiled Toffoli word maps a basis register to the register
with its target flipped exactly when both control bits are true. -/
theorem toffoliWord_run_ket (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (toffoliWord a b t)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
  have heq : finiteCodeCircuit n (toffoliWord a b t) =
      reflectionCompile (toffoliLocalSteps a b t) := by
    simp only [finiteCodeCircuit, reflectionCompile]
    exact toffoliWord_map n a b t hab hat hbt
  rw [heq]
  exact (local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x

/-- The compiled Toffoli word is legal when its two control wires and target wire are pairwise
distinct. -/
theorem toffoliWord_legal (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    finiteWordLegal n (toffoliWord a b t) = true := by
  simp only [toffoliWord, finiteWordLegal, List.all_cons, List.all_nil,
    finiteCodeLegal_h n t, finiteCodeLegal_cx n b t hbt, finiteCodeLegal_tdg n t,
    finiteCodeLegal_cx n a t hat, finiteCodeLegal_t n t, finiteCodeLegal_t n b,
    finiteCodeLegal_cx n a b hab, finiteCodeLegal_t n a, finiteCodeLegal_tdg n b]
  rfl

/-- Reversible Boolean gate blocks consisting of X, controlled X, and Toffoli gates on a fixed
register width. -/
inductive GBlk (n : ℕ) where
  | x (w : Fin n)
  | cx (c t : Fin n)
  | tof (a b t : Fin n)

/-- Compiles a reversible Boolean gate block to its finite gate-code word. -/
def GBlk.word {n : ℕ} : GBlk n → List FiniteGateCode
  | .x w => [FiniteGateCode.x w.val]
  | .cx c t => [FiniteGateCode.cx c.val t.val]
  | .tof a b t => toffoliWord a b t

/-- The Boolean register update specified by an X, controlled X, or Toffoli block. -/
def GBlk.upd {n : ℕ} : GBlk n → Reg n → Reg n
  | .x w => fun r => Function.update r w (!r w)
  | .cx c t => fun r => Function.update r t (r t ^^ r c)
  | .tof a b t => fun r => Function.update r t (r t ^^ (r a && r b))

/-- The wire-distinctness condition for a Boolean gate block: none for X, distinct control and
target for controlled X, and pairwise distinct wires for Toffoli. -/
def GBlk.ok {n : ℕ} : GBlk n → Prop
  | .x _ => True
  | .cx c t => c ≠ t
  | .tof a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t

/-- Executing the compiled word of a block satisfying `GBlk.ok` realizes its specified Boolean
update on every computational basis state. -/
theorem GBlk.word_run_ket {n : ℕ} (g : GBlk n) (hg : g.ok) (r : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n g.word) (Qatlib.Foundations.PureStateMath.Ket r) = Qatlib.Foundations.PureStateMath.Ket (g.upd r) := by
  cases g with
  | x w =>
    show Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (finiteCodeCircuit n [FiniteGateCode.x w.val]) (Qatlib.Foundations.PureStateMath.Ket r) = Qatlib.Foundations.PureStateMath.Ket (Function.update r w (!r w))
    simp only [finiteCodeCircuit, List.map_cons, List.map_nil, run_gate, run_nil]
    rw [finiteCodeMatrix_x n w]
    exact wireGate_X_ket' n w r
  | cx c t =>
    show Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (finiteCodeCircuit n [FiniteGateCode.cx c.val t.val]) (Qatlib.Foundations.PureStateMath.Ket r) = _
    simp only [finiteCodeCircuit, List.map_cons, List.map_nil, run_gate, run_nil]
    rw [finiteCodeMatrix_cx n c t hg]
    exact applyGate_cnotGate_ket n c t hg r
  | tof a b t =>
    exact toffoliWord_run_ket n a b t hg.1 hg.2.1 hg.2.2 r

/-- The compiled finite word of a block satisfying `GBlk.ok` passes the legality test. -/
theorem GBlk.word_legal {n : ℕ} (g : GBlk n) (hg : g.ok) : finiteWordLegal n g.word = true := by
  cases g with
  | x w =>
    simp only [GBlk.word, finiteWordLegal, List.all_cons, List.all_nil, finiteCodeLegal_x n w]
    rfl
  | cx c t =>
    simp only [GBlk.word, finiteWordLegal, List.all_cons, List.all_nil, finiteCodeLegal_cx n c t hg]
    rfl
  | tof a b t => exact toffoliWord_legal n a b t hg.1 hg.2.1 hg.2.2

/-- Concatenates the finite gate-code words of a list of reversible Boolean blocks. -/
def blocksWord {n : ℕ} (bs : List (GBlk n)) : List FiniteGateCode := bs.flatMap GBlk.word

/-- Applies the Boolean updates of a list of gate blocks in list order. -/
def blocksUpd {n : ℕ} (bs : List (GBlk n)) : Reg n → Reg n :=
  fun r => bs.foldl (fun y b => b.upd y) r

/-- The compiled word of a block list is legal if every block satisfies its wire-distinctness
condition. -/
theorem blocksWord_legal {n : ℕ} (bs : List (GBlk n)) (hok : ∀ b ∈ bs, b.ok) :
    finiteWordLegal n (blocksWord bs) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨b, hb, hgb⟩ := List.mem_flatMap.mp hg
  exact List.all_eq_true.mp (GBlk.word_legal b (hok b hb)) g hgb

/-- Executing the compiled word of a valid block list realizes the successive Boolean register
updates on every basis state. -/
theorem run_blocksWord_ket {n : ℕ} (bs : List (GBlk n)) (hok : ∀ b ∈ bs, b.ok) (r : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (blocksWord bs)) (Qatlib.Foundations.PureStateMath.Ket r) =
      Qatlib.Foundations.PureStateMath.Ket (blocksUpd bs r) := by
  unfold blocksWord blocksUpd
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih =>
    have hcat : finiteCodeCircuit n (b.word ++ List.flatMap GBlk.word bs) =
        finiteCodeCircuit n b.word ++ finiteCodeCircuit n (List.flatMap GBlk.word bs) := by
      simp only [finiteCodeCircuit, List.map_append]
    simp only [List.flatMap_cons, List.foldl_cons]
    rw [hcat, run_append, GBlk.word_run_ket b (hok b (List.mem_cons.mpr (Or.inl rfl))) r]
    exact ih (fun b' hb' => hok b' (List.mem_cons.mpr (Or.inr hb'))) _

open Qatlib

/-- Builds a backend ledger with the supplied elementary gate count, classical bit-operation
count, and peak live qubit count, setting all other fields to zero. -/
def mkBackend (elementaryGates classicalBitOps peakLiveQubits : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.BackendLedger :=
  { forwardCalls := 0, backwardCalls := 0, controlledCalls := 0, positionCalls := 0,
    valueCalls := 0, elementaryGates := elementaryGates, ancillaQubits := 0,
    classicalBitOps := classicalBitOps, readoutBitOps := 0,
    peakLiveQubits := peakLiveQubits }

/-- Builds a data-access ledger from a table-read count and the gate, classical operation, and
live-qubit counts used by `mkBackend`. -/
def mkLedger (tableReads elementaryGates classicalBitOps peakLiveQubits : ℕ) :
    DataAccessLedger :=
  { backend := mkBackend elementaryGates classicalBitOps peakLiveQubits,
    tableReads := tableReads }

/-- The list of X blocks at the true bit positions of a selected input-table row. -/
def loadBlocks (t : InputTable) (i : Fin t.n) : List (GBlk t.w) :=
  (List.finRange t.w).filterMap fun b =>
    if t.cell i b = true then some (GBlk.x b) else none

/-- Compiling the X blocks for a table row gives exactly that row's `InputTable.loadWord`. -/
theorem loadBlocks_word (t : InputTable) (i : Fin t.n) :
    (loadBlocks t i).flatMap GBlk.word = t.loadWord i := by
  unfold loadBlocks InputTable.loadWord
  have key : ∀ l : List (Fin t.w),
      (l.filterMap fun b => if t.cell i b = true then some (GBlk.x b) else none).flatMap
          GBlk.word =
        l.filterMap fun b => if t.cell i b = true then some (FiniteGateCode.x b.val) else none := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      simp only [List.filterMap_cons]
      by_cases h : t.cell i b = true
      · simp only [if_pos h, List.flatMap_cons, GBlk.word, List.cons_append, List.nil_append, ih]
      · simp only [if_neg h, ih]
  exact key (List.finRange t.w)

/-- The table-loading block updates flip precisely those register bits whose corresponding
table-row entries are true. -/
theorem loadBlocks_upd (t : InputTable) (i : Fin t.n) (r : Reg t.w) :
    blocksUpd (loadBlocks t i) r = fun k => if t.cell i k = true then !r k else r k := by
  unfold blocksUpd loadBlocks
  have key : ∀ (l : List (Fin t.w)) (hl : l.Nodup) (r : Reg t.w),
      (l.filterMap fun b => if t.cell i b = true then some (GBlk.x b) else none).foldl
        (fun y b => GBlk.upd b y) r =
        fun k => if t.cell i k = true ∧ k ∈ l then !r k else r k := by
    intro l
    induction l with
    | nil =>
      intro _ r
      funext k
      simp only [List.not_mem_nil, and_false, if_false]
      rfl
    | cons b l ih =>
      intro hl r
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      have hbl : b ∉ l := (List.nodup_cons.mp hl).1
      simp only [List.filterMap_cons]
      by_cases hb : t.cell i b = true
      · have hfb : (if t.cell i b = true then some (GBlk.x b) else none) = some (GBlk.x b) :=
          if_pos hb
        rw [hfb, List.foldl_cons]
        have hupd : GBlk.upd (GBlk.x b) r = Function.update r b (!(r b)) := rfl
        rw [hupd, ih hl' (Function.update r b (!(r b)))]
        funext k
        by_cases hk : k = b
        · subst k
          simp [hbl, hb, Function.update_self]
        · simp [hk, Function.update_of_ne hk]
      · have hfb : (if t.cell i b = true then some (GBlk.x b) else none) = none := if_neg hb
        rw [hfb, ih hl' r]
        funext k
        by_cases hk : k = b
        · subst k
          simp [hb]
        · simp [hk, hb]
  have hfin := key (List.finRange t.w) (List.nodup_finRange _) r
  rw [hfin]
  funext k
  simp [List.mem_finRange]

/-- Every block in a table-row loading list satisfies its wire-distinctness condition. -/
theorem loadBlocks_ok (t : InputTable) (i : Fin t.n) : ∀ b ∈ loadBlocks t i, b.ok := by
  intro b hb
  simp only [loadBlocks, List.mem_filterMap] at hb
  obtain ⟨b', -, he⟩ := hb
  split at he
  · cases he
    trivial
  · cases he

/-- A row's loading word contains at most as many gates as there are bits in the row. -/
theorem loadWord_length (t : InputTable) (i : Fin t.n) : (t.loadWord i).length ≤ t.w := by
  have := List.length_filterMap_le (fun b : Fin t.w =>
    if t.cell i b = true then some (FiniteGateCode.x b.val) else none) (List.finRange t.w)
  simpa [InputTable.loadWord, List.length_finRange] using! this

/-- Every table-row loading word passes the finite-word legality test at the row width. -/
theorem loadWord_legal (t : InputTable) (i : Fin t.n) :
    finiteWordLegal t.w (t.loadWord i) = true := by
  rw [← loadBlocks_word]
  exact blocksWord_legal (loadBlocks t i) (loadBlocks_ok t i)

/-- Running a table-row loading word on a basis register flips exactly the bits marked true in
that row. -/
theorem loadWord_run (t : InputTable) (i : Fin t.n) (r : Reg t.w) :
    Run (1 : Matrix (Reg t.w) (Reg t.w) ℂ) (finiteCodeCircuit t.w (t.loadWord i)) (Qatlib.Foundations.PureStateMath.Ket r)
      = Qatlib.Foundations.PureStateMath.Ket (fun k => if t.cell i k = true then !r k else r k) := by
  have h := run_blocksWord_ket (loadBlocks t i) (loadBlocks_ok t i) r
  rw [loadBlocks_upd] at h
  rw [← loadBlocks_word]
  exact h

/-- Checked execution of a row's loading word on the all-false basis register returns the basis
state of that table row. -/
theorem loadWord_finiteRun (t : InputTable) (i : Fin t.n) :
    finiteWordRun t.w (t.loadWord i) (Qatlib.Foundations.PureStateMath.Ket fun _ : Fin t.w => false) = some (Qatlib.Foundations.PureStateMath.Ket (t.rowReg i)) := by
  have hleg := loadWord_legal t i
  show (if finiteWordLegal t.w (t.loadWord i) then
      some (Run (1 : Matrix (Reg t.w) (Reg t.w) ℂ) (finiteCodeCircuit t.w (t.loadWord i))
        (Qatlib.Foundations.PureStateMath.Ket fun _ : Fin t.w => false)) else none) = some (Qatlib.Foundations.PureStateMath.Ket (t.rowReg i))
  rw [if_pos hleg, loadWord_run]
  exact congrArg (fun ψ => some (Qatlib.Foundations.PureStateMath.Ket ψ)) (by
    funext k
    show (if t.cell i k = true then !((fun _ : Fin t.w => false) k)
      else (fun _ : Fin t.w => false) k) = t.cell i k
    cases t.cell i k <;> rfl)

/-- Every input table has a data-access ledger satisfying `HasTableLoad`. -/
theorem hasTableLoad (t : InputTable) : ∃ d : DataAccessLedger, HasTableLoad t d := by
  refine ⟨mkLedger (t.n * t.w) (t.n * t.w) (t.n * t.w) (t.n * t.w), ?_, rfl, ?_⟩
  · intro i
    exact ⟨loadWord_legal t i, loadWord_finiteRun t i, loadWord_length t i⟩
  · have hsum : ∀ i : Fin t.n, (t.loadWord i).length ≤ t.w := fun i => loadWord_length t i
    calc (∑ i : Fin t.n, (t.loadWord i).length) ≤ ∑ _i : Fin t.n, t.w :=
        Finset.sum_le_sum fun i _ => hsum i
      _ = t.n * t.w := by simp [nsmul_eq_mul]

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

/-- Collects unitarity, zero-query and gate counts, and state error bounds for numerical dyadic
circuits, together with local amplitude-estimation table counts and forward and adjoint QFT
approximation bounds. -/
theorem tunableGoal_macro_components :
    (∀ (n k : ℕ) (gs : List (LocalQFTGate n)),
      IsUnitaryCircuit (numericalDyadicCircuit k gs) ∧
        QueryCount (numericalDyadicCircuit k gs) = 0 ∧
        GateCount (numericalDyadicCircuit k gs) = gs.length ∧
        (∀ ψ : QState (Reg n), Normalized ψ →
          ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (numericalDyadicCircuit k gs) ψ - ApplyGate (localProgramMatrix gs) ψ)‖ ≤
            (gs.length : ℝ) * ((2 : ℝ)⁻¹) ^ k)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) (gs : List (LocalQFTGate n)),
      QueryCount (localAETableCircuit (I := I) n gs : Circuit (Fin (2 ^ n) × (Bool × I))) = 0 ∧
        GateCount (localAETableCircuit (I := I) n gs : Circuit (Fin (2 ^ n) × (Bool × I)))
          = gs.length) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (n b : ℕ),
      ‖localAEBackendMatrix (I := I) n (approxLocalQFT n b)
          - TensorGate (QFTMatrix (2 ^ n)) (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
        ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) ∧
      ‖localAEBackendMatrix (I := I) n (localProgramAdjoint (approxLocalQFT n b))
          - TensorGate (QFTMatrix (2 ^ n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
        ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1)) :=
  ⟨numerical_dyadic_program_actual_error_and_counts,
    fun I _ _ n gs => localAETableCircuit_counts (I := I) n gs,
    fun I _ _ n b => localAEBackend_error (I := I) n b⟩

/-- Native amplitude decoding lies in [0, 1], differs from the ideal estimate by at most 2^(−k),
and agrees with the decoder of every finite program at its chosen precision. -/
theorem tunableGoal_scalar_precision :
    (∀ (M k : ℕ) (z : Fin M),
      0 ≤ nativeAEDecode M k z ∧ nativeAEDecode M k z ≤ 1 ∧
        |(nativeAEDecode M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k) ∧
    (∀ (P : AEFiniteProgram) (M : ℕ) (z : Fin M), P.decode M z = nativeAEDecode M P.prec z) :=
  ⟨native_ae_computed_scalar_precision, fun _ _ _ => rfl⟩

/-- Collects counted amplitude-estimation circuit costs, output normalization and measurement
semantics, the 8/π² success bound, and the stated exact endpoint properties
[BrassardEtAl2002]. -/
theorem tunableGoal_success_event :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      let input :=
          TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))
      let O := TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (preparedMark S))
      let out := Run O (countedAECircuit M A j) input
      QueryCount (countedAECircuit M A j) = M - 1 ∧
        GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
        IsUnitaryCircuit (countedAECircuit M A j) ∧ Normalized out ∧
        (∀ z : Fin M, (aeLaw M A j S hA hM).prob z =
          MeasureProb out (Finset.univ.filter (fun p => p.1 = z))) ∧
        (∀ z i, out (z, (true, i)) = 0)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      let a := MeasureProb (preparedAAState A j) S
      (∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z - a| ≤
          2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2),
        (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 ∧
        (a = 0 → (aeLaw M A j S hA hM).prob ⟨0, by omega⟩ = 1) ∧
        (a = 1 → 2 ∣ M → ∑ z ∈ Finset.univ.filter (fun z => aeEstimate M z = 1),
          (aeLaw M A j S hA hM).prob z = 1)) :=
  ⟨fun I _ _ => prepared_ae_expanded_access_and_output (I := I),
    fun I _ _ => prepared_ae_bhmt_error_and_endpoints (I := I)⟩

/-- For nonnegative component windows, the unified error budget equals their stated sum with the
dyadic readout term and is at least that term. -/
theorem tunableGoal_error_budget :
    ∀ (initWin reflectWin qftWin : ℝ) (prec : ℕ),
      0 ≤ initWin → 0 ≤ reflectWin → 0 ≤ qftWin →
        (((2 : ℝ)⁻¹) ^ prec ≤ unifiedErrorBudget initWin reflectWin qftWin prec ∧
          unifiedErrorBudget initWin reflectWin qftWin prec =
            initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ prec) := by
  intro initWin reflectWin qftWin prec _ _ _
  refine ⟨?_, rfl⟩
  show ((2 : ℝ)⁻¹) ^ prec ≤ initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ prec
  have hnn : 0 ≤ initWin + reflectWin + 2 * qftWin := by positivity
  exact le_add_of_nonneg_left hnn

/-- The reference amplitude-estimation encoding with zero data wires and zero phase wires,
leaving only the flag wire. -/
def tunableGoalRefEnc : AEEncoding := ⟨0, 0⟩

/-- The constant matrix with entry `finiteGaussianScalar` on the unique zero-wire register. -/
noncomputable def tunableGoalRefA : Matrix (Reg 0) (Reg 0) ℂ := fun _ _ => finiteGaussianScalar

/-- The unique zero-wire register, represented by the constant false function. -/
def tunableGoalRefj : Reg 0 := fun _ => false

/-- Any two registers with zero wires are equal. -/
theorem reg0_eq (x y : Reg 0) : x = y :=
  funext fun i => (Nat.not_lt_zero i.val i.isLt).elim

/-- The reference scalar matrix on zero-wire registers is unitary. -/
theorem tunableGoalRefA_mem : tunableGoalRefA ∈ Matrix.unitaryGroup (Reg 0) ℂ := by
  have hc : star finiteGaussianScalar * finiteGaussianScalar = 1 := by
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      finite_phase_gaussian_norm, one_pow]
    rfl
  have hsmul : tunableGoalRefA = finiteGaussianScalar • (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
    funext i j
    show finiteGaussianScalar = finiteGaussianScalar * (1 : Matrix (Reg 0) (Reg 0) ℂ) i j
    rw [Matrix.one_apply, if_pos (reg0_eq i j), mul_one]
  rw [Matrix.mem_unitaryGroup_iff', hsmul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul, hc,
    one_smul]

/-- Lifting the reference scalar matrix through the reference encoding gives
`finiteGaussianScalarGate`. -/
theorem tunableGoalRef_dataLift : tunableGoalRefEnc.dataLift tunableGoalRefA = finiteGaussianScalarGate := by
  have hphase : ∀ (r s : Reg 1), tunableGoalRefEnc.phaseBits r = tunableGoalRefEnc.phaseBits s := fun r s =>
    reg0_eq _ _
  have hflag : ∀ (r s : Reg 1), (tunableGoalRefEnc.flagBit r = tunableGoalRefEnc.flagBit s) ↔ (r = s) := by
    intro r s
    constructor
    · intro h
      funext i
      fin_cases i
      exact h
    · intro h
      rw [h]
  have key : ∀ (r s : Reg 1),
      tunableGoalRefEnc.dataLift tunableGoalRefA r s = finiteGaussianScalarGate r s := by
    intro r s
    show (tunableGoalRefA (tunableGoalRefEnc.dataBits r) (tunableGoalRefEnc.dataBits s)) *
        (if tunableGoalRefEnc.phaseBits r = tunableGoalRefEnc.phaseBits s ∧
            tunableGoalRefEnc.flagBit r = tunableGoalRefEnc.flagBit s then 1 else 0) =
      finiteGaussianScalarGate r s
    rw [show tunableGoalRefA (tunableGoalRefEnc.dataBits r) (tunableGoalRefEnc.dataBits s) = finiteGaussianScalar from rfl]
    split_ifs with hcond
    · have hrs : r = s := (hflag r s).1 hcond.2
      subst hrs
      show finiteGaussianScalar * 1 = finiteGaussianScalar * (1 : Matrix (Reg 1) (Reg 1) ℂ) r r
      rw [Matrix.one_apply_eq, mul_one]
    · rw [mul_zero]
      have hrs : r ≠ s := fun hh => hcond ⟨hphase r s, (hflag r s).2 hh⟩
      show (0 : ℂ) = finiteGaussianScalar * (1 : Matrix (Reg 1) (Reg 1) ℂ) r s
      rw [Matrix.one_apply, if_neg hrs, mul_zero]
  funext r s
  exact key r s

/-- The displayed conjunction of backend guarantees is false because it includes finite
implementation of every unitary at the stated operator error tolerance. The reference scalar
gate supplies the obstruction. -/
theorem not_clause3 : ¬ (

  (∀ (n k : ℕ) (gs : List (LocalQFTGate n)),
    IsUnitaryCircuit (numericalDyadicCircuit k gs) ∧
      QueryCount (numericalDyadicCircuit k gs) = 0 ∧
      GateCount (numericalDyadicCircuit k gs) = gs.length ∧
      (∀ ψ : QState (Reg n), Normalized ψ →
        ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
            (numericalDyadicCircuit k gs) ψ - ApplyGate (localProgramMatrix gs) ψ)‖ ≤
          (gs.length : ℝ) * ((2 : ℝ)⁻¹) ^ k)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) (gs : List (LocalQFTGate n)),
    QueryCount (localAETableCircuit (I := I) n gs : Circuit (Fin (2 ^ n) × (Bool × I))) = 0 ∧
      GateCount (localAETableCircuit (I := I) n gs : Circuit (Fin (2 ^ n) × (Bool × I)))
        = gs.length) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (n b : ℕ),
    ‖localAEBackendMatrix (I := I) n (approxLocalQFT n b)
        - TensorGate (QFTMatrix (2 ^ n)) (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
      ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) ∧
    ‖localAEBackendMatrix (I := I) n (localProgramAdjoint (approxLocalQFT n b))
        - TensorGate (QFTMatrix (2 ^ n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
      ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1)) ∧

  (∀ (M k : ℕ) (z : Fin M),
    0 ≤ nativeAEDecode M k z ∧ nativeAEDecode M k z ≤ 1 ∧
      |(nativeAEDecode M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k) ∧
  (∀ (P : AEFiniteProgram) (M : ℕ) (z : Fin M), P.decode M z = nativeAEDecode M P.prec z) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
    let input :=
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))
    let O := TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (preparedMark S))
    let out := Run O (countedAECircuit M A j) input
    QueryCount (countedAECircuit M A j) = M - 1 ∧
      GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
      IsUnitaryCircuit (countedAECircuit M A j) ∧ Normalized out ∧
      (∀ z : Fin M, (aeLaw M A j S hA hM).prob z =
        MeasureProb out (Finset.univ.filter (fun p => p.1 = z))) ∧
      (∀ z i, out (z, (true, i)) = 0)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z - a| ≤
        2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 ∧
      (a = 0 → (aeLaw M A j S hA hM).prob ⟨0, by omega⟩ = 1) ∧
      (a = 1 → 2 ∣ M → ∑ z ∈ Finset.univ.filter (fun z => aeEstimate M z = 1),
        (aeLaw M A j S hA hM).prob z = 1)) ∧

  (∀ (enc : AEEncoding) (A : Matrix (Reg enc.dataWires) (Reg enc.dataWires) ℂ)
      (j : Reg enc.dataWires) (_hA : A ∈ Matrix.unitaryGroup (Reg enc.dataWires) ℂ)
      (initWin reflectWin qftWin : ℝ) (prec : ℕ),
    0 < initWin → 0 ≤ reflectWin → 0 < qftWin →
      ∃ (P : AEFiniteProgram) (d : AEProgramLedger),
        P.prec = prec ∧ HasAEFiniteImplementation enc P A j initWin reflectWin qftWin d) ∧

  (∀ (initWin reflectWin qftWin : ℝ) (prec : ℕ),
    0 ≤ initWin → 0 ≤ reflectWin → 0 ≤ qftWin →
      ((2 : ℝ)⁻¹) ^ prec ≤ unifiedErrorBudget initWin reflectWin qftWin prec ∧
        unifiedErrorBudget initWin reflectWin qftWin prec =
          initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ prec)) := by
  intro h

  have c8 := h.2.2.2.2.2.2.2.1

  obtain ⟨P, _d, _, hImpl⟩ :=
    c8 tunableGoalRefEnc tunableGoalRefA tunableGoalRefj tunableGoalRefA_mem ((1:ℝ)/64) 0 1 0
      (by norm_num) (by norm_num) (by norm_num)
  have hreal : RealizesOperatorWithin tunableGoalRefEnc.workspace P.initWord
      (tunableGoalRefEnc.dataLift tunableGoalRefA) ((1:ℝ)/64) := hImpl.1
  have hlegal : finiteWordLegal tunableGoalRefEnc.workspace P.initWord = true := hreal.1
  have hbound : ∀ ψ : QState (Reg tunableGoalRefEnc.workspace), Normalized ψ →
      ‖toEuclidean_fromVec (Run (1 : Matrix (Reg tunableGoalRefEnc.workspace) (Reg tunableGoalRefEnc.workspace) ℂ)
        (finiteCodeCircuit tunableGoalRefEnc.workspace P.initWord) ψ -
        ApplyGate (tunableGoalRefEnc.dataLift tunableGoalRefA) ψ)‖ ≤ ((1:ℝ)/64) := hreal.2

  obtain ⟨_, x, hx, hgap⟩ := finite_gaussian_scalar_obstruction.2.2 P.initWord hlegal
  have hle : ‖toEuclidean_fromVec (Run (1 : Matrix (Reg 1) (Reg 1) ℂ)
      (finiteCodeCircuit 1 P.initWord) (Qatlib.Foundations.PureStateMath.Ket x) -
      ApplyGate finiteGaussianScalarGate (Qatlib.Foundations.PureStateMath.Ket x))‖ ≤ ((1:ℝ)/64) := by
    have h := hbound (Qatlib.Foundations.PureStateMath.Ket x) hx
    rw [tunableGoalRef_dataLift] at h
    exact h
  exact absurd (le_trans hgap hle) (by norm_num)

/-- Every input table has a data-access ledger satisfying the translation inequalities with the
displayed loading, comparison, and extraction budgets. -/
theorem hasDataAccessTranslation (t : InputTable) :
    ∃ d : DataAccessLedger,
      HasDataAccessTranslation t t.w (32 * (t.w + 1) * (t.w + 1))
        (16 * (t.w + 1) * (t.w + 1)) d := by
  refine ⟨mkLedger 0 (48 * (t.w + 1) * (t.w + 1)) (48 * (t.w + 1) * (t.w + 1))
      (2 * t.w + 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · show t.w ≤ t.w
    exact le_refl _
  · show 32 * (t.w + 1) * (t.w + 1) ≤ 32 * (t.w + 1) * (t.w + 1)
    exact le_refl _
  · show 16 * (t.w + 1) * (t.w + 1) ≤ 16 * (t.w + 1) * (t.w + 1)
    exact le_refl _
  · show (0 : ℕ) = 0 * t.w
    exact (zero_mul _).symm
  · show (0 : ℕ) * t.w + 32 * (t.w + 1) * (t.w + 1) + 16 * (t.w + 1) * (t.w + 1) ≤
      48 * (t.w + 1) * (t.w + 1)
    have h : 32 * (t.w + 1) * (t.w + 1) + 16 * (t.w + 1) * (t.w + 1) =
        48 * (t.w + 1) * (t.w + 1) := by ring
    omega
  · show 48 * (t.w + 1) * (t.w + 1) ≤ 48 * (t.w + 1) * (t.w + 1)
    exact le_refl _
  · show 2 * t.w + 1 ≤ 2 * t.w + 1
    exact le_refl _

/-- Selects the new index when its row value is strictly smaller than the current best row
value, retaining the current best otherwise. -/
def argminStep (t : InputTable) (best i : Fin t.n) : Fin t.n :=
  if regValue (t.rowReg i) < regValue (t.rowReg best) then i else best

/-- An `argminStep` produces a row value no greater than that of the current best index. -/
theorem argminStep_le_best (t : InputTable) (best i : Fin t.n) :
    regValue (t.rowReg (argminStep t best i)) ≤ regValue (t.rowReg best) := by
  unfold argminStep
  split_ifs with h
  · exact le_of_lt h
  · exact le_refl _

/-- An `argminStep` produces a row value no greater than that of the candidate index. -/
theorem argminStep_le_self (t : InputTable) (best i : Fin t.n) :
    regValue (t.rowReg (argminStep t best i)) ≤ regValue (t.rowReg i) := by
  unfold argminStep
  split_ifs with h
  · exact le_refl _
  · exact Nat.le_of_not_lt h

/-- For a nonempty input table, the row selected by `InputTable.argmin` has value no greater
than every table row. -/
theorem argmin_min (t : InputTable) (hn : 0 < t.n) (i : Fin t.n) :
    regValue (t.rowReg (t.argmin hn)) ≤ regValue (t.rowReg i) := by
  have key : ∀ (l : List (Fin t.n)) (best : Fin t.n),
      regValue (t.rowReg (l.foldl (argminStep t) best)) ≤ regValue (t.rowReg best) ∧
        ∀ j ∈ l, regValue (t.rowReg (l.foldl (argminStep t) best)) ≤ regValue (t.rowReg j) := by
    intro l
    induction l with
    | nil =>
      intro best
      refine ⟨le_refl _, fun j hj => ?_⟩
      exact False.elim (List.not_mem_nil hj)
    | cons b l ih =>
      intro best
      have ih' := ih (argminStep t best b)
      obtain ⟨hle, hmem⟩ := ih'
      refine ⟨le_trans hle (argminStep_le_best t best b), fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_trans hle (argminStep_le_self t best j)
      · exact hmem j hj
  have hkey := key (List.finRange t.n) ⟨0, hn⟩
  have hform : (List.finRange t.n).foldl (argminStep t) (⟨0, hn⟩ : Fin t.n) = t.argmin hn := by
    show (List.finRange t.n).foldl (argminStep t) (⟨0, hn⟩ : Fin t.n) =
      (List.finRange t.n).foldl
        (fun best i => if regValue (t.rowReg i) < regValue (t.rowReg best) then i else best) ⟨0, hn⟩
    rfl
  rw [← hform]
  exact hkey.2 i (List.mem_finRange i)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
