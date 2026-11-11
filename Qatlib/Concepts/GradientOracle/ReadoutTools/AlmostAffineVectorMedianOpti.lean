/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianStat
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineCoordinateReadoutOpti

/-!
# Median amplification of gradient coordinates

This module identifies fresh-register executions with product states and relates counted
rational selection to real sorted medians. It proves simultaneous coordinate accuracy and
explicit resource bounds for the median procedure associated with [GilyenArunachalamWiebe2019].

## Main statements

* `almostAffineVectorMedian`: repeated readout has product outcome masses and failure at most `d
  * (143/144)^r`, with a repetition choice achieving the requested tolerance.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

namespace AlmostAffineVectorMedianAux

/-- Evaluating the reversed prepared translation of a circuit with data oracle `U` and identity
input oracle has the same state action as `Run U` on the original circuit. -/
private theorem gradient_bridge (d M : ℕ) (U : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) :
    ∀ (L : List (Step (GradientGrid d M))) (ψ : QState (GradientGrid d M)),
      ApplyGate (evaluatePrepared U 1 (L.reverse.map fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward)) ψ = Run U L ψ := by
  intro L
  induction L with
  | nil => intro ψ; simp [evaluatePrepared]
  | cons s L ih =>
    intro ψ
    have hmap : (s :: L).reverse.map (fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward) =
        L.reverse.map (fun s => match s with
          | Step.gate V => PreparedStep.gate V
          | Step.query => PreparedStep.dataForward) ++ [match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward] := by
      simp [List.reverse_cons, List.map_append]
    rw [hmap, evaluatePrepared_append, applyGate_mul]
    cases s with
    | gate V =>
      have hev : evaluatePrepared U 1 [PreparedStep.gate V] = V := by
        simp [evaluatePrepared, preparedInstruction]
      rw [hev, run_gate]
      exact ih _
    | query =>
      have hev : evaluatePrepared U 1 [PreparedStep.dataForward] = U := by
        simp [evaluatePrepared, preparedInstruction]
      rw [hev, run_query]
      exact ih _

/-- The fresh-register gradient output is the `R`-fold fresh product state of the single-run
gradient readout. -/
private theorem gradientFreshOutput_eq (d M : ℕ) (hM : 0 < M)
    (φ : GradientGrid d M → ℝ) (R : ℕ) :
    gradientFreshOutput d M hM φ R = freshState (gradientReadout d M hM φ) R := by
  unfold gradientFreshOutput gradientFreshWord
  rw [evaluateFresh_apply_zero (gradientPhase d M φ) 1 (gradientPreparedWord d M)
    (gradientZero d M hM) R]
  congr 1
  exact gradient_bridge d M (gradientPhase d M φ) (gradientWord d M) (Ket (gradientZero d M hM))

/-- The Born probability of a recorded tuple in a fresh product state equals the product of the
individual outcome probabilities. -/
private theorem freshState_BornProb {H : Type} [Fintype H] [DecidableEq H] (ψ : QState H) :
    ∀ (R : ℕ) (ω : Fin R → H),
      BornProb (freshState ψ R) (gradientFreshRecord ω) = ∏ t, BornProb ψ (ω t) := by
  intro R
  induction R with
  | zero =>
    intro ω
    show ‖(1:ℂ)‖^2 = 1
    simp
  | succ R ih =>
    intro ω
    have h1 : TensorState ψ (freshState ψ R) (ω 0, gradientFreshRecord fun i => ω i.succ)
        = ψ (ω 0) * (freshState ψ R) (gradientFreshRecord fun i => ω i.succ) := rfl
    have hL : BornProb (TensorState ψ (freshState ψ R))
        (ω 0, gradientFreshRecord fun i => ω i.succ)
        = BornProb ψ (ω 0)
          * BornProb (freshState ψ R) (gradientFreshRecord fun i => ω i.succ) := by
      show ‖TensorState ψ (freshState ψ R) (ω 0, gradientFreshRecord fun i => ω i.succ)‖^2
        = ‖ψ (ω 0)‖^2
          * ‖(freshState ψ R) (gradientFreshRecord fun i => ω i.succ)‖^2
      rw [h1, norm_mul, mul_pow]
    rw [Fin.prod_univ_succ]
    show BornProb (TensorState ψ (freshState ψ R))
        (ω 0, gradientFreshRecord fun i => ω i.succ)
      = BornProb ψ (ω 0) * ∏ t : Fin R, BornProb ψ ((fun i => ω i.succ) t)
    rw [hL, ih]

/-- For a normalized state, the probabilities of all recorded tuples in its fresh product state
sum to one. -/
private theorem freshState_mass_sum {H : Type} [Fintype H] [DecidableEq H] {ψ : QState H}
    (hψ : Normalized ψ) (R : ℕ) :
    ∑ ω : Fin R → H, BornProb (freshState ψ R) (gradientFreshRecord ω) = 1 := by
  let hp : FinDist H :=
    ⟨fun x => BornProb ψ x, fun x => bornProb_nonneg ψ x, measureProb_univ hψ⟩
  have hrw : ∑ ω : Fin R → H, BornProb (freshState ψ R) (gradientFreshRecord ω)
      = ∑ ω : Fin R → H, FinDist.probOf hp ω :=
    Finset.sum_congr rfl fun ω _ => freshState_BornProb ψ R ω
  rw [hrw, hp.sum_probOf]

/-- The reversed prepared translation preserves data-query and fixed-gate counts and uses zero
input queries. -/
private theorem reverse_counts (d M : ℕ) :
    ∀ (L : List (Step (GradientGrid d M))),
      preparedDataQueries (L.reverse.map fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward) = QueryCount L ∧
      preparedInputQueries (L.reverse.map fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward) = 0 ∧
      preparedFixedGates (L.reverse.map fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward) = GateCount L := by
  intro L
  induction L with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons s L ih =>
    have hmap : (s :: L).reverse.map (fun s => match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward) =
        L.reverse.map (fun s => match s with
          | Step.gate V => PreparedStep.gate V
          | Step.query => PreparedStep.dataForward) ++ [match s with
        | Step.gate V => PreparedStep.gate V
        | Step.query => PreparedStep.dataForward] := by
      simp [List.reverse_cons, List.map_append]
    rw [hmap]
    obtain ⟨ha, hb, hc⟩ := preparedCounts_append _ _
    rw [ha, hb, hc]
    cases s with
    | gate V =>
      have h0 : preparedDataQueries [PreparedStep.gate V] = 0 ∧
          preparedInputQueries [PreparedStep.gate V] = 0 ∧
          preparedFixedGates [PreparedStep.gate V] = 1 := by
        simp [preparedDataQueries, preparedInputQueries, preparedFixedGates]
      rw [h0.1, h0.2.1, h0.2.2, ih.1, ih.2.1, ih.2.2]
      simp [queryCount_gate, gateCount_gate]
    | query =>
      have h0 : preparedDataQueries [PreparedStep.dataForward (H := GradientGrid d M)] = 1 ∧
          preparedInputQueries [PreparedStep.dataForward (H := GradientGrid d M)] = 0 ∧
          preparedFixedGates [PreparedStep.dataForward (H := GradientGrid d M)] = 0 := by
        simp [preparedDataQueries, preparedInputQueries, preparedFixedGates]
      rw [h0.1, h0.2.1, h0.2.2, ih.1, ih.2.1, ih.2.2]
      simp [queryCount_query, gateCount_query]

/-- The prepared gradient word has the data-query and gate counts of `gradientWord` and has no
input queries. -/
private theorem gradientPreparedWord_counts (d M : ℕ) :
    preparedDataQueries (gradientPreparedWord d M) = QueryCount (gradientWord d M) ∧
    preparedInputQueries (gradientPreparedWord d M) = 0 ∧
    preparedFixedGates (gradientPreparedWord d M) = GateCount (gradientWord d M) :=
  reverse_counts d M (gradientWord d M)

/-- Pointwise equivalent predicates on outcome tuples have equal event probability under the
same finite distribution. -/
private theorem probEvent_of_iff {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} {E E' : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E ω ↔ E' ω) : FinDist.probEvent p E = FinDist.probEvent p E' := by
  have hset : Finset.univ.filter E = Finset.univ.filter E' := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h ω
  unfold FinDist.probEvent
  rw [hset]

/-- Casting rational signed grid decoding to the reals gives `signedGridValue`. -/
private theorem gradientSignedValueQ_cast (M : ℕ) (z : Fin M) :
    ((gradientSignedValueQ M z : ℚ) : ℝ) = signedGridValue M z := by
  by_cases h : 2*z.val ≤ M
  · rw [gradientSignedValueQ, if_pos h, signedGridValue, if_pos h]
    push_cast
    ring
  · rw [gradientSignedValueQ, if_neg h, signedGridValue, if_neg h]
    push_cast
    ring

/-- The real cast of the counted rational median equals the sorted-block median of the real
signed coordinate outcomes. -/
private theorem gradientMedianCounted_cast {d M : ℕ} (r : ℕ)
    (ω : Fin (2*r+1) → GradientGrid d M) (j : Fin d) :
    ((gradientMedianCounted r ω j).1 : ℝ)
      = sortedBlockMedian r (fun t => signedGridValue M (ω t j)) := by
  have hsem := (rational_selection_median_exact_real_sorted_semantics r
    (fun t => gradientSignedValueQ M (ω t j))).1
  unfold gradientMedianCounted at hsem ⊢
  rw [hsem]
  congr 1
  funext t
  exact gradientSignedValueQ_cast M (ω t j)

/-- Selecting the counted median of `2*r+1` coordinate outcomes uses at most `10000*(2*r+1)`
comparisons. -/
private theorem gradientMedianCounted_count {d M : ℕ} (r : ℕ)
    (ω : Fin (2*r+1) → GradientGrid d M) (j : Fin d) :
    (gradientMedianCounted r ω j).2 ≤ 10000*(2*r+1) :=
  (rational_selection_median_exact_real_sorted_semantics r
    (fun t => gradientSignedValueQ M (ω t j))).2

end AlmostAffineVectorMedianAux
open Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianAux

/-- Proves normalized repeated readout with product outcome masses, simultaneous
coordinate-median accuracy, and the stated circuit and comparison bounds. The failure bound
`d*(143/144)^r` and its prescribed confidence choice implement amplification associated with
[GilyenArunachalamWiebe2019]. -/
theorem almostAffineVectorMedian : AlmostAffineVectorMedian := by
  intro d n hN φ g c S hg hbad hgood
  have hnormψ : Normalized (gradientReadout d (2^n) hN φ) :=
    (gradient_coordinate_qft_word_unitarity d (2^n) hN).1.normalized_run
      (gradientPhase_unitary d (2^n) φ) (normalized_ket _)
  have hsem := (almostAffineCoordinateReadout d n hN φ g c S hg hbad hgood).1
  have hconf : ∀ (r : ℕ),
      1-(d:ℝ)*(143/144 : ℝ)^r ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2 : ℝ)^n),
          gradientFreshMass d (2^n) hN φ ω := by
    intro r
    let hp : FinDist (GradientGrid d (2^n)) :=
      ⟨fun x => BornProb (gradientReadout d (2^n) hN φ) x,
        fun x => bornProb_nonneg (gradientReadout d (2^n) hN φ) x,
        measureProb_univ hnormψ⟩
    have hnn : ∀ ω : Fin (2*r+1) → GradientGrid d (2^n), 0 ≤ FinDist.probOf hp ω :=
      fun ω => Finset.prod_nonneg fun _ _ => hp.nonneg _
    have hmassω : ∀ ω : Fin (2*r+1) → GradientGrid d (2^n),
        gradientFreshMass d (2^n) hN φ ω = FinDist.probOf hp ω := by
      intro ω
      unfold gradientFreshMass
      rw [gradientFreshOutput_eq]
      exact freshState_BornProb (gradientReadout d (2^n) hN φ) _ ω
    have hsum1 : (∑ ω : Fin (2*r+1) → GradientGrid d (2^n),
        gradientFreshMass d (2^n) hN φ ω) = 1 := by
      have hrw : ∑ ω : Fin (2*r+1) → GradientGrid d (2^n),
          gradientFreshMass d (2^n) hN φ ω =
          ∑ ω : Fin (2*r+1) → GradientGrid d (2^n),
            BornProb (freshState (gradientReadout d (2^n) hN φ) (2*r+1))
              (gradientFreshRecord ω) :=
        Finset.sum_congr rfl fun ω _ => by
          unfold gradientFreshMass
          rw [gradientFreshOutput_eq]
      rw [hrw]
      exact freshState_mass_sum hnormψ _
    have hbadev : ∀ j : Fin d,
        FinDist.probEvent hp (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|)
          ≤ (143/144 : ℝ)^r := by
      intro j
      have hbad : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass hp (fun z : GradientGrid d (2^n) =>
          4/(2:ℝ)^n < |signedGridValue (2^n) (z j)-g j|) ≤ 11/24 := by
        have hc := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement hp (fun z : GradientGrid d (2^n) =>
          |signedGridValue (2^n) (z j)-g j| ≤ 4/(2:ℝ)^n)
        have hgoodmass : 2/3 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass hp (fun z : GradientGrid d (2^n) =>
            |signedGridValue (2^n) (z j)-g j| ≤ 4/(2:ℝ)^n) := hsem j
        have hnot : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass hp (fun z : GradientGrid d (2^n) =>
            ¬ |signedGridValue (2^n) (z j)-g j| ≤ 4/(2:ℝ)^n)
            = Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass hp (fun z : GradientGrid d (2^n) =>
          4/(2:ℝ)^n < |signedGridValue (2^n) (z j)-g j|) := by
          congr 1
          funext z
          simp [not_le]
        rw [hnot] at hc
        linarith
      have hf := native_sorted_median_failure hp
        (fun z : GradientGrid d (2^n) => signedGridValue (2^n) (z j)) r (g j)
        (4/(2:ℝ)^n) (by positivity) hbad
      have hiff : ∀ ω : Fin (2*r+1) → GradientGrid d (2^n),
          (4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|) ↔
          (4/(2:ℝ)^n < |sortedBlockMedian r (fun t => signedGridValue (2^n) (ω t j))-g j|) := by
        intro ω
        rw [gradientMedianCounted_cast r ω j]
      exact (probEvent_of_iff hp hiff).trans_le hf
    have hub := FinDist.union_bound (L := 2*r+1) (E := fun (j : Fin d)
        (ω : Fin (2*r+1) → GradientGrid d (2^n)) =>
          4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|) hp
    have hsub : Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n)
        ⊆ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ∃ j : Fin d, 4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|) := by
      intro ω hω
      have hne : ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n :=
        (Finset.mem_filter.mp hω).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨j, hj⟩ := not_forall.mp hne
      exact ⟨j, lt_of_not_ge hj⟩
    have hmono : (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n),
          FinDist.probOf hp ω)
        ≤ (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ∃ j : Fin d, 4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|),
          FinDist.probOf hp ω) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro ω _ _
      exact hnn ω
    have hbadsum : (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n),
          gradientFreshMass d (2^n) hN φ ω) ≤ (d:ℝ)*(143/144 : ℝ)^r := by
      calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
            ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n),
            gradientFreshMass d (2^n) hN φ ω)
          = ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
              ¬ ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n),
              FinDist.probOf hp ω :=
            Finset.sum_congr rfl fun ω _ => hmassω ω
        _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
              ∃ j : Fin d, 4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|),
              FinDist.probOf hp ω := hmono
        _ = FinDist.probEvent hp (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
              ∃ j : Fin d, 4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|) := rfl
        _ ≤ ∑ j : Fin d, FinDist.probEvent hp
              (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
                4/(2:ℝ)^n < |((gradientMedianCounted r ω j).1 : ℝ)-g j|) := hub
        _ ≤ ∑ j : Fin d, (143/144 : ℝ)^r := Finset.sum_le_sum fun j _ => hbadev j
        _ = (d:ℝ)*(143/144 : ℝ)^r := by
            simp [Finset.sum_const]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
        ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2:ℝ)^n)
      (fun ω => gradientFreshMass d (2^n) hN φ ω)
    rw [hsum1] at hsplit
    linarith
  refine ⟨?_, ?_⟩
  · intro r
    refine ⟨?_, ?_, ?_, hconf r, ?_, ?_, ?_, ?_⟩
    · rw [gradientFreshOutput_eq]
      exact freshState_normalized hnormψ _
    · intro ω
      unfold gradientFreshMass
      rw [gradientFreshOutput_eq]
      exact freshState_BornProb (gradientReadout d (2^n) hN φ) _ ω
    · have hrw : ∑ ω : Fin (2*r+1) → GradientGrid d (2^n),
          gradientFreshMass d (2^n) hN φ ω =
          ∑ ω : Fin (2*r+1) → GradientGrid d (2^n),
            BornProb (freshState (gradientReadout d (2^n) hN φ) (2*r+1))
              (gradientFreshRecord ω) :=
        Finset.sum_congr rfl fun ω _ => by
          unfold gradientFreshMass
          rw [gradientFreshOutput_eq]
      rw [hrw]
      exact freshState_mass_sum hnormψ _
    · have hc := compileFresh_counts (gradientPreparedWord d (2^n)) (2*r+1)
      have hcounts := gradientPreparedWord_counts d (2^n)
      rw [show gradientFreshWord d (2^n) (2*r+1)
          = compileFresh (gradientPreparedWord d (2^n)) (2*r+1) from rfl,
        hc.1, hcounts.1, (gradient_coordinate_qft_word_unitarity d (2^n) hN).2.1]
      norm_num
    · have hc := compileFresh_counts (gradientPreparedWord d (2^n)) (2*r+1)
      have hcounts := gradientPreparedWord_counts d (2^n)
      rw [show gradientFreshWord d (2^n) (2*r+1)
          = compileFresh (gradientPreparedWord d (2^n)) (2*r+1) from rfl,
        hc.2.1, hcounts.2.1]
      simp
    · have hc := compileFresh_counts (gradientPreparedWord d (2^n)) (2*r+1)
      have hcounts := gradientPreparedWord_counts d (2^n)
      rw [show gradientFreshWord d (2^n) (2*r+1)
          = compileFresh (gradientPreparedWord d (2^n)) (2*r+1) from rfl,
        hc.2.2, hcounts.2.2, (gradient_coordinate_qft_word_unitarity d (2^n) hN).2.2]
      ring
    · intro ω
      refine ⟨fun j => gradientMedianCounted_cast r ω j, ?_⟩
      calc ∑ j, (gradientMedianCounted r ω j).2
          ≤ ∑ j : Fin d, 10000*(2*r+1) :=
            Finset.sum_le_sum fun j _ => gradientMedianCounted_count r ω j
        _ = d*10000*(2*r+1) := by
            simp [Finset.sum_const]
            ring
  · intro δ hδpos _hδ1
    have hδR : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδpos
    have hA : d ≤ 2^(Nat.clog 2 (max 1 d)) :=
      (le_max_right 1 d).trans (Nat.le_pow_clog (by norm_num : (1:ℕ) < 2) _)
    have hdR : (d:ℝ) ≤ (2:ℝ)^(Nat.clog 2 (max 1 d)) := by
      exact_mod_cast hA
    have hceil : (1:ℚ)/δ ≤ ((Nat.ceil ((1:ℚ)/δ) : ℕ) : ℚ) := Nat.le_ceil _
    have hB : ((Nat.ceil ((1:ℚ)/δ) : ℕ) : ℚ)
        ≤ ((2^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ)))) : ℕ) : ℚ) := by
      have h := Nat.le_pow_clog (by norm_num : (1:ℕ) < 2) (max 1 (Nat.ceil ((1:ℚ)/δ)))
      exact_mod_cast (le_max_right 1 _).trans h
    have h1δ : (1:ℝ)/((δ:ℝ))
        ≤ (2:ℝ)^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ)))) := by
      exact_mod_cast hceil.trans hB
    have h143R : ((143:ℝ)/144)^100 ≤ 1/2 := by norm_num
    have hrdef : gradientMedianRepetitions d δ = 100*(Nat.clog 2 (max 1 d)
        + Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))) + 1) := rfl
    have hle : (d:ℝ)*(143/144 : ℝ)^(gradientMedianRepetitions d δ) ≤ (δ:ℝ) := by
      rw [hrdef, pow_mul]
      calc (d:ℝ)*(((143:ℝ)/144)^100)^(Nat.clog 2 (max 1 d)
            + Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))) + 1)
          ≤ (d:ℝ)*((1:ℝ)/2)^(Nat.clog 2 (max 1 d)
            + Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))) + 1) :=
            mul_le_mul_of_nonneg_left
              (show (((143:ℝ)/144)^100)^(Nat.clog 2 (max 1 d)
                + Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))) + 1)
                ≤ ((1:ℝ)/2)^(Nat.clog 2 (max 1 d)
                + Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))) + 1) from
                pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ ((143:ℝ)/144)^100) h143R _)
              (by positivity)
        _ = (d:ℝ)*((1:ℝ)/((2:ℝ)^(Nat.clog 2 (max 1 d))
            *((2:ℝ)^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))))*2))) := by
            rw [_root_.one_div_pow, pow_add, pow_add, pow_one]
            ring
        _ ≤ (2:ℝ)^(Nat.clog 2 (max 1 d))*((1:ℝ)/((2:ℝ)^(Nat.clog 2 (max 1 d))
            *((2:ℝ)^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))))*2))) :=
            mul_le_mul_of_nonneg_right hdR (by positivity)
        _ = (1:ℝ)/(2*(2:ℝ)^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ))))) := by
            field_simp
        _ ≤ (δ:ℝ) := by
            apply (div_le_iff₀ (by positivity :
              (0:ℝ) < 2*(2:ℝ)^(Nat.clog 2 (max 1 (Nat.ceil ((1:ℚ)/δ)))))).mpr
            have hb := (div_le_iff₀ hδR).mp h1δ
            nlinarith [hb]
    refine ⟨hle, ?_⟩
    have h := hconf (gradientMedianRepetitions d δ)
    linarith

end Qatlib.Concepts.GradientOracle.ReadoutTools
