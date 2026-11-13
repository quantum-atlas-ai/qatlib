/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedSearchAttemptStat
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptionCounterexampleContracts
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsAqua

/-!
# Observed traces of interrupted search attempts

This module identifies phase-observation traces and acceptance probabilities after a search
circuit or query prefix. The theorem `interruptedSearchAttempt` assembles the corrected
interruption contract, while `interruptedSearchAttempt_counterexample` refutes the legacy
truncation contract.

The observation formulas provide the search-call semantics used in minimum finding
[DurrHoyer1996].

## Main statements

* `phaseCall_acceptance`: The acceptance probability of a circuit followed by search phase
  observation equals the measurement probability of the marked-index subspace.
* `interruptedSearchAttempt`: Establishes the query-prefix observation, query-count,
  normalization, success-comparison, and reconstruction guarantees in `InterruptedSearchAttempt`
  for the minimum-search setting [DurrHoyer1996].

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.SearchStopping.GroverSuccess
open scoped Classical BigOperators

/-- The legacy interrupted-search-attempt contract is false. -/
theorem interruptedSearchAttempt_counterexample : ¬ InterruptedSearchAttemptLegacy := by
  intro h
  have hN : 0 < Fintype.card (Fin 1) := by norm_num
  let A : Finset (Fin 1) := Finset.univ
  let O := BitOracleOn (fun x : Fin 1 => decide (x ∈ A))
  let ψ : QState (Fin 1 × Bool) := WithMinus (Uniform (Fin 1))
  have hcut : truncateObservedQueries (searchPhaseAttempt A 1) 0 = ObservedCircuit.halt false := by
    simp [searchPhaseAttempt, SearchCircuit, Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit, Qatlib.Concepts.SearchStopping.KnownCount.GroverStep,
      RepeatCircuit, LiftCircuit, observedOfCircuit, truncateObservedQueries]
  have hprefix : queryPrefix (LiftCircuit (SearchCircuit (Fin 1) 1)) 0 = [] := by
    simp [SearchCircuit, Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit, Qatlib.Concepts.SearchStopping.KnownCount.GroverStep,
      RepeatCircuit, LiftCircuit, queryPrefix]
  have hnorm : Normalized ψ := normalized_tensorState (normalized_uniform hN) normalized_minus
  have hmass : MeasureProb ψ (A ×ˢ Finset.univ) = 1 := by
    simpa [A] using! measureProb_univ hnorm
  have he := (h (Fin 1) hN A 1 0).1
  change observedAcceptance O (truncateObservedQueries (searchPhaseAttempt A 1) 0) ψ =
    MeasureProb (Run O (queryPrefix (LiftCircuit (SearchCircuit (Fin 1) 1)) 0) ψ)
      (A ×ˢ Finset.univ) at he
  rw [hcut, hprefix, show Run O [] ψ = ψ from rfl, hmass] at he
  simp [observedAcceptance, observedTraces] at he

/-- The branch trace obtained by measuring index outcome `o`, recording one measurement, the
supplied query and gate counts, and acceptance precisely for a marked index. -/
private noncomputable def phaseTrace {I : Type} [Fintype I] [DecidableEq I]
    (A : Finset I) (ψ : QState (I × Bool)) (q g : ℕ) (o : Fin (Fintype.card I)) :
    BranchTrace (I × Bool) :=
  { state := Collapse ψ (Finset.univ.filter (fun x => Fintype.equivFin I x.1 = o))
    accepted := decide ((Fintype.equivFin I).symm o ∈ A)
    queries := q
    gates := g
    measurements := 1
    outcomes := [(Fintype.card I, o.val)] }

/-- A circuit followed by the search phase observation has the list of index-measurement traces
given by `phaseTrace`. -/
theorem phaseCall_traces {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix (I × Bool) (I × Bool) ℂ) (C : Circuit (I × Bool))
    (A : Finset I) (ψ : QState (I × Bool)) :
    observedTraces O (observedOfCircuit C (searchPhaseObservation A)) ψ =
      List.ofFn (phaseTrace A (Run O C ψ) (QueryCount C) (GateCount C)) := by
  induction C generalizing ψ with
  | nil =>
    simp only [observedOfCircuit, searchPhaseObservation, observedTraces, List.map_singleton,
      Run, QueryCount, GateCount]
    change (List.ofFn (fun o => [phaseTrace A ψ 0 0 o])).flatten = _
    have hmap : List.ofFn (fun o => [phaseTrace A ψ 0 0 o]) =
        (List.ofFn (phaseTrace A ψ 0 0)).map (fun t => [t]) := by
      simpa only [Function.comp_def] using
          (List.map_ofFn (f := phaseTrace A ψ 0 0) (g := fun t => [t])).symm
    rw [hmap, ← List.flatMap_def, List.flatMap_singleton']
  | cons s C ih =>
    cases s with
    | query =>
      simp only [observedOfCircuit, observedTraces, ih, List.map_ofFn]
      congr 1
    | gate U =>
      simp only [observedOfCircuit, observedTraces, ih, List.map_ofFn]
      congr 1

/-- The sum of masses of accepted traces equals the sum over all traces with rejected masses
replaced by zero. -/
private theorem acceptance_sum_if {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (BranchTrace I)) :
    ((ts.filter (fun t => t.accepted)).map (fun t => branchMass t.state)).sum =
      (ts.map (fun t => if t.accepted then branchMass t.state else 0)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases h : t.accepted <;> simp [h, ih]

/-- The acceptance probability of a circuit followed by search phase observation equals the
measurement probability of the marked-index subspace. -/
theorem phaseCall_acceptance {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix (I × Bool) (I × Bool) ℂ) (C : Circuit (I × Bool))
    (A : Finset I) (ψ : QState (I × Bool)) :
    observedAcceptance O (observedOfCircuit C (searchPhaseObservation A)) ψ =
      MeasureProb (Run O C ψ) (A ×ˢ Finset.univ) := by
  rw [observedAcceptance_eq_sum, acceptance_sum_if, phaseCall_traces]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, phaseTrace, decide_eq_true_eq]
  simp_rw [branchMass, measureProb_collapse, Finset.inter_univ]
  have hset : A ×ˢ (Finset.univ : Finset Bool) =
      Finset.univ.filter (fun x : I × Bool => x.1 ∈ A) := by ext x; simp
  rw [hset]
  simp only [MeasureProb, Finset.sum_filter]
  have hite (o : Fin (Fintype.card I)) :
      (if (Fintype.equivFin I).symm o ∈ A then
        ∑ x : I × Bool, if Fintype.equivFin I x.1 = o then BornProb (Run O C ψ) x else 0
        else 0) =
      ∑ x : I × Bool, if (Fintype.equivFin I).symm o ∈ A then
        (if Fintype.equivFin I x.1 = o then BornProb (Run O C ψ) x else 0) else 0 := by
    by_cases h : (Fintype.equivFin I).symm o ∈ A <;> simp [h]
  simp_rw [hite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x.1 ∈ A
  · have hsum : (∑ o : Fin (Fintype.card I),
        if (Fintype.equivFin I).symm o ∈ A then
          (if Fintype.equivFin I x.1 = o then BornProb (Run O C ψ) x else 0) else 0) =
        BornProb (Run O C ψ) x := by
      rw [Finset.sum_eq_single (Fintype.equivFin I x.1)]
      · simp [hx]
      · intro o _ ho
        simp [Ne.symm ho]
      · intro hn
        exact (hn (Finset.mem_univ _)).elim
    simpa only [hx, if_true] using hsum
  · have hsum : (∑ o : Fin (Fintype.card I),
        if (Fintype.equivFin I).symm o ∈ A then
          (if Fintype.equivFin I x.1 = o then BornProb (Run O C ψ) x else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro o _
      by_cases he : Fintype.equivFin I x.1 = o
      · subst o
        simp [hx]
      · simp [he]
    simpa only [hx, if_false] using hsum

/-- Establishes the query-prefix observation, query-count, normalization, success-comparison,
and reconstruction guarantees in `InterruptedSearchAttempt` for the minimum-search setting
[DurrHoyer1996]. -/
theorem interruptedSearchAttempt : InterruptedSearchAttempt := by
  intro I _ _ hN A j r
  let O := BitOracleOn (fun x => decide (x ∈ A))
  let ψ : QState (I × Bool) := WithMinus (Uniform I)
  let C := LiftCircuit (SearchCircuit I j)
  let D := queryPrefix C r
  have hC : QueryCount C = j := by
    rw [queryCount_liftCircuit]
    exact (search_circuit_laws hN A j).1
  have hp : interruptedSearchPhaseAttempt A j r = observedOfCircuit D (searchPhaseObservation A) :=
    interruptObservedCircuit_eq_prefix C r _
  have hacc : observedAcceptance O (interruptedSearchPhaseAttempt A j r) ψ =
      MeasureProb (Run O D ψ) (A ×ˢ Finset.univ) := by rw [hp]; exact phaseCall_acceptance O D A ψ
  have hnorm : Normalized ψ := normalized_tensorState (normalized_uniform hN) normalized_minus
  have hO : O ∈ Matrix.unitaryGroup (I × Bool) ℂ := bitOracleOn_unitary _
  have hunit : IsUnitaryCircuit C :=
      (Qatlib.Concepts.SearchStopping.KnownCount.isUnitaryCircuit_groverCircuit hN j).lift
  have hDnorm : Normalized (Run O D ψ) :=
      normalized_run O hO D (queryPrefix_unitary C r hunit) hnorm
  have hfit (hjr : j ≤ r) : observedAcceptance O (interruptedSearchPhaseAttempt A j r) ψ =
      MeasureProb (SearchState A j) A := by
    rw [hacc, show D = C from queryPrefix_eq_self C r (by rw [hC]; exact hjr)]
    have h := (search_bit_oracle_compile_phase (fun x => decide (x ∈ A))
      (SearchCircuit I j) (Uniform I)).2.2 A
    simpa only [O, ψ, C, SearchState, Qatlib.Concepts.SearchStopping.KnownCount.GroverState,
        SetOracle] using h
  refine ⟨hacc, ?_, ?_, ?_, hfit, (interruptedCallLaws (I × Bool) O C ψ r).2.2.2.2⟩
  · intro t ht
    rw [hp, phaseCall_traces] at ht
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp ht
    change QueryCount D = min j r
    rw [queryPrefix_queryCount, hC]
  · rw [hp, phaseCall_traces]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, phaseTrace]
    rw [sum_measureProb_collapse_partition]
    exact measureProb_univ hDnorm
  · by_cases hjr : j ≤ r
    · rw [hfit hjr]
      exact sub_le_self _ (by positivity)
    · have hratio : 1 ≤ (j : ℝ) / (r + 1) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < r + 1)).mpr
        have hh : r + 1 ≤ j := by omega
        simpa only [one_mul] using (show (r : ℝ) + 1 ≤ (j : ℝ) by exact_mod_cast hh)
      have hfull := measureProb_le_one (search_circuit_laws hN A j).2.1 A
      have hnonneg := observedAcceptance_nonneg O (interruptedSearchPhaseAttempt A j r) ψ
      linarith

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
