/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryEffectiveDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
open Qatlib
open Qatlib
open Qatlib
open Qatlib

theorem lossTag_no_deletion {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) (hψ : Normalized ψ)
    (decode : LossDecode Y) :
    lossTagAnyAnswerMass O program ψ decode + lossTagLossMass O program ψ decode = 1 := by
  have hcompl : lossTagLossEvent decode
      = (fun t : BranchTrace I => !(lossTagAnyAnswerEvent decode t)) := by
    funext t
    exact lossTagLossEvent_eq_not_any decode t
  have h := observedEventMass_add_compl O hO program hprogram ψ (lossTagAnyAnswerEvent decode)
  simp only [lossTagAnyAnswerMass, lossTagLossMass]
  rw [hcompl]
  simpa only [branchMass, measureProb_univ hψ] using! h

theorem lossTag_loss_mass_le {I Y : Type} [Fintype I] [DecidableEq I] [DecidableEq Y]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) (hψ : Normalized ψ)
    (decode : LossDecode Y) (y : Y) (eps : ℝ)
    (hsuccess : 1 - eps ≤ lossTagSuccessMass O program ψ decode y) :
    lossTagLossMass O program ψ decode ≤ eps := by
  have hmono : lossTagSuccessMass O program ψ decode y
      ≤ lossTagAnyAnswerMass O program ψ decode :=
    observedEventMass_mono O program ψ (lossTagAnswerEvent decode y) (lossTagAnyAnswerEvent decode)
      (fun t _ ht => lossTagAnswerEvent_le_any decode y t ht)
  have htotal : lossTagAnyAnswerMass O program ψ decode
      + lossTagLossMass O program ψ decode = 1 :=
    lossTag_no_deletion O hO program hprogram ψ hψ decode
  linarith

theorem clause16_loss_tagged_endpoint
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (hP : observedWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → LossTagged Y)
    (ψ : QState ((Fin n × Fin q) × W)) (hψ : Normalized ψ)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1 - eps ≤ observedEventMass (phaseOracle (input x)) P ψ
      (fun t => decide (decode t.accepted t.outcomes = (.inl (f x) : LossTagged Y)))) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Gamma‖ ≤
      2 * (observedQueryDepth P : ℝ) * maxFilterNorm input Gamma := by
  refine phase_observed_query_lower_bound input (fun x => (.inl (f x) : LossTagged Y)) Gamma P hP
    decode ψ hψ eps he0 he1 hG ?_ hsuccess
  intro x y hxy
  exact hz x y (Sum.inl.inj hxy)

theorem instrumentLossTagLossEvent_eq_not_any {Y : Type} (decode : InstrumentLossDecode Y)
    (accepted : Bool) (outcomes : List (ℕ × ℕ)) :
    instrumentLossTagLossEvent decode accepted outcomes
      = ! instrumentLossTagAnyAnswerEvent decode accepted outcomes := by
  cases h : decode accepted outcomes <;>
    simp [instrumentLossTagLossEvent, instrumentLossTagAnyAnswerEvent, h]

theorem instrumentLossTagAnswerEvent_le_any {Y : Type} [DecidableEq Y]
    (decode : InstrumentLossDecode Y) (y : Y) (accepted : Bool) (outcomes : List (ℕ × ℕ))
    (h : instrumentLossTagAnswerEvent decode y accepted outcomes = true) :
    instrumentLossTagAnyAnswerEvent decode accepted outcomes = true := by
  cases hdec : decode accepted outcomes with
  | inl o =>
    simp [instrumentLossTagAnyAnswerEvent, hdec]
  | inr t =>
    simp [instrumentLossTagAnswerEvent, hdec] at h

private theorem instrumentEventMass_mono {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef)
    (E₁ E₂ : Bool → List (ℕ × ℕ) → Bool)
    (h : ∀ t ∈ instrumentCircuitMixedTraces O P rho,
      E₁ t.accepted t.outcomes = true → E₂ t.accepted t.outcomes = true) :
    instrumentCircuitEventMass O P rho E₁ ≤ instrumentCircuitEventMass O P rho E₂ := by
  have hm : ∀ t ∈ instrumentCircuitMixedTraces O P rho, 0 ≤ mixedMass t :=
    instrumentTraceMass_nonneg O P rho hrho
  unfold instrumentCircuitEventMass
  apply List.sum_le_sum
  intro t ht
  by_cases h1 : E₁ t.accepted t.outcomes = true
  · have h2 : E₂ t.accepted t.outcomes = true := h t ht h1
    simp only [if_pos h1, if_pos h2]
    exact le_rfl
  · by_cases h2 : E₂ t.accepted t.outcomes = true
    · simp only [if_neg h1, if_pos h2]
      exact hm t ht
    · simp only [if_neg h1, if_neg h2]
      exact le_rfl

private theorem sum_map_flatten {γ : Type} (l : List (List γ)) (g : γ → ℝ) :
    ((l.flatten).map g).sum = (l.map fun x => (x.map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hfl : List.flatten (x :: l) = x ++ List.flatten l := rfl
    rw [hfl, List.map_append, List.sum_append]
    simp only [List.map_cons, List.sum_cons]
    rw [ih]

private theorem instrument_ofFn_flatten_mass {d s : ℕ} (X : Fin s → List (MixedBranchTrace d))
    (g : MixedBranchTrace d → ℝ) :
    ((List.ofFn X).flatten.map g).sum = ∑ o : Fin s, ((X o).map g).sum := by
  have h1 : ((List.ofFn X).flatten.map g).sum
      = ((List.ofFn X).map fun x => (x.map g).sum).sum :=
    sum_map_flatten (List.ofFn X) g
  rw [h1]
  have h2 : ((List.ofFn X).map fun x => (x.map g).sum).sum
      = ∑ o : Fin s, ((X o).map g).sum := by
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  exact h2

private theorem instrument_gate_mass {d : ℕ} (O : Operator d) (G : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) :
    instrumentTotalMass O (.step (.gate G) P) rho
      = instrumentTotalMass O P (conjBranch G rho) := by
  unfold instrumentTotalMass
  have hmass : ∀ t : MixedBranchTrace d, mixedMass {t with gates := t.gates + 1} = mixedMass t := by
    intro t
    simp [mixedMass]
  simp only [instrumentCircuitEventMass, instrumentCircuitMixedTraces, List.map_map,
    Function.comp_def, if_true]
  rw [show (fun t : MixedBranchTrace d => mixedMass {t with gates := t.gates + 1}) = mixedMass
    from funext hmass]

private theorem instrument_query_mass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) :
    instrumentTotalMass O (.step .query P) rho
      = instrumentTotalMass O P (conjBranch O rho) := by
  unfold instrumentTotalMass
  have hmass : ∀ t : MixedBranchTrace d, mixedMass {t with queries := t.queries + 1} = mixedMass t := by
    intro t
    simp [mixedMass]
  simp only [instrumentCircuitEventMass, instrumentCircuitMixedTraces, List.map_map,
    Function.comp_def, if_true]
  rw [show (fun t : MixedBranchTrace d => mixedMass {t with queries := t.queries + 1}) = mixedMass
    from funext hmass]

private theorem instrument_instrument_mass {d s : ℕ} (O : Operator d) (I : Instrument (Fin s) d d)
    (next : Fin s → InstrumentCircuit d) (rho : Operator d) :
    instrumentTotalMass O (.instrument s I next) rho
      = ∑ o : Fin s, instrumentTotalMass O (next o) (I.branch o rho) := by
  unfold instrumentTotalMass
  have hmass : ∀ (o : Fin s) (t : MixedBranchTrace d), mixedMass {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, o.val) :: t.outcomes} = mixedMass t := by
    intro o t
    simp [mixedMass]
  simp only [instrumentCircuitEventMass, instrumentCircuitMixedTraces, if_true]
  have h1 : (List.map (fun t => mixedMass t) (List.ofFn fun o : Fin s => (instrumentCircuitMixedTraces O (next o) (I.branch o rho)).map fun t => {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, o.val) :: t.outcomes}).flatten).sum = ∑ o : Fin s, (((instrumentCircuitMixedTraces O (next o) (I.branch o rho)).map fun t => {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, o.val) :: t.outcomes}).map (fun t => mixedMass t)).sum :=
    instrument_ofFn_flatten_mass _ _
  rw [h1]
  rw [Finset.sum_congr rfl (fun o _ => ?_)]
  simp only [List.map_map, Function.comp_def]
  rw [show (fun t : MixedBranchTrace d => mixedMass {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, o.val) :: t.outcomes}) = mixedMass from funext (hmass o)]

theorem instrument_total_mass {d : ℕ} (O : Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (P : InstrumentCircuit d)
    (hP : instrumentCircuitWellFormed P) (rho : Operator d) :
    instrumentTotalMass O P rho = (Matrix.trace rho).re := by
  induction P generalizing rho with
  | halt b => simp [instrumentTotalMass, instrumentCircuitEventMass, instrumentCircuitMixedTraces,
      mixedMass]
  | step action P ih =>
    cases action with
    | gate G =>
      rw [instrument_gate_mass O G P rho, ih hP.2 (conjBranch G rho)]
      exact congrArg Complex.re (trace_conjBranch_unitary G hP.1 rho)
    | query =>
      rw [instrument_query_mass O P rho, ih hP (conjBranch O rho)]
      exact congrArg Complex.re (trace_conjBranch_unitary O hO rho)
  | instrument s I next ih =>
    rw [instrument_instrument_mass O I next rho]
    rw [Finset.sum_congr rfl (fun o _ => ih o (hP o) (I.branch o rho))]
    calc (∑ o : Fin s, (Matrix.trace (I.branch o rho)).re)
        = (∑ o : Fin s, Matrix.trace (I.branch o rho)).re := by rw [← Complex.re_sum]
      _ = (Matrix.trace (∑ o : Fin s, I.branch o rho)).re := by rw [Matrix.trace_sum]
      _ = (Matrix.trace rho).re := congrArg Complex.re (I.total rho)

private theorem instrumentEventMass_add {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (E₁ E₂ : Bool → List (ℕ × ℕ) → Bool)
    (h : ∀ t : MixedBranchTrace d,
      (if E₁ t.accepted t.outcomes then mixedMass t else 0)
        + (if E₂ t.accepted t.outcomes then mixedMass t else 0) = mixedMass t) :
    instrumentCircuitEventMass O P rho E₁ + instrumentCircuitEventMass O P rho E₂
      = instrumentCircuitEventMass O P rho (fun _ _ => true) := by
  unfold instrumentCircuitEventMass
  rw [← List.sum_map_add]
  have heq : (fun t : MixedBranchTrace d =>
      (if E₁ t.accepted t.outcomes then mixedMass t else 0)
        + (if E₂ t.accepted t.outcomes then mixedMass t else 0))
      = (fun t : MixedBranchTrace d => mixedMass t) := by
    funext t
    exact h t
  rw [heq]
  simp

theorem instrument_lossTag_no_deletion {d : ℕ} {Y : Type} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (decode : InstrumentLossDecode Y) :
    instrumentLossTagAnyAnswerMass O P rho decode + instrumentLossTagLossMass O P rho decode
      = instrumentTotalMass O P rho := by
  have hpoint : ∀ (t : MixedBranchTrace d),
      (if instrumentLossTagAnyAnswerEvent decode t.accepted t.outcomes then mixedMass t else 0)
        + (if instrumentLossTagLossEvent decode t.accepted t.outcomes then mixedMass t else 0)
          = mixedMass t := by
    intro t
    cases hdec : decode t.accepted t.outcomes with
    | inl o =>
      simp [instrumentLossTagAnyAnswerEvent, instrumentLossTagLossEvent, hdec]
    | inr t' =>
      simp [instrumentLossTagAnyAnswerEvent, instrumentLossTagLossEvent, hdec]
  have h := instrumentEventMass_add O P rho (instrumentLossTagAnyAnswerEvent decode)
    (instrumentLossTagLossEvent decode) hpoint
  simpa only [instrumentLossTagAnyAnswerMass, instrumentLossTagLossMass,
      instrumentTotalMass] using! h

theorem instrument_lossTag_loss_mass_le {d : ℕ} {Y : Type} (O : Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (P : InstrumentCircuit d)
    (hP : instrumentCircuitWellFormed P) (rho : Operator d) (hrho : IsDensityOperator rho)
    (decode : InstrumentLossDecode Y) (y : Y) (eps : ℝ)
    (hsuccess : 1 - eps ≤ instrumentLossTagSuccessMass O P rho decode y) :
    instrumentLossTagLossMass O P rho decode ≤ eps := by
  have hmono : instrumentLossTagSuccessMass O P rho decode y
      ≤ instrumentLossTagAnyAnswerMass O P rho decode := by
    refine instrumentEventMass_mono O P rho hrho.1 (instrumentLossTagAnswerEvent decode y)
      (instrumentLossTagAnyAnswerEvent decode) ?_
    intro t _ ht
    exact instrumentLossTagAnswerEvent_le_any decode y t.accepted t.outcomes ht
  have htotal : instrumentLossTagAnyAnswerMass O P rho decode
      + instrumentLossTagLossMass O P rho decode = (Matrix.trace rho).re := by
    rw [instrument_lossTag_no_deletion O P rho decode]
    exact instrument_total_mass O hO P hP rho
  have htrace : (Matrix.trace rho).re = 1 := by
    have htr := hrho.2
    simp [htr]
  linarith

theorem instrument_lossTag_loss_queries_le_expected {d : ℕ} {Y : Type} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (hrho : rho.PosSemidef)
    (decode : InstrumentLossDecode Y) :
    instrumentLossTagLossQueryCost O P rho decode ≤ instrumentCircuitExpectedQueries O P rho := by
  have hm : ∀ t ∈ instrumentCircuitMixedTraces O P rho, 0 ≤ mixedMass t :=
    instrumentTraceMass_nonneg O P rho hrho
  unfold instrumentLossTagLossQueryCost instrumentCircuitExpectedQueries
  apply List.sum_le_sum
  intro t ht
  by_cases h : instrumentLossTagLossEvent decode t.accepted t.outcomes
  · simp only [h, if_true]
    exact le_rfl
  · simp only [h]
    exact mul_nonneg (hm t ht) (Nat.cast_nonneg _)

theorem clause16_instrument_loss_tagged_endpoint
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {n q d : ℕ} [NeZero q] {W : Type} [Fintype W]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : InstrumentLossDecode Y)
    (ψ : QState (Fin d)) (hψ : Normalized ψ)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1 - eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P
        (outerProduct ψ) (fun b rec => decide (decode b rec = (.inl (f x) : LossTagged Y)))) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Gamma‖
      ≤ 2 * (instrumentCircuitQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  refine phase_instrument_query_lower_bound e input (fun x => (.inl (f x) : LossTagged Y))
    Gamma P hP decode ψ hψ eps he0 he1 hG ?_ hsuccess
  intro x y hxy
  exact hz x y (Sum.inl.inj hxy)

theorem clause21_instrument_truncation_loss_endpoint {d : ℕ} {Y : Type} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ) (hK : 0 < K)
    (decode : InstrumentLossDecode Y) :
    (instrumentQueryTailMass O P rho K ≤ instrumentCircuitExpectedQueries O P rho / (K : ℝ)) ∧
      (instrumentCircuitEventMass O P rho (instrumentLossTagAnyAnswerEvent decode)
          - instrumentCircuitExpectedQueries O P rho / (K + 1 : ℕ)
        ≤ instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho
          (instrumentLossTagAnyAnswerEvent decode)) ∧
      (instrumentCircuitWellFormed P →
        instrumentCircuitWellFormed (truncateInstrumentQueries P K)) := by
  refine ⟨instrumentQueryTail_le_expected O P rho hrho K hK, ?_, ?_⟩
  · exact instrument_event_sub_expected_le_truncate O P rho hrho K
      (instrumentLossTagAnyAnswerEvent decode)
  · intro hP
    exact truncateInstrumentQueries_legal P hP K

theorem clause21_truncation_conserves_weight {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (ψ : QState I) (hψ : Normalized ψ) (K : ℕ)
    (hPt : observedWellFormed (truncateObservedQueries P K)) :
    observedEventMass O (truncateObservedQueries P K) ψ (fun _ => true) = 1 := by
  have h := observedEventMass_true O hO (truncateObservedQueries P K) hPt ψ
  simpa only [branchMass, measureProb_univ hψ] using! h

theorem clause21_truncation_keeps_answers {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) (K : ℕ)
    (decode : LossDecode Y) :
    observedEventMass O P ψ (lossTagAnyAnswerEvent decode)
      - expectedObservedQueries O P ψ / (K + 1 : ℕ)
      ≤ observedEventMass O (truncateObservedQueries P K) ψ (lossTagAnyAnswerEvent decode) := by
  have h := observed_event_sub_expected_le_truncate O P ψ K
    (fun accepted outcomes => match decode accepted outcomes with
      | .inl _ => true
      | .inr _ => false)
  simpa only [lossTagAnyAnswerEvent] using! h

noncomputable def lossTagLossQueryCost {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) : ℝ :=
  (List.map (fun t =>
    if lossTagLossEvent decode t then branchMass t.state * (t.queries : ℝ) else 0)
    (observedTraces O P ψ)).sum

theorem lossTag_loss_queries_le_expected {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) (decode : LossDecode Y) :
    lossTagLossQueryCost O P ψ decode ≤ expectedObservedQueries O P ψ := by
  have hterm : ∀ (t : BranchTrace I),
      (if lossTagLossEvent decode t then branchMass t.state * (t.queries : ℝ) else 0)
        ≤ branchMass t.state * (t.queries : ℝ) := by
    intro t
    by_cases h : lossTagLossEvent decode t
    · simp only [h, if_true]
      exact le_rfl
    · simp only [h]
      exact mul_nonneg (branchMass_nonneg t.state) (Nat.cast_nonneg _)
  rw [expectedObservedQueries_eq_sum]
  unfold lossTagLossQueryCost
  exact List.sum_le_sum (fun t _ => hterm t)

theorem clause21_truncation_loss_endpoint {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (ψ : QState I) (hψ : Normalized ψ) (K : ℕ) (hK : 0 < K)
    (decode : LossDecode Y)
    (hPt : observedWellFormed (truncateObservedQueries P K)) :
    (observedEventMass O P ψ (fun t => decide (K ≤ t.queries))
        ≤ expectedObservedQueries O P ψ / (K : ℝ)) ∧
      (observedEventMass O (truncateObservedQueries P K) ψ (fun _ => true) = 1) ∧
      (observedEventMass O P ψ (lossTagAnyAnswerEvent decode)
          - expectedObservedQueries O P ψ / (K + 1 : ℕ)
        ≤ observedEventMass O (truncateObservedQueries P K) ψ (lossTagAnyAnswerEvent decode)) := by
  refine ⟨observedQueries_tail_le O P ψ hK,
    clause21_truncation_conserves_weight O hO P ψ hψ K hPt,
    clause21_truncation_keeps_answers O P ψ K decode⟩

theorem genAdvFilter_eq_genFilterDelta {X κ A : Type} [DecidableEq A]
    (input : X → κ → A) (Γ : Matrix X X ℂ) (i : κ) :
    genAdvFilter input Γ i = genFilterDelta input i ⊙ Γ := by
  ext x y
  by_cases h : input x i = input y i <;>
    simp [genAdvFilter, genFilterDelta, Matrix.hadamard_apply, h]

theorem genAdversaryValue_le_queryDelta {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) :
    genAdversaryValue input f ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (genFilterDelta input) := by
  unfold genAdversaryValue
  refine iSup_le fun Γ => ?_
  have hzero : gramFunctionEvaluationMatrix f ⊙ Γ.1 = Γ.1 := by
    ext x y
    by_cases h : f x = f y <;>
      simp [gramFunctionEvaluationMatrix, Matrix.hadamard_apply, h, Γ.2.2.1 x y]
  have h :=
      filteredGamma2_dual_ge (gramFunctionEvaluationMatrix f) (genFilterDelta input) Γ.1 Γ.2.2.2
  rw [hzero] at h
  exact h

theorem gen_witness_le_filteredGamma2 {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) (Γ : Matrix X X ℂ)
    (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hfilter : ∀ j, ‖genFilterDelta input j ⊙ Γ‖ ≤ 1) :
    ENNReal.ofReal ‖Γ‖ ≤ filteredGamma2 (gramFunctionEvaluationMatrix f) (genFilterDelta input) := by
  have hzero : gramFunctionEvaluationMatrix f ⊙ Γ = Γ := by
    ext x y
    by_cases h : f x = f y <;>
      simp [gramFunctionEvaluationMatrix, Matrix.hadamard_apply, h, hz x y]
  have h := filteredGamma2_dual_ge (gramFunctionEvaluationMatrix f) (genFilterDelta input) Γ hfilter
  rw [hzero] at h
  exact h

set_option linter.unusedVariables false in

theorem gen_degenerate_filter {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) (Γ : Matrix X X ℂ)
    (hm : maxFilterNorm input Γ = 0) :
    ∀ j, genAdvFilter input Γ j = 0 := by
  intro j
  have hj : ‖genAdvFilter input Γ j‖ = 0 := by
    have hle := Qatlib.Concepts.AdversaryBounds.AdvDuality.genAdvFilter_le_maxFilterNorm input Γ j
    rw [hm] at hle
    exact le_antisymm hle (by simp)
  exact norm_eq_zero.mp hj

theorem gen_degenerate_witness_value_top {X κ A : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ] [DecidableEq A]
    (input : X → κ → A) (Γ : Matrix X X ℂ) (hne : Γ ≠ 0)
    (hm : maxFilterNorm input Γ = 0) :
    advPmWitnessValue input Γ = ⊤ := by
  have hpos : ENNReal.ofReal ‖Γ‖ ≠ 0 := by
    intro h
    have hle : (‖Γ‖ : ℝ) ≤ 0 := (ENNReal.ofReal_eq_zero).mp h
    have hz : ‖Γ‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [norm_eq_zero] at hz
    exact hne hz
  have hz : ENNReal.ofReal (maxFilterNorm input Γ) = 0 := by
    rw [hm]
    simp
  unfold advPmWitnessValue
  rw [hz]
  rw [ENNReal.div_eq_top]
  exact Or.inl ⟨hpos, rfl⟩

theorem clause20_general_alphabet_bridge_endpoint {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) (Γ : Matrix X X ℂ) (hne : Γ ≠ 0)
    (hm : maxFilterNorm input Γ = 0) :
    (genAdversaryValue input f ≤
        filteredGamma2 (gramFunctionEvaluationMatrix f) (genFilterDelta input)) ∧
      (∀ j, genAdvFilter input Γ j = 0) ∧
      (advPmWitnessValue input Γ = ⊤) := by
  refine ⟨genAdversaryValue_le_queryDelta input f, gen_degenerate_filter input f Γ hm, ?_⟩
  exact gen_degenerate_witness_value_top input Γ hne hm

theorem cutWitness_hermitian {X : Type} [DecidableEq X] (x y : X) :
    (cutWitness x y).IsHermitian := by
  have hT : (cutWitness x y)ᵀ = cutWitness x y := by
    rw [cutWitness, Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single,
        add_comm]
  have hsym : ∀ i j : X, cutWitness x y j i = cutWitness x y i j := by
    intro i j
    have h := congrArg (fun M : Matrix X X ℂ => M i j) hT
    simpa [Matrix.transpose_apply] using! h
  ext i j
  simp [Matrix.conjTranspose_apply, cutWitness, Matrix.single, Matrix.add_apply, and_comm,
    add_comm]

theorem cutWitness_support {X E : Type} [DecidableEq X] {g : X → E} (x y : X)
    (hgy : g x ≠ g y) (x' y' : X) (h : g x' = g y') : cutWitness x y x' y' = 0 := by
  have h1 : ¬ (x = x' ∧ y = y') := by
    rintro ⟨rfl, rfl⟩
    exact hgy h
  have h2 : ¬ (y = x' ∧ x = y') := by
    rintro ⟨rfl, rfl⟩
    exact hgy h.symm
  simp [cutWitness, Matrix.single, Matrix.add_apply, h1, h2]

theorem cutWitness_ne_zero {X E : Type} [DecidableEq X] {g : X → E} (x y : X)
    (hgy : g x ≠ g y) : cutWitness x y ≠ 0 := by
  intro h
  have hxy : x ≠ y := fun hxy => hgy (hxy ▸ rfl)
  have hone : cutWitness x y x y = 1 := by
    simp [cutWitness, Matrix.single, Matrix.add_apply, hxy]
  have hz : cutWitness x y x y = 0 := by rw [h]; simp
  linarith

theorem cutWitness_norm_ge_one {X : Type} [Fintype X] [DecidableEq X] (x y : X) (hxy : x ≠ y) :
    1 ≤ ‖cutWitness x y‖ := by
  have hentry : ‖cutWitness x y x y‖ = 1 := by
    simp [cutWitness, Matrix.single, Matrix.add_apply, hxy]
  have hbound := gamma2_operator_entry_bound (cutWitness x y) x y
  rw [hentry] at hbound
  simpa using! hbound

theorem genAdvFilter_cutWitness {X κ A : Type} [DecidableEq X] [DecidableEq A]
    (input : X → κ → A) (x y : X) (j : κ) (hsep : input x j ≠ input y j) :
    genAdvFilter input (cutWitness x y) j = cutWitness x y := by
  ext i k
  by_cases hik : input i j ≠ input k j
  · simp [genAdvFilter, hik]
  · have hab : input i j = input k j := by
      by_contra hcon
      exact hik fun h => hcon h
    have h1 : ¬ (x = i ∧ y = k) := by
      rintro ⟨rfl, rfl⟩
      exact hsep hab
    have h2 : ¬ (y = i ∧ x = k) := by
      rintro ⟨rfl, rfl⟩
      exact hsep.symm hab
    simp [genAdvFilter, hik, cutWitness, Matrix.single, Matrix.add_apply, h1, h2]

theorem genAdvFilter_cutWitness_zero {X κ A : Type} [DecidableEq X] [DecidableEq A]
    (input : X → κ → A) (x y : X) (j : κ) (hsep : input x j = input y j) :
    genAdvFilter input (cutWitness x y) j = 0 := by
  ext u v
  by_cases huv : input u j ≠ input v j
  · have h1 : ¬ (x = u ∧ y = v) := by
      rintro ⟨rfl, rfl⟩
      exact (hsep ▸ huv) rfl
    have h2 : ¬ (y = u ∧ x = v) := by
      rintro ⟨rfl, rfl⟩
      exact (hsep ▸ huv.symm) rfl
    simp [genAdvFilter, huv, cutWitness, Matrix.single, Matrix.add_apply, h1, h2]
  · simp [genAdvFilter, huv]

theorem genAdvFilter_cutWitness_le {X κ A : Type} [Fintype X] [DecidableEq X] [DecidableEq A]
    (input : X → κ → A) (x y : X) (j : κ) :
    ‖genAdvFilter input (cutWitness x y) j‖ ≤ ‖cutWitness x y‖ := by
  by_cases h : input x j = input y j
  · rw [genAdvFilter_cutWitness_zero input x y j h]
    simp
  · rw [genAdvFilter_cutWitness input x y j h]

theorem maxFilterNorm_cutWitness_le {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] [Nonempty κ] (input : X → κ → A) (x y : X) :
    maxFilterNorm input (cutWitness x y) ≤ ‖cutWitness x y‖ := by
  unfold maxFilterNorm
  exact ciSup_le fun i => genAdvFilter_cutWitness_le input x y i

theorem cutWitness_certified_coordinate {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq κ] (input : X → κ → Bool) (β : κ → ℝ≥0∞) (x y : X) (j : κ)
    (hsep : input x j ≠ input y j) :
    β j ≤ β j * ENNReal.ofReal ‖cutWitness x y‖
      / ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖ := by
  have hxy : x ≠ y := fun h => hsep (h ▸ rfl)
  have hnorm : 1 ≤ ‖cutWitness x y‖ := cutWitness_norm_ge_one x y hxy
  have hfilter : ‖genAdvFilter input (cutWitness x y) j‖ ≤ ‖cutWitness x y‖ :=
    genAdvFilter_cutWitness_le input x y j
  have hA : 1 ≤ ENNReal.ofReal ‖cutWitness x y‖ := by
    simpa using! (ENNReal.ofReal_le_ofReal hnorm)
  have hApos : 0 < ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_pos.mpr (by
    have : (0 : ℝ) < ‖cutWitness x y‖ := lt_of_lt_of_le (by norm_num) hnorm
    exact this)
  have hB : ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖
      ≤ ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_le_ofReal hfilter
  have hfilterj : genAdvFilter input (cutWitness x y) j = cutWitness x y :=
    genAdvFilter_cutWitness input x y j hsep
  have hBpos : 0 < ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖ := by
    rw [hfilterj]
    exact ENNReal.ofReal_pos.mpr (by
      have : (0 : ℝ) < ‖cutWitness x y‖ := lt_of_lt_of_le (by norm_num) hnorm
      exact this)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hBpos))
    (Or.inl ENNReal.ofReal_ne_top)).2
  exact mul_le_mul_of_nonneg_left hB (bot_le)

theorem clause18_effective_cut_witness_endpoint {X Y κ A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype κ] [DecidableEq A] [Nonempty κ] (input : X → κ → A) (f : X → Y) (x y : X)
    (hgy : f x ≠ f y) (hsep : ∃ j, input x j ≠ input y j) :
    ENNReal.ofReal 1 ≤ advPmValue input f := by
  obtain ⟨j, hj⟩ := hsep
  have hxy : x ≠ y := fun h => hgy (h ▸ rfl)
  have hfilterj : genAdvFilter input (cutWitness x y) j = cutWitness x y :=
    genAdvFilter_cutWitness input x y j hj
  have hnormj : 1 ≤ ‖genAdvFilter input (cutWitness x y) j‖ := by
    rw [hfilterj]
    exact cutWitness_norm_ge_one x y hxy
  have hmaxpos : 0 < maxFilterNorm input (cutWitness x y) := by
    have hle : ‖genAdvFilter input (cutWitness x y) j‖
        ≤ maxFilterNorm input (cutWitness x y) :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.genAdvFilter_le_maxFilterNorm input (cutWitness x y) j
    have h1 : (1 : ℝ) ≤ maxFilterNorm input (cutWitness x y) := le_trans hnormj hle
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1
  have hmaxle : maxFilterNorm input (cutWitness x y) ≤ ‖cutWitness x y‖ :=
    maxFilterNorm_cutWitness_le input x y
  have hApos : 0 < ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_pos.mpr (by
    have : (0 : ℝ) < ‖cutWitness x y‖ := lt_of_lt_of_le (by norm_num)
        (cutWitness_norm_ge_one x y hxy)
    exact this)
  have hquot : 1 ≤ ENNReal.ofReal ‖cutWitness x y‖
      / ENNReal.ofReal (maxFilterNorm input (cutWitness x y)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inr (ne_of_gt hApos)) (Or.inl ENNReal.ofReal_ne_top)]
    have hle : ENNReal.ofReal (maxFilterNorm input (cutWitness x y))
        ≤ ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_le_ofReal hmaxle
    simpa using! hle
  have hvalue : ENNReal.ofReal 1 ≤ advPmWitnessValue input (cutWitness x y) := by
    unfold advPmWitnessValue
    simpa using! hquot
  have hadm : (cutWitness x y).IsHermitian
      ∧ (∀ x' y', f x' = f y' → cutWitness x y x' y' = 0)
      ∧ cutWitness x y ≠ 0 := by
    refine ⟨cutWitness_hermitian x y, ?_, cutWitness_ne_zero (g := f) x y hgy⟩
    intro x' y' h
    exact cutWitness_support x y hgy x' y' h
  unfold advPmValue
  exact le_trans hvalue
    (le_iSup (fun Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧
        (∀ x' y', f x' = f y' → Γ x' y' = 0) ∧ Γ ≠ 0} => advPmWitnessValue input Γ.1)
      ⟨cutWitness x y, hadm.1, hadm.2.1, hadm.2.2⟩)

theorem certifiedCutCost_le_of_separating {X κ A : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ] [DecidableEq A] (input : X → κ → A) (β : κ → ℝ≥0∞)
    (x y : X) (j : κ) (hsep : input x j ≠ input y j) :
    certifiedCutCost input β x y ≤ (β j).toReal := by
  have hj : j ∈ separatingCoords input x y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsep⟩
  unfold certifiedCutCost
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

theorem certifiedCutCost_attained {X κ A : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ] [DecidableEq A] (input : X → κ → A) (β : κ → ℝ≥0∞)
    (x y : X) (hsep : ∃ j, input x j ≠ input y j) :
    ∃ j, input x j ≠ input y j ∧ (β j).toReal = certifiedCutCost input β x y := by
  obtain ⟨j, hj⟩ := hsep
  have hmem : j ∈ separatingCoords input x y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hne : (separatingCoords input x y).Nonempty := ⟨j, hmem⟩
  obtain ⟨j', hj'mem, hjval⟩ := Finset.exists_mem_eq_inf'
    (s := separatingCoords input x y) hne (fun j : κ => (β j).toReal)
  refine ⟨j', Finset.mem_filter.mp hj'mem |>.2, ?_⟩
  unfold certifiedCutCost
  rw [dif_pos hne]
  exact hjval.symm

theorem effectiveCertifiedValue_attained {X E κ A : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ] [DecidableEq A]
    (input : X → κ → A) (g : X → E) (β : κ → ℝ≥0∞)
    (hcross : ∃ x y, g x ≠ g y) :
    ∃ x y, g x ≠ g y ∧ certifiedCutCost input β x y = effectiveCertifiedValue input g β := by
  obtain ⟨x, y, hxy⟩ := hcross
  have hmem : (x, y) ∈ crossOutputPairs g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
  have hne : (crossOutputPairs g).Nonempty := ⟨(x, y), hmem⟩
  obtain ⟨p, hp, hpval⟩ := Finset.exists_mem_eq_sup' (s := crossOutputPairs g) hne
    (fun p : X × X => certifiedCutCost input β p.1 p.2)
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  unfold effectiveCertifiedValue
  rw [dif_pos hne]
  exact hpval.symm

theorem effectiveCertifiedValue_ge_of_pair {X E κ A : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ] [DecidableEq A]
    (input : X → κ → A) (g : X → E) (β : κ → ℝ≥0∞) (x y : X) (hgy : g x ≠ g y) :
    certifiedCutCost input β x y ≤ effectiveCertifiedValue input g β := by
  have hmem : (x, y) ∈ crossOutputPairs g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgy⟩
  have hne : (crossOutputPairs g).Nonempty := ⟨(x, y), hmem⟩
  unfold effectiveCertifiedValue
  rw [dif_pos hne]
  exact Finset.le_sup' (fun p : X × X => certifiedCutCost input β p.1 p.2) hmem

theorem clause18_effective_certificate_cost_endpoint
    {X E κ A : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    [Fintype κ] [DecidableEq κ] [DecidableEq A] [Nonempty κ]
    (input : X → κ → A) (f : X → E) (β : κ → ℝ≥0∞)
    (x y : X) (hgy : f x ≠ f y) (hsep : ∃ j, input x j ≠ input y j) :
    (∃ j, input x j ≠ input y j ∧ (β j).toReal ≥ certifiedCutCost input β x y) ∧
      certifiedCutCost input β x y ≤ effectiveCertifiedValue input f β ∧
      ENNReal.ofReal 1 ≤ advPmValue input f := by
  obtain ⟨j, hj⟩ := hsep
  have hcost := certifiedCutCost_le_of_separating input β x y j hj
  refine ⟨⟨j, hj, hcost⟩, effectiveCertifiedValue_ge_of_pair input f β x y hgy, ?_⟩
  exact clause18_effective_cut_witness_endpoint input f x y hgy ⟨j, hj⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
