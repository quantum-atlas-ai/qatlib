/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceExecutionDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DisjointWorkspaceComposition
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportFreshCopy
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportImplBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceExecution

theorem stepAccount_queries_eq (s : DynStep) :
    s.stepAccount.queries = forwardOracleStep s := by
  match s with
  | .oracle false _ => rfl
  | .oracle true _ => rfl
  | .macro _ => rfl
  | .evolve _ => rfl
  | .classical _ => rfl
  | .alloc _ => rfl
  | .releaseClean _ => rfl
  | .releaseDirty _ => rfl
  | .reset _ => rfl
  | .uncompute _ => rfl

theorem stepAccount_adjointQueries_eq (s : DynStep) :
    s.stepAccount.adjointQueries = adjointOracleStep s := by
  match s with
  | .oracle false _ => rfl
  | .oracle true _ => rfl
  | .macro _ => rfl
  | .evolve _ => rfl
  | .classical _ => rfl
  | .alloc _ => rfl
  | .releaseClean _ => rfl
  | .releaseDirty _ => rfl
  | .reset _ => rfl
  | .uncompute _ => rfl

theorem stepAccount_hamiltonianCount_eq (s : DynStep) :
    s.stepAccount.hamiltonianCount = evolveStep s := by
  match s with
  | .oracle false _ => rfl
  | .oracle true _ => rfl
  | .macro _ => rfl
  | .evolve _ => rfl
  | .classical _ => rfl
  | .alloc _ => rfl
  | .releaseClean _ => rfl
  | .releaseDirty _ => rfl
  | .reset _ => rfl
  | .uncompute _ => rfl

theorem counters_queries (ops : List DynStep) :
    (counters ops).queries = forwardOracleCount ops := by
  induction ops with
  | nil => rfl
  | cons s rest ih =>
      rw [counters_cons, seq_queries, ih, stepAccount_queries_eq]
      rfl

theorem counters_adjointQueries (ops : List DynStep) :
    (counters ops).adjointQueries = adjointOracleCount ops := by
  induction ops with
  | nil => rfl
  | cons s rest ih =>
      rw [counters_cons, seq_adjointQueries, ih, stepAccount_adjointQueries_eq]
      rfl

theorem counters_hamiltonianCount (ops : List DynStep) :
    (counters ops).hamiltonianCount = evolveCount ops := by
  induction ops with
  | nil => rfl
  | cons s rest ih =>
      rw [counters_cons, seq_hamiltonianCount, ih, stepAccount_hamiltonianCount_eq]
      rfl

theorem account_queries_count (base : ℕ) (ops : List DynStep) :
    (account base ops).queries = forwardOracleCount ops := by
  rw [account_queries, counters_queries]

theorem account_adjointQueries_count (base : ℕ) (ops : List DynStep) :
    (account base ops).adjointQueries = adjointOracleCount ops := by
  rw [account_adjointQueries, counters_adjointQueries]

theorem account_hamiltonianCount_count (base : ℕ) (ops : List DynStep) :
    (account base ops).hamiltonianCount = evolveCount ops := by
  rw [account_hamiltonianCount, counters_hamiltonianCount]

theorem unifiedCounts_of_account (base : ℕ) (ops : List DynStep) :
    UnifiedCounts.ofAccount (account base ops) =
      ⟨forwardOracleCount ops, adjointOracleCount ops, evolveCount ops⟩ := by
  simp only [UnifiedCounts.ofAccount, account_queries_count, account_adjointQueries_count,
    account_hamiltonianCount_count]

theorem unifiedCounts_total_count (base : ℕ) (ops : List DynStep) :
    (UnifiedCounts.ofAccount (account base ops)).total =
      forwardOracleCount ops + adjointOracleCount ops := by
  simp only [UnifiedCounts.total, UnifiedCounts.ofAccount, account_queries_count,
    account_adjointQueries_count]

theorem program_queries_count {Out : Type*} (P : Program Out) :
    P.account.queries = forwardOracleCount P.word := by
  exact account_queries_count P.base P.word

theorem localCopy_localGates_same_execution {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (localCopyQPEProgramResources n s C)).localGates =
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).localGates := by
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g3 n M s ρ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)
    (copyQPEInput (2 ^ n) M ρ)
  simp only [FreshLedger.local]
  rw [← hr]
  exact hg.2.2.1.symm

theorem numericCopy_localGates_same_execution {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (numericCopyResources n b C)).localGates =
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).localGates := by
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g4 n M b k ρ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)
    (copyQPEInput (2 ^ n) M ρ)
  simp only [FreshLedger.local]
  rw [← hr]
  exact hg.2.2.1.symm

def SameRunFull (l : FreshLedger) (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : Prop :=
  l.copies = c.copies ∧ l.partialSwaps = c.partialSwaps ∧
    l.localGates = c.localGates ∧ l.discards = c.discards ∧
    l.bitQueries = c.bitQueries

def SameRunLocal (l : FreshLedger) (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : Prop :=
  l.copies = c.copies ∧ l.localGates = c.localGates ∧
    l.discards = c.discards ∧ l.bitQueries = c.bitQueries

theorem quadruple_eq_components {q : ℕ × ℕ × ℕ × ℕ} {c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost}
    (h : q = (c.copies, c.partialSwaps, c.discards, c.bitQueries)) :
    q.1 = c.copies ∧ q.2.1 = c.partialSwaps ∧ q.2.2.1 = c.discards ∧
      q.2.2.2 = c.bitQueries :=
  ⟨congrArg Prod.fst h, congrArg (fun t => t.2.1) h, congrArg (fun t => t.2.2.1) h,
    congrArg (fun t => t.2.2.2) h⟩

theorem copyDriven_full_same_execution {n M : ℕ} (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    SameRunFull (FreshLedger.copyDriven (copyQPEProgramResources n C))
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)) := by
  have h4 := copyDriven_same_execution ρ C
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g2 n M n ρ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)
    (copyQPEInput (2 ^ n) M ρ)
  have hlg : (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).localGates = 0 := by
    rw [← hr, hg.2.1]
  obtain ⟨hc, hps, hd, hb⟩ := quadruple_eq_components h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [FreshLedger.copyDriven]
    exact hc
  · simp only [FreshLedger.copyDriven]
    exact hps
  · simp only [FreshLedger.copyDriven]
    exact hlg.symm
  · simp only [FreshLedger.copyDriven]
    exact hd
  · simp only [FreshLedger.copyDriven]
    exact hb

theorem localCopy_full_same_execution {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    SameRunLocal (FreshLedger.local (localCopyQPEProgramResources n s C))
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)) := by
  have h3 := localCopy_same_execution s ρ C
  refine ⟨h3.1, localCopy_localGates_same_execution s ρ C, h3.2.1, h3.2.2⟩

theorem numericCopy_full_same_execution {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    SameRunLocal (FreshLedger.local (numericCopyResources n b C))
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)) := by
  have h3 := numericCopy_same_execution b k ρ C
  refine ⟨h3.1, numericCopy_localGates_same_execution b k ρ C, h3.2.1, h3.2.2⟩

theorem twoSpecies_full_same_execution {n M : ℕ} (ρ σ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    SameRunFull (FreshLedger.twoSpecies (copyQPEProgramResources (2 * n) C))
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)) := by
  have h4 := twoSpecies_same_execution ρ σ C
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g5 n M n ρ σ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)
    (copyQPEInput (2 ^ n) M ρ)
  have hlg : (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).localGates = 0 := by
    rw [← hr, hg.2.1]
  obtain ⟨hc, hps, hd, hb⟩ := quadruple_eq_components h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [FreshLedger.twoSpecies]
    exact hc
  · simp only [FreshLedger.twoSpecies]
    exact hps
  · simp only [FreshLedger.twoSpecies]
    exact hlg.symm
  · simp only [FreshLedger.twoSpecies]
    exact hd
  · simp only [FreshLedger.twoSpecies]
    exact hb

theorem plainComposition_full_same_execution (D : ℕ) (ρ : Operator D) (angles : List ℝ)
    (X : Operator D) :
    SameRunFull (FreshLedger.plainComposition (freshCopyResourceCounts D angles))
      ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2) := by
  have h4 := plainComposition_same_execution D ρ angles X
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g6.1 D ρ X angles
  have hlg : ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2).localGates
      = 0 := by
    rw [hg.2.1]
  obtain ⟨hc, hps, hd, hb⟩ := quadruple_eq_components h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [FreshLedger.plainComposition]
    exact hc
  · simp only [FreshLedger.plainComposition]
    exact hps
  · simp only [FreshLedger.plainComposition]
    exact hlg.symm
  · simp only [FreshLedger.plainComposition]
    exact hd
  · simp only [FreshLedger.plainComposition]
    exact hb

theorem localCopy_partialSwaps_position_absent {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (localCopyQPEProgramResources n s C)).partialSwaps = 0 ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).partialSwaps
        = s * QueryCount C := by
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g3 n M s ρ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)
    (copyQPEInput (2 ^ n) M ρ)
  constructor
  · rfl
  · rw [← hr, hg.2.1]
    exact Nat.mul_comm _ _

theorem numericCopy_partialSwaps_position_absent {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (numericCopyResources n b C)).partialSwaps = 0 ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).partialSwaps
        = 2 ^ b * QueryCount C := by
  have hg := Qatlib.Concepts.FreshCopyExec.QpeConsumers.g4 n M b k ρ C (copyQPEInput (2 ^ n) M ρ)
  have hr := fresh_run_cost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)
    (copyQPEInput (2 ^ n) M ρ)
  constructor
  · rfl
  · rw [← hr, hg.2.1]
    exact Nat.mul_comm _ _

theorem workOf_account (base : ℕ) (ops : List DynStep) :
    workOf (account base ops) = workOf (counters ops) := by
  simp only [workOf, WorkLedger.mk.injEq]
  exact ⟨account_queries base ops, account_adjointQueries base ops,
    account_hamiltonianCount base ops, account_macroGates base ops,
    account_basicGates base ops, account_depth base ops, account_classicalBits base ops,
    account_hamiltonianTicks base ops⟩

theorem account_work_append (base : ℕ) (a b : List DynStep) :
    workOf (account base (a ++ b)) =
      (workOf (account base a)).add (workOf (account base b)) := by
  rw [workOf_account, counters_append, Account.seq_work, workOf_account, workOf_account]

theorem stepAccount_shiftStepWires (k : ℕ) (s : DynStep) :
    (shiftStepWires k s).stepAccount = s.stepAccount := by
  match s with
  | .oracle adj ws => cases adj <;> rfl
  | .macro _ => rfl
  | .evolve _ => rfl
  | .classical _ => rfl
  | .alloc _ => rfl
  | .releaseClean _ => rfl
  | .releaseDirty _ => rfl
  | .reset _ => rfl
  | .uncompute _ => rfl

theorem counters_shiftMap (k : ℕ) (b : List DynStep) :
    (counters (List.map (shiftStepWires k) b)).queries = (counters b).queries ∧
      (counters (List.map (shiftStepWires k) b)).adjointQueries =
        (counters b).adjointQueries ∧
      (counters (List.map (shiftStepWires k) b)).hamiltonianCount =
        (counters b).hamiltonianCount ∧
      (counters (List.map (shiftStepWires k) b)).macroGates = (counters b).macroGates ∧
      (counters (List.map (shiftStepWires k) b)).basicGates = (counters b).basicGates ∧
      (counters (List.map (shiftStepWires k) b)).depth = (counters b).depth ∧
      (counters (List.map (shiftStepWires k) b)).classicalBits = (counters b).classicalBits ∧
      (counters (List.map (shiftStepWires k) b)).hamiltonianTicks =
        (counters b).hamiltonianTicks := by
  induction b with
  | nil => simp
  | cons s rest ih =>
      simp only [List.map_cons, counters_cons]
      rw [stepAccount_shiftStepWires]
      simp only [seq_queries, seq_adjointQueries, seq_hamiltonianCount, seq_macroGates,
        seq_basicGates, seq_depth, seq_classicalBits, seq_hamiltonianTicks]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih
      simp [h1, h2, h3, h4, h5, h6, h7, h8]

theorem workOf_shiftWord (base : ℕ) (k : ℕ) (b : List DynStep) :
    workOf (account base (shiftWord k b)) = workOf (account base b) := by
  rw [workOf_account, workOf_account]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := counters_shiftMap k b
  simp only [workOf, WorkLedger.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem account_work_merge (base : ℕ) (a b : List DynStep) :
    workOf (account base (mergeWords a b)) =
      (workOf (account base a)).add (workOf (account base b)) := by
  rw [mergeWords, account_work_append, workOf_shiftWord]

theorem account_work_repeat (base : ℕ) (s : List DynStep) (k : ℕ) :
    workOf (account base (repeatWord s k)) = (workOf (account base s)).smul k := by
  rw [workOf_account, counters_repeatWord, workOf_repeat, workOf_account]

theorem maxTrail_repeat_balanced (base : ℕ) (s : List DynStep) (k : ℕ)
    (h : balanced base s) :
    maxTrail (liveTrail (List.range base) (repeatWord s (k + 1))) =
      maxTrail (liveTrail (List.range base) s) := by
  induction k with
  | zero =>
      have h1 : repeatWord s 1 = s ++ [] := by
        simp [Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.repeatWord]
      rw [h1, liveTrail_append, maxTrail_append]
      simp only [maxTrail, liveTrail]
      exact Nat.max_eq_left (Nat.zero_le _)
  | succ k ih =>
      have h1 : repeatWord s (Nat.succ (Nat.succ k)) = s ++ repeatWord s (Nat.succ k) := by
        simp [Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.repeatWord]
      have h2 : liveAfter (List.range base) s = List.range base := by
        rw [liveAfter_range_base]
        exact h
      rw [h1, liveTrail_append, h2, maxTrail_append, ih]
      exact Nat.max_eq_left (Nat.le_refl _)

theorem account_peak_repeat_balanced (base : ℕ) (s : List DynStep) (k : ℕ)
    (h : balanced base s) :
    (account base (repeatWord s (k + 1))).livePeak = (account base s).livePeak := by
  rw [account_livePeak_formula, account_livePeak_formula,
    maxTrail_repeat_balanced base s k h]

theorem step_profile_peakWorkspace_is_run_quantity (base : ℕ) (w : ℕ) :
    (profileOf (DynStep.alloc w)).space = 0 ∧
      (account base [DynStep.alloc w]).peakWorkspace = 1 := by
  constructor
  · simp [profileOf, DynStep.stepAccount, Account.zero]
  · rw [account_peakWorkspace_formula]
    simp [wsTrail, applyLive, maxTrail]

def executedProfile (base : ℕ) (s : DynStep) : StepProfile :=
  ⟨(account base [s]).basicGates, (account base [s]).peakWorkspace,
    (account base [s]).toResourceCost.hamiltonianTime, (account base [s]).classicalBits⟩

theorem executedProfile_verified (base : ℕ) (s : DynStep) :
    (executedProfile base s).basicGates = (profileOf s).basicGates ∧
      (executedProfile base s).classicalBits = (profileOf s).classicalBits ∧
      (executedProfile base s).evolve = (profileOf s).evolve ∧
      (executedProfile base s).space = (account base [s]).peakWorkspace := by
  obtain ⟨h1, h2⟩ := profileOf_execution_verified base s
  have h3 : (account base [s]).hamiltonianTicks = s.stepAccount.hamiltonianTicks := by
    rw [account_hamiltonianTicks, counters_cons, seq_hamiltonianTicks, counters_nil]
    simp [Account.zero]
  refine ⟨h1.symm, h2.symm, ?_, rfl⟩
  simp only [executedProfile, profileOf, Account.toResourceCost]
  rw [h3]

theorem freshRunAccount_ledgers {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M))
    (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M) :
    (freshRunAccount ops X).queries = (freshRunCost ops X).bitQueries ∧
      (freshRunAccount ops X).adjointQueries = 0 ∧
      (freshRunAccount ops X).hamiltonianCount = 0 ∧
      (freshRunAccount ops X).macroGates = (freshRunCost ops X).fixedMacros ∧
      (freshRunAccount ops X).basicGates = (freshRunCost ops X).localGates ∧
      (freshRunAccount ops X).depth = (freshRunCost ops X).copies +
        (freshRunCost ops X).partialSwaps + (freshRunCost ops X).localGates +
        (freshRunCost ops X).fixedMacros + (freshRunCost ops X).discards +
        (freshRunCost ops X).bitQueries ∧
      (freshRunAccount ops X).livePeak =
        max (freshRunCost ops X).peakFreshRegisters (freshRunCost ops X).peakCleanQubits ∧
      (freshRunAccount ops X).peakWorkspace = (freshRunCost ops X).peakFreshRegisters +
        (freshRunCost ops X).peakCleanQubits ∧
      (freshRunAccount ops X).classicalBits = (freshRunCost ops X).discards := by
  simp [freshRunAccount, freshRunCost, Account.ofFreshCost]

theorem program_account_determined {Out : Type*} (P Q : Program Out)
    (hw : P.word = Q.word) (hb : P.base = Q.base) : P.account = Q.account := by
  unfold Program.account
  rw [hw, hb]

theorem program_outcome_same_run {Out : Type*} (P : Program Out) :
    P.outcome = .done (P.readout (finalLive P.base P.word), account P.base P.word) := rfl

theorem emptyProgram_no_cost {Out : Type*} (P : Program Out) (h : P.word = []) :
    P.account.queries = 0 ∧ P.account.adjointQueries = 0 ∧
      P.account.hamiltonianCount = 0 ∧ P.account.basicGates = 0 ∧
      P.account.macroGates = 0 ∧ P.account.depth = 0 := by
  rw [Program.account, h, account_nil]
  simp [Account.initAccount, Account.zero]

theorem constantProgram_not_implements {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account)
    (P : Program Out) (hconst : ∀ L : List ℕ, P.readout L = P.readout [])
    (hnt : T.nontrivial) :
    ¬ Implements T (Program.gen P) B := by
  intro h
  have h' : Implements T (fun _ => (.done (P.readout [], P.account) : Outcome (Out × Account))) B := by
    intro i hi
    obtain ⟨o, acc, ho, hok, hle⟩ := h i hi
    have ho2 : Program.gen P i = .done (P.readout [], P.account) := by
      simp only [Program.gen, Program.outcome]
      rw [hconst _]
    rw [ho2] at ho
    refine ⟨o, acc, ho, hok, hle⟩
  exact constant_not_implements T B (P.readout []) (fun _ => P.account) hnt h'

theorem forwardOracleCount_circuitResourceWord {I : Type} (C : Circuit I) :
    forwardOracleCount (C.map circuitResourceStep) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, forwardOracleCount, forwardOracleStep, ih]
          simp only [QueryCount]
          omega
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, forwardOracleCount, forwardOracleStep, ih]
          simp only [QueryCount]
          omega

theorem forwardOracleCount_append (a b : List DynStep) :
    forwardOracleCount (a ++ b) = forwardOracleCount a + forwardOracleCount b := by
  induction a with
  | nil => rw [List.nil_append, forwardOracleCount]; omega
  | cons s a ih =>
      rw [List.cons_append, forwardOracleCount, ih, forwardOracleCount]
      ring

theorem forwardOracleCount_circuitResourceWord' {I : Type} (C : Circuit I) (w : ℕ) :
    forwardOracleCount (circuitResourceWord C w) = QueryCount C := by
  have hmap : ∀ (c : Circuit I),
      forwardOracleCount (c.map circuitResourceStep) = QueryCount c := by
    intro c
    induction c with
    | nil => rfl
    | cons a c ih =>
        cases a with
        | query =>
            show forwardOracleStep (DynStep.oracle false []) +
                forwardOracleCount (c.map circuitResourceStep) = _
            rw [forwardOracleStep, ih]
            simp only [QueryCount]
            omega
        | gate U =>
            show forwardOracleStep (DynStep.macro (.h 0)) +
                forwardOracleCount (c.map circuitResourceStep) = _
            rw [forwardOracleStep, ih]
            simp only [QueryCount]
            omega
  have hexp : circuitResourceWord C w
      = DynStep.alloc w :: (C.map circuitResourceStep ++ [DynStep.releaseClean w]) := rfl
  rw [hexp]
  rw [forwardOracleCount, forwardOracleStep, forwardOracleCount_append]
  rw [hmap C]
  rw [forwardOracleCount, forwardOracleStep]
  have hnil : forwardOracleCount [] = 0 := rfl
  rw [hnil]
  omega

theorem counters_classicalBits_circuit {I : Type} (C : Circuit I) :
    (counters (C.map circuitResourceStep)).classicalBits = 0 := by
  induction C with
  | nil => simp [counters, Account.zero]
  | cons a C ih =>
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, counters_cons, seq_classicalBits]
          have h1 : (DynStep.oracle false []).stepAccount.classicalBits = 0 := rfl
          rw [h1, ih]
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, counters_cons, seq_classicalBits]
          have h1 : (DynStep.macro (.h 0)).stepAccount.classicalBits = 0 := rfl
          rw [h1, ih]

theorem counters_depth_circuit {I : Type} (C : Circuit I) :
    (counters (C.map circuitResourceStep)).depth = C.length := by
  induction C with
  | nil => simp [counters, Account.zero]
  | cons a C ih =>
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, counters_cons, seq_depth]
          have h1 : (DynStep.oracle false []).stepAccount.depth = 1 := rfl
          rw [h1, ih]
          simp only [List.length_cons]
          omega
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, counters_cons, seq_depth]
          have h1 : (DynStep.macro (.h 0)).stepAccount.depth = 1 := rfl
          rw [h1, ih]
          simp only [List.length_cons]
          omega

theorem counters_basicGates_circuit {I : Type} (C : Circuit I) :
    (counters (C.map circuitResourceStep)).basicGates = GateCount C := by
  induction C with
  | nil => simp [counters, Account.zero]
  | cons a C ih =>
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, counters_cons, seq_basicGates]
          have h1 : (DynStep.oracle false []).stepAccount.basicGates = 0 := rfl
          rw [h1, ih]
          simp only [GateCount]
          omega
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, counters_cons, seq_basicGates]
          have h1 : (DynStep.macro (.h 0)).stepAccount.basicGates = 1 := rfl
          rw [h1, ih]
          simp only [GateCount]
          omega

theorem liveAfter_circuitSteps {I : Type} : ∀ (C : Circuit I) (live : List ℕ),
    liveAfter live (C.map circuitResourceStep) = live := by
  intro C
  induction C with
  | nil => intro live; rfl
  | cons a C ih =>
      intro live
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap]
          show liveAfter (applyLive live (DynStep.oracle false []))
            (C.map circuitResourceStep) = live
          rw [ih]
          rfl
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap]
          show liveAfter (applyLive live (DynStep.macro (.h 0)))
            (C.map circuitResourceStep) = live
          rw [ih]
          rfl

theorem liveTrail_circuitSteps {I : Type} : ∀ (C : Circuit I) (live : List ℕ),
    liveTrail live (C.map circuitResourceStep) = List.replicate C.length live.length := by
  intro C
  induction C with
  | nil => intro live; rfl
  | cons a C ih =>
      intro live
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, liveTrail]
          rw [ih]
          rfl
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, liveTrail]
          rw [ih]
          rfl

theorem wsTrail_circuitSteps {I : Type} : ∀ (C : Circuit I) (live : List ℕ),
    wsTrail 0 live (C.map circuitResourceStep) = List.replicate C.length (live.length - 0) := by
  intro C
  induction C with
  | nil => intro live; rfl
  | cons a C ih =>
      intro live
      cases a with
      | query =>
          have hmap : circuitResourceStep (.query : Step I) = DynStep.oracle false [] := rfl
          rw [List.map_cons, hmap, wsTrail]
          rw [ih]
          rfl
      | gate U =>
          have hmap : circuitResourceStep (.gate U) = DynStep.macro (.h 0) := rfl
          rw [List.map_cons, hmap, wsTrail]
          rw [ih]
          rfl

theorem liveTrail_circuitResourceWord {I : Type} (C : Circuit I) :
    liveTrail [] (circuitResourceWord C 0) = 1 :: (List.replicate C.length 1 ++ [0]) := by
  have hexp : circuitResourceWord C 0
      = DynStep.alloc 0 :: (C.map circuitResourceStep ++ [DynStep.releaseClean 0]) := rfl
  rw [hexp]
  simp only [liveTrail]
  rw [liveTrail_append]
  rw [liveTrail_circuitSteps]
  rw [liveAfter_circuitSteps]
  rfl

theorem grover_actual_resources {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) :
    (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).queries
        = QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).livePeak = 1 ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).peakWorkspace = 1 ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).classicalBits = 3 ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).basicGates
        = GateCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) ∧
      (Account.ofCircuit
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))).livePeak = 0 ∧
      (Account.ofCircuit
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))).classicalBits = 0 := by
  have hq : (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).queries
      = QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) := by
    rw [account_queries_count]
    exact forwardOracleCount_circuitResourceWord'
      (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0
  have hbits : (counters (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).classicalBits = 3 := by
    simp only [circuitResourceWord, counters_cons, seq_classicalBits, counters_append,
      seq_classicalBits]
    have h1 : (DynStep.alloc 0).stepAccount.classicalBits = 1 := rfl
    have h2 : (DynStep.releaseClean 0).stepAccount.classicalBits = 2 := rfl
    rw [h1, h2, counters_classicalBits_circuit, counters_nil]
    simp [Account.zero]
  have hbg : (counters (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).basicGates
      = GateCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) := by
    simp only [circuitResourceWord, counters_cons, seq_basicGates, counters_append,
      seq_basicGates]
    have h1 : (DynStep.alloc 0).stepAccount.basicGates = 0 := rfl
    have h2 : (DynStep.releaseClean 0).stepAccount.basicGates = 0 := rfl
    rw [h1, h2, counters_basicGates_circuit, counters_nil]
    simp [Account.zero]
  have hws : wsTrail 0 [] (circuitResourceWord
      (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)
      = 1 :: (List.replicate (workspaceGroverCircuit (W := W) n
        (singletonSearchIterations n)).length 1 ++ [0]) := by
    have hexp : circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0
        = DynStep.alloc 0 :: ((workspaceGroverCircuit (W := W) n
            (singletonSearchIterations n)).map circuitResourceStep ++
            [DynStep.releaseClean 0]) := rfl
    rw [hexp]
    simp only [wsTrail]
    rw [wsTrail_append]
    rw [wsTrail_circuitSteps]
    rw [liveAfter_circuitSteps]
    rfl
  refine ⟨hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [account_livePeak_formula]
    have hz : List.range 0 = [] := by rfl
    rw [hz, liveTrail_circuitResourceWord]
    simp only [maxTrail_cons]
    rw [maxTrail_append, maxTrail_replicate]
    by_cases hn : (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)).length = 0
    · simp [hn, maxTrail]
    · simp [hn, maxTrail]
  · rw [account_peakWorkspace_formula]
    have hz : List.range 0 = [] := by rfl
    rw [hz, hws]
    simp only [maxTrail_cons]
    rw [maxTrail_append, maxTrail_replicate]
    by_cases hn : (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)).length = 0
    · simp [hn, maxTrail]
    · simp [hn, maxTrail]
  · rw [account_classicalBits, hbits]
  · rw [account_basicGates, hbg]
  · rfl
  · rfl

theorem search_same_execution_born_and_resources {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (hn : 2 ≤ n) (x : Reg n) :
    MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
        (Ket ((ZeroStr n, false), w)))
      (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ) ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).queries
        = QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) ∧
      (account 0 (circuitResourceWord
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).livePeak = 1 := by
  obtain ⟨hq, hp, _, _, _, _, _⟩ := grover_actual_resources (W := W) n
  exact ⟨search_born_mass n W w hn x, hq, hp⟩

theorem parityIndicator_onehot : parityIndicator (fun i : Fin 2 => decide (i = 0)) = 1 := by
  have hcard : (Finset.univ.filter (fun i : Fin 2 => decide (i = 0) = true)).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨0, ?_⟩
    ext x
    simp [Finset.mem_filter]
  simp only [parityIndicator]
  rw [hcard]
  rfl

theorem parityIndicator_allfalse : parityIndicator (fun _ : Fin 2 => false) = 0 := by
  have hcard : (Finset.univ.filter (fun _ : Fin 2 => false = true)).card = 0 := by
    have hset : Finset.univ.filter (fun _ : Fin 2 => false = true) = ∅ := by
      ext x
      simp
    rw [hset]
    simp
  simp only [parityIndicator]
  rw [hcard]
  rfl

theorem parity_lower_bound_nonConstant (W : Type) [Fintype W] [DecidableEq W] :
    QueryLower (parityGen : ParityProgram (Fin 2) W → Gen ((Fin 2) → Bool) ℝ)
      (parityTask (Fin 2)) (fun _ => Fintype.card (Fin 2) / 2) 1 ∧
      parityIndicator (fun i : Fin 2 => decide (i = 0)) = 1 ∧
      parityIndicator (fun _ : Fin 2 => false) = 0 ∧
      (parityTask (Fin 2)).legal (fun i : Fin 2 => decide (i = 0)) := by
  refine ⟨parity_lower_bound_consumer (I := Fin 2) W, parityIndicator_onehot,
    parityIndicator_allfalse, ?_⟩
  trivial

theorem joint_bigO {f g : ℕ → ℝ → ℝ} (c : ℝ) (hc : 0 ≤ c) (n0 : ℕ) (E0 : ℝ)
    (h : ∀ n E, n0 ≤ n → E0 ≤ E →
      0 ≤ f n E ∧ 0 ≤ g n E ∧ f n E ≤ c * g n E) :
    BigO jointFilter (fun p => f p.1 p.2) (fun p => g p.1 p.2) := by
  refine ⟨c, hc, ?_⟩
  simp only [BigOWith, jointFilter]
  rw [Filter.eventually_prod_iff]
  refine ⟨fun n => n0 ≤ n, ?_, fun E => E0 ≤ E, ?_, ?_⟩
  · exact (Filter.eventually_atTop (p := fun n : ℕ => n0 ≤ n)).mpr
      ⟨n0, fun b hb => hb⟩
  · exact (Filter.eventually_atTop (p := fun E : ℝ => E0 ≤ E)).mpr
      ⟨E0, fun b hb => hb⟩
  · intro x hx y hy
    obtain ⟨h1, h2, h3⟩ := h x y hx hy
    simp only [abs_of_nonneg h1, abs_of_nonneg h2]
    exact h3

theorem jointFilter_is_product : jointFilter = sizeFilter ×ˢ precFilter := rfl

theorem certifiedGateBudget_bigO {n k c : ℕ} (cert : ℝ → SynthCertificate n)
    (hlen : ∀ E : ℝ, 1 ≤ E → (cert E).word.length ≤ c * polylog k E) :
    BigO precFilter (fun E => (certifiedGateBudget n cert) n E) (polylog k) := by
  refine ⟨c, by positivity, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => 1 ≤ E) (precFilter : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => 1 ≤ E)).mpr ⟨1, by norm_num⟩
  filter_upwards [hev] with E hE
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hpow : 0 ≤ polylog k E := by unfold polylog; positivity
  calc |(certifiedGateBudget n cert) n E| = (cert E).word.length := by
        simp only [certifiedGateBudget]
        exact abs_of_nonneg (Nat.cast_nonneg _)
    _ ≤ c * polylog k E := hlen E hE
    _ = c * |polylog k E| := by rw [abs_of_nonneg hpow]

theorem certifiedSynthesis_error_bigO {n d k c : ℕ} (S : ℝ → CertifiedSynthesis n d)
    (herr : ∀ E : ℝ, 1 ≤ E → (S E).error ≤ c * polylog k E) :
    BigO precFilter (fun E => (S E).error) (polylog k) := by
  refine ⟨c, by positivity, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => 1 ≤ E) (precFilter : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => 1 ≤ E)).mpr ⟨1, by norm_num⟩
  filter_upwards [hev] with E hE
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hpow : 0 ≤ polylog k E := by unfold polylog; positivity
  have hne : 0 ≤ (S E).error := (S E).error_nonneg
  calc |(S E).error| = (S E).error := abs_of_nonneg hne
    _ ≤ c * polylog k E := herr E hE
    _ = c * |polylog k E| := by rw [abs_of_nonneg hpow]

theorem compileError_budget_bigO :
    BigO precFilter (fun E => compileErrorBudget E) (polylog 1) := by
  refine ⟨1, by norm_num, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => Real.exp 1 ≤ E) (precFilter : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => Real.exp 1 ≤ E)).mpr
      ⟨Real.exp 1, fun b hb => hb⟩
  filter_upwards [hev] with E hExp
  have hlog : 1 ≤ Real.log E := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log E := Real.log_le_log (Real.exp_pos 1) hExp
    rw [Real.log_exp] at h1
    exact h1
  have hE : 1 ≤ E := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hEpos : 0 < E := lt_of_lt_of_le (Real.exp_pos 1) hExp
  have hdiv : 0 < 1 / E := one_div_pos.mpr hEpos
  have hdiv1 : 1 / E ≤ 1 := (div_le_one hEpos).2 hE
  have habs : 1 ≤ |Real.log E| := le_trans hlog (le_abs_self (Real.log E))
  calc |compileErrorBudget E| = 1 / E := by
        simp only [compileErrorBudget]
        exact abs_of_nonneg hdiv.le
    _ ≤ 1 := hdiv1
    _ ≤ |Real.log E| := habs
    _ = |polylog 1 E| := by simp [polylog]
    _ ≤ 1 * |polylog 1 E| := by rw [one_mul]

theorem macro_step_charge_discrepancy (g : FiniteGateCode) :
    (DynStep.macro g).stepAccount.classicalBits = 0 ∧ (DynStep.macro g).bitCharge = 1 :=
  ⟨rfl, rfl⟩

theorem emissionTime_actual (bits : ℕ) (word : List FiniteGateCode) :
    emissionTime bits word = bits * word.length := by
  unfold emissionTime machineWord
  rw [account_classicalBits]
  have hmain : ∀ (w : List FiniteGateCode),
      (counters (machineWord bits w)).classicalBits = bits * w.length := by
    intro w
    induction w with
    | nil => simp [machineWord, counters, Account.zero]
    | cons g rest ih =>
        have hexp : machineWord bits (g :: rest)
            = DynStep.classical bits :: DynStep.macro g :: machineWord bits rest := by
          simp [machineWord, List.flatMap_cons, List.cons_append]
        rw [hexp]
        simp only [counters_cons, seq_classicalBits]
        have h1 : (DynStep.classical bits).stepAccount.classicalBits = bits := rfl
        have h2 : (DynStep.macro g).stepAccount.classicalBits = 0 := rfl
        rw [h1, h2, ih]
        simp only [List.length_cons]
        ring
  exact hmain word

theorem emissionTime_stipulated_gap (bits : ℕ) (word : List FiniteGateCode) :
    (word.map (fun g => (DynStep.macro g).bitCharge)).sum + bits * word.length
      = (bits + 1) * word.length := by
  have h1 : (word.map (fun g => (DynStep.macro g).bitCharge)).sum = word.length := by
    induction word with
    | nil => simp
    | cons g rest ih =>
        have h2 : (DynStep.macro g).bitCharge = 1 := rfl
        simp only [List.map_cons, List.sum_cons, h2]
        rw [ih]
        simp only [List.length_cons]
        ring
  rw [h1]
  ring

theorem applyLive_alloc (live : List ℕ) (w : ℕ) (_h : w ∉ live) :
    applyLive live (DynStep.alloc w) = w :: live ∧
      w ∈ applyLive live (DynStep.alloc w) :=
  ⟨rfl, by simp [applyLive]⟩

theorem alloc_releaseClean_restores (live : List ℕ) (w : ℕ) (_h : w ∉ live) :
    applyLive (applyLive live (DynStep.alloc w)) (DynStep.releaseClean w) = live := by
  show (w :: live).erase w = live
  simp [List.erase]

theorem legalOps_lcuBlock (g : FiniteGateCode) :
    legalOps 0 (lcuTermBlock g) [] = true := by
  simp [legalOps, lcuTermBlock]

theorem lcuTermProgram_legal (terms : List FiniteGateCode) :
    legal 0 (lcuTermProgram terms) = true := by
  have hmain : ∀ (t : List FiniteGateCode), legalOps 0 (lcuTermProgram t) [] = true := by
    intro t
    induction t with
    | nil => rfl
    | cons g rest ih =>
        have hexp : lcuTermProgram (g :: rest)
            = DynStep.alloc 0 :: DynStep.macro g :: DynStep.releaseClean 0 ::
              lcuTermProgram rest := by
          simp [lcuTermProgram, List.flatMap_cons, List.cons_append]
        rw [hexp]
        simp [legalOps, List.erase, ih]
  have h1 : legal 0 (lcuTermProgram terms)
      = legalOps 0 (lcuTermProgram terms) (List.range 0) := rfl
  rw [h1]
  have h2 : List.range 0 = [] := by rfl
  rw [h2]
  exact hmain terms

theorem lcuTermProgram_balanced (terms : List FiniteGateCode) :
    balanced 0 (lcuTermProgram terms) := by
  have hmain : ∀ (t : List FiniteGateCode),
      liveAfter [] (lcuTermProgram t) = [] := by
    intro t
    induction t with
    | nil => rfl
    | cons g rest ih =>
        have hexp : lcuTermProgram (g :: rest)
            = DynStep.alloc 0 :: DynStep.macro g :: DynStep.releaseClean 0 ::
              lcuTermProgram rest := by
          simp [lcuTermProgram, List.flatMap_cons, List.cons_append]
        rw [hexp]
        simp only [liveAfter, List.foldl_cons]
        have hlive : applyLive (applyLive (applyLive [] (DynStep.alloc 0)) (DynStep.macro g))
            (DynStep.releaseClean 0) = [] := rfl
        rw [hlive]
        exact ih
  have h1 : finalLive 0 (lcuTermProgram terms)
      = liveAfter (List.range 0) (lcuTermProgram terms) := by
    unfold finalLive
    rw [runTrace_eq, runFrom_live]
    rfl
  unfold balanced
  rw [h1]
  have h2 : List.range 0 = [] := by rfl
  rw [h2]
  exact hmain terms

theorem lcuTermProgram_counters (t : List FiniteGateCode) :
    (counters (lcuTermProgram t)).basicGates = t.length ∧
      (counters (lcuTermProgram t)).macroGates = t.length ∧
      (counters (lcuTermProgram t)).depth = 3 * t.length ∧
      (counters (lcuTermProgram t)).classicalBits = 3 * t.length := by
  induction t with
  | nil => simp [lcuTermProgram, counters, Account.zero]
  | cons g rest ih =>
      have hexp : lcuTermProgram (g :: rest)
          = DynStep.alloc 0 :: DynStep.macro g :: DynStep.releaseClean 0 ::
            lcuTermProgram rest := by
        simp [lcuTermProgram, List.flatMap_cons, List.cons_append]
      rw [hexp]
      simp only [counters_cons, seq_basicGates, seq_macroGates, seq_depth, seq_classicalBits]
      have h1 : (DynStep.alloc 0).stepAccount.basicGates = 0 := rfl
      have h2 : (DynStep.macro g).stepAccount.basicGates = 1 := rfl
      have h3 : (DynStep.releaseClean 0).stepAccount.basicGates = 0 := rfl
      have h4 : (DynStep.alloc 0).stepAccount.macroGates = 0 := rfl
      have h5 : (DynStep.macro g).stepAccount.macroGates = 1 := rfl
      have h6 : (DynStep.releaseClean 0).stepAccount.macroGates = 0 := rfl
      have h7 : (DynStep.alloc 0).stepAccount.depth = 1 := rfl
      have h8 : (DynStep.macro g).stepAccount.depth = 1 := rfl
      have h9 : (DynStep.releaseClean 0).stepAccount.depth = 1 := rfl
      have h10 : (DynStep.alloc 0).stepAccount.classicalBits = 1 := rfl
      have h11 : (DynStep.macro g).stepAccount.classicalBits = 0 := rfl
      have h12 : (DynStep.releaseClean 0).stepAccount.classicalBits = 2 := rfl
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
      obtain ⟨i1, i2, i3, i4⟩ := ih
      rw [i1, i2, i3, i4]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        ring
      · simp only [List.length_cons]
        ring
      · simp only [List.length_cons]
        ring
      · simp only [List.length_cons]
        ring

theorem lcuTermProgram_ledgers (terms : List FiniteGateCode) :
    (account 0 (lcuTermProgram terms)).basicGates = terms.length ∧
      (account 0 (lcuTermProgram terms)).macroGates = terms.length ∧
      (account 0 (lcuTermProgram terms)).depth = 3 * terms.length ∧
      (account 0 (lcuTermProgram terms)).classicalBits = 3 * terms.length := by
  obtain ⟨i1, i2, i3, i4⟩ := lcuTermProgram_counters terms
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [account_basicGates, i1]
  · rw [account_macroGates, i2]
  · rw [account_depth, i3]
  · rw [account_classicalBits, i4]

theorem lcuTermProgram_peak (terms : List FiniteGateCode) :
    (account 0 (lcuTermProgram terms)).livePeak = (if terms = [] then 0 else 1) ∧
      (account 0 (lcuTermProgram terms)).peakWorkspace = (if terms = [] then 0 else 1) := by
  have hmain : ∀ (u : List FiniteGateCode),
      maxTrail (liveTrail [] (lcuTermProgram u)) = (if u = [] then 0 else 1) := by
    intro u
    induction u with
    | nil => simp [lcuTermProgram, liveTrail, maxTrail]
    | cons g rest ih =>
        have hexp : lcuTermProgram (g :: rest)
            = DynStep.alloc 0 :: DynStep.macro g :: DynStep.releaseClean 0 ::
              lcuTermProgram rest := by
          simp [lcuTermProgram, List.flatMap_cons, List.cons_append]
        rw [hexp]
        show maxTrail (1 :: 1 :: 0 :: liveTrail [] (lcuTermProgram rest)) =
          (if g :: rest = [] then 0 else 1)
        simp only [maxTrail_cons]
        rw [ih]
        by_cases hr : rest = []
        · simp [hr]
        · simp [hr]
  have hws : ∀ (u : List FiniteGateCode),
      maxTrail (wsTrail 0 [] (lcuTermProgram u)) = (if u = [] then 0 else 1) := by
    intro u
    induction u with
    | nil => simp [lcuTermProgram, wsTrail, maxTrail]
    | cons g rest ih =>
        have hexp : lcuTermProgram (g :: rest)
            = DynStep.alloc 0 :: DynStep.macro g :: DynStep.releaseClean 0 ::
              lcuTermProgram rest := by
          simp [lcuTermProgram, List.flatMap_cons, List.cons_append]
        rw [hexp]
        show maxTrail (1 :: 1 :: 0 :: wsTrail 0 [] (lcuTermProgram rest)) =
          (if g :: rest = [] then 0 else 1)
        simp only [maxTrail_cons]
        rw [ih]
        by_cases hr : rest = []
        · simp [hr]
        · simp [hr]
  have hz : List.range 0 = [] := by rfl
  refine ⟨?_, ?_⟩
  · rw [account_livePeak_formula, hz, hmain]
    simp
  · rw [account_peakWorkspace_formula, hz, hws]
    simp

theorem lcuTermProgram_lqSynthCount (n : ℕ) :
    (account 0 (lcuTermProgram (List.replicate (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n) (.h 0)))).macroGates
      = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n := by
  rw [account_macroGates]
  obtain ⟨_, hm, _, _⟩ := lcuTermProgram_counters
    (List.replicate (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n) (.h 0))
  rw [hm]
  simp

theorem lcuTermProgram_peak_disjoint_factors (terms : List FiniteGateCode)
    (hn : 0 < terms.length) :
    (account 0 (lcuTermProgram terms)).livePeak = 1 ∧
      (Account.par (account 0 (lcuTermBlock (.h 0)))
        (account 0 (lcuTermProgram terms))).livePeak = 2 := by
  have h1 : (account 0 (lcuTermBlock (.h 0))).livePeak = 1 := by
    rw [account_livePeak_formula]
    simp [lcuTermBlock, liveTrail, applyLive, maxTrail]
  obtain ⟨h2, _⟩ := lcuTermProgram_peak terms
  have hne : terms ≠ [] := by
    intro hcon
    subst hcon
    simp at hn
  have h2' : (account 0 (lcuTermProgram terms)).livePeak = 1 := by
    simp only [h2, hne, if_false]
  refine ⟨h2', ?_⟩
  simp only [Account.par]
  rw [h1, h2']

theorem certified_ref_composition {d r : ℕ}
    {A A' B B' : Matrix (Fin (d * r)) (Fin (d * r)) ℂ} {εA εB : ℝ}
    (hεA : 0 ≤ εA) (_hεB : 0 ≤ εB) (hA : Nonexpansive A) (hB' : Nonexpansive B')
    (hRA : RefBounded A A' εA) (hRB : RefBounded B B' εB) :
    RefBounded (A * B) (A' * B') (εA + εB) :=
  ref_error_combination d r A A' B B' εA εB hεA _hεB hA hB' hRA hRB

theorem stopping_interpreter_bridge (prep trial : ℕ) :
    (account 0 (stoppingWord prep trial)).classicalBits = prep + trial ∧
      (account 0 (stoppingWord prep trial)).depth = 2 ∧
      (stoppingAccount prep trial).classicalBits =
        (account 0 (stoppingWord prep trial)).classicalBits ∧
      (account 0 (stoppingWord prep trial ++ stoppingWord prep trial)).classicalBits
        = 2 * (prep + trial) ∧
      (Account.seq (stoppingAccount prep trial) (stoppingAccount prep trial)).classicalBits
        = 2 * (prep + trial) := by
  have h1 : (counters (stoppingWord prep trial)).classicalBits = prep + trial := by
    simp [stoppingWord, counters, seq_classicalBits, DynStep.stepAccount, Account.zero]
  have h2 : (counters (stoppingWord prep trial)).depth = 2 := by
    simp [stoppingWord, counters, seq_depth, DynStep.stepAccount, Account.zero]
  have h3 : (counters (stoppingWord prep trial ++ stoppingWord prep trial)).classicalBits
      = 2 * (prep + trial) := by
    rw [counters_append, seq_classicalBits, h1]
    ring
  have h4 : (stoppingAccount prep trial).classicalBits = prep + trial := rfl
  have e1 : (account 0 (stoppingWord prep trial)).classicalBits = prep + trial := by
    simp only [account_classicalBits, h1]
  have e2 : (account 0 (stoppingWord prep trial)).depth = 2 := by
    simp only [account_depth, h2]
  have e3 : (stoppingAccount prep trial).classicalBits =
      (account 0 (stoppingWord prep trial)).classicalBits := by
    simp only [h4, account_classicalBits, h1]
  have e4 : (account 0 (stoppingWord prep trial ++ stoppingWord prep trial)).classicalBits
      = 2 * (prep + trial) := by
    simp only [account_classicalBits, h3]
  have e5 : (Account.seq (stoppingAccount prep trial) (stoppingAccount prep trial)).classicalBits
      = 2 * (prep + trial) := by
    simp only [seq_classicalBits, h4]
    ring
  exact ⟨e1, e2, e3, e4, e5⟩

theorem stopping_alternating_retry_bridge :
    (account 0 (stoppingWord 2 3 ++ stoppingWord 2 3)).classicalBits = 10 ∧
      weightedExpectedCost alternatingRetryKernel alternatingRetryCost (.inr false) = 10 := by
  obtain ⟨_, _, _, h4, _⟩ := stopping_interpreter_bridge 2 3
  exact ⟨h4, alternatingRetry_expectedCost⟩

theorem clause1_complete :
    (∀ {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (FreshLedger.local (localCopyQPEProgramResources n s C)).localGates =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).localGates) ∧
    (∀ {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (FreshLedger.local (numericCopyResources n b C)).localGates =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).localGates) ∧
    (∀ {n M : ℕ} (ρ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      SameRunFull (FreshLedger.copyDriven (copyQPEProgramResources n C))
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C))) ∧
    (∀ {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      SameRunLocal (FreshLedger.local (localCopyQPEProgramResources n s C))
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C))) ∧
    (∀ {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      SameRunLocal (FreshLedger.local (numericCopyResources n b C))
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C))) ∧
    (∀ {n M : ℕ} (ρ σ : Operator (2 ^ n))
        (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      SameRunFull (FreshLedger.twoSpecies (copyQPEProgramResources (2 * n) C))
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C))) ∧
    (∀ (D : ℕ) (ρ : Operator D) (angles : List ℝ) (X : Operator D),
      SameRunFull (FreshLedger.plainComposition (freshCopyResourceCounts D angles))
        ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2)) ∧
    (∀ (base : ℕ) (ops : List DynStep),
      (account base ops).queries = forwardOracleCount ops) ∧
    (∀ (base : ℕ) (a b : List DynStep),
      workOf (account base (a ++ b)) = (workOf (account base a)).add (workOf (account base b))) ∧
    (∀ (base : ℕ) (a b : List DynStep),
      workOf (account base (mergeWords a b)) =
        (workOf (account base a)).add (workOf (account base b))) ∧
    (∀ (base : ℕ) (s : List DynStep) (k : ℕ),
      workOf (account base (repeatWord s k)) = (workOf (account base s)).smul k) :=
  ⟨localCopy_localGates_same_execution, numericCopy_localGates_same_execution,
    copyDriven_full_same_execution, localCopy_full_same_execution,
    numericCopy_full_same_execution, twoSpecies_full_same_execution,
    plainComposition_full_same_execution, account_queries_count, account_work_append,
    account_work_merge, account_work_repeat⟩

theorem clause2_complete :
    (∀ {Out : Type*} (P Q : Program Out),
      P.word = Q.word → P.base = Q.base → P.account = Q.account) ∧
    (∀ {Out : Type*} (P : Program Out), P.word = [] →
      P.account.queries = 0 ∧ P.account.adjointQueries = 0 ∧
        P.account.hamiltonianCount = 0 ∧ P.account.basicGates = 0 ∧
        P.account.macroGates = 0 ∧ P.account.depth = 0) ∧
    (∀ {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account) (P : Program Out),
      (∀ L : List ℕ, P.readout L = P.readout []) → T.nontrivial →
        ¬ Implements T (Program.gen P) B) ∧
    (∀ {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) (w : W), 2 ≤ n →
      ∀ (x : Reg n),
      MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ) ∧
        (account 0 (circuitResourceWord
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).queries
          = QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) ∧
        (account 0 (circuitResourceWord
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) 0)).livePeak = 1) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W],
      QueryLower (parityGen : ParityProgram (Fin 2) W → Gen ((Fin 2) → Bool) ℝ)
        (parityTask (Fin 2)) (fun _ => Fintype.card (Fin 2) / 2) 1 ∧
      parityIndicator (fun i : Fin 2 => decide (i = 0)) = 1 ∧
      parityIndicator (fun _ : Fin 2 => false) = 0 ∧
      (parityTask (Fin 2)).legal (fun i : Fin 2 => decide (i = 0))) :=
  ⟨program_account_determined, emptyProgram_no_cost, constantProgram_not_implements,
    search_same_execution_born_and_resources, parity_lower_bound_nonConstant⟩

theorem clause3_complete :
    jointFilter = sizeFilter ×ˢ precFilter ∧
    (∀ {f g : ℕ → ℝ → ℝ} (c : ℝ) (n0 : ℕ) (E0 : ℝ),
      (0 ≤ c ∧ (∀ n E, n0 ≤ n → E0 ≤ E →
        0 ≤ f n E ∧ 0 ≤ g n E ∧ f n E ≤ c * g n E)) →
        BigO jointFilter (fun p => f p.1 p.2) (fun p => g p.1 p.2)) ∧
    (∀ {n k c : ℕ} (cert : ℝ → SynthCertificate n),
      (∀ E : ℝ, 1 ≤ E → (cert E).word.length ≤ c * polylog k E) →
        BigO precFilter (fun E => (certifiedGateBudget n cert) n E) (polylog k)) ∧
    (∀ {n d k c : ℕ} (S : ℝ → CertifiedSynthesis n d),
      (∀ E : ℝ, 1 ≤ E → (S E).error ≤ c * polylog k E) →
        BigO precFilter (fun E => (S E).error) (polylog k)) ∧
    (BigO precFilter (fun E => compileErrorBudget E) (polylog 1)) ∧
    (∀ (bits : ℕ) (word : List FiniteGateCode),
      emissionTime bits word = bits * word.length) := by
  refine ⟨jointFilter_is_product, ?_, certifiedGateBudget_bigO,
    certifiedSynthesis_error_bigO, compileError_budget_bigO, emissionTime_actual⟩
  intro f g c n0 E0 hconj
  obtain ⟨hc, h⟩ := hconj
  exact joint_bigO c hc n0 E0 h

theorem clause4_complete :
    (∀ (g : FiniteGateCode), legalOps 0 (lcuTermBlock g) [] = true) ∧
    (∀ (terms : List FiniteGateCode), legal 0 (lcuTermProgram terms) = true) ∧
    (∀ (terms : List FiniteGateCode), balanced 0 (lcuTermProgram terms)) ∧
    (∀ (terms : List FiniteGateCode),
      (account 0 (lcuTermProgram terms)).basicGates = terms.length ∧
        (account 0 (lcuTermProgram terms)).macroGates = terms.length ∧
        (account 0 (lcuTermProgram terms)).depth = 3 * terms.length ∧
        (account 0 (lcuTermProgram terms)).classicalBits = 3 * terms.length) ∧
    (∀ (n : ℕ),
      (account 0 (lcuTermProgram
        (List.replicate (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n) (.h 0)))).macroGates
          = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n) ∧
    (∀ (terms : List FiniteGateCode), 0 < terms.length →
      (account 0 (lcuTermProgram terms)).livePeak = 1 ∧
        (Account.par (account 0 (lcuTermBlock (.h 0)))
          (account 0 (lcuTermProgram terms))).livePeak = 2) ∧
    (∀ (prep trial : ℕ),
      (account 0 (stoppingWord prep trial)).classicalBits = prep + trial ∧
        (account 0 (stoppingWord prep trial)).depth = 2 ∧
        (stoppingAccount prep trial).classicalBits =
          (account 0 (stoppingWord prep trial)).classicalBits ∧
        (account 0 (stoppingWord prep trial ++ stoppingWord prep trial)).classicalBits
          = 2 * (prep + trial) ∧
        (Account.seq (stoppingAccount prep trial) (stoppingAccount prep trial)).classicalBits
          = 2 * (prep + trial)) :=
  ⟨legalOps_lcuBlock, lcuTermProgram_legal, lcuTermProgram_balanced,
    lcuTermProgram_ledgers, lcuTermProgram_lqSynthCount,
    lcuTermProgram_peak_disjoint_factors, stopping_interpreter_bridge⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceExecution
