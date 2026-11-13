/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Transporting fresh-copy execution resources

This module relates fresh-copy compilation and execution counts to resource ledgers for direct,
local, numeric, two-species, and plain-composition consumers. It gives exact copy, partial-swap,
discard, local-gate, and bit-query formulas, keeping the cost units explicit. Quantum circuit
resource accounting is discussed in [NielsenChuang2010].

The work ledger scales linearly under repetition, whereas positive repetition preserves peak
fields. `freshPeak_transport` preserves the separate fresh-register and clean-qubit peaks under
composition; the combined workspace field of `Account.ofFreshCost` does not universally preserve
composition.

## Main statements

* `copyDriven_same_execution`: Direct compilation realizes the stated program resource counts.
* `freshPeak_transport`: Separate fresh-copy peak fields preserve composition.
* `workOf_repeat`: Work scales linearly under repetition.
* `ofFreshCost_peakWorkspace_not_transported`: Combined workspace peaks fail universal
  transport.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
noncomputable section

/-- Every fresh-copy operation has equal partial-swap and copy counts. -/
theorem stepCost_partialSwaps_eq_copies {n M : ℕ} (op : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M) :
    (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost op).partialSwaps = (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost op).copies := by
  cases op <;> rfl
end
noncomputable section

/-- A word of fresh-copy operations has equal total partial-swap and copy counts. -/
theorem freshWordCost_partialSwaps_eq_copies {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M)) :
    (freshWordCost ops).partialSwaps = (freshWordCost ops).copies := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      rw [freshWordCost_cons, seqCost_partialSwaps, seqCost_copies, ih,
        stepCost_partialSwaps_eq_copies]
end
noncomputable section

/-- A plain operation list uses one copy, partial swap, and discard per entry and no bit
queries. -/
theorem freshPlainCost_counts {D : ℕ} (ops : List (Operator D × ℝ)) :
    (freshPlainCost ops).copies = ops.length ∧
      (freshPlainCost ops).partialSwaps = ops.length ∧
      (freshPlainCost ops).discards = ops.length ∧
      (freshPlainCost ops).bitQueries = 0 := by
  induction ops with
  | nil => simp [freshPlainCost, Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost]
  | cons p ops ih =>
      rw [freshPlainCost]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [seqCost_copies, ih.1]
        norm_num [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost, List.length_cons]; omega
      · rw [seqCost_partialSwaps, ih.2.1]
        norm_num [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost, List.length_cons]; omega
      · rw [seqCost_discards, ih.2.2.1]
        norm_num [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost, List.length_cons]; omega
      · rw [seqCost_bitQueries, ih.2.2.2]
        norm_num [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
end
noncomputable section

/-- For `M ≥ 2` and `n > 0`, the copy-driven ledger has `(M - 1) * n` copies, partial swaps, and
discards, and zero local gates and bit queries. -/
theorem copyDrivenLedger_eq (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) :
    copyDrivenLedger D M n = ⟨(M - 1) * n, (M - 1) * n, 0, (M - 1) * n, 0⟩ := by
  have h := copy_qpe_same_path_fresh_resource_counts D M n hM hn
  simp [copyDrivenLedger, FreshLedger.copyDriven, h]
end
noncomputable section

/-- For `M ≥ 2`, the local-copy ledger has `(M - 1) * s` copies and discards and `(36 * n + 7)`
local gates per copy, with no partial swaps or bit queries. -/
theorem localCopyLedger_eq (n M s : ℕ) (hM : 2 ≤ M) :
    localCopyLedger n M s = ⟨(M - 1) * s, 0, (M - 1) * s * (36 * n + 7), (M - 1) * s, 0⟩ := by
  obtain ⟨h1, _⟩ := localCopyQPEResources_eq n M s hM
  simp [localCopyLedger, FreshLedger.local, h1]
end
noncomputable section

/-- For `M > 0`, the numeric-copy ledger has `(M - 1) * 2 ^ b` copies and discards and `(36 * n
+ 4)` local gates per copy, with no partial swaps or bit queries. -/
theorem numericCopyLedger_eq (n M b : ℕ) (hM : 0 < M) :
    numericCopyLedger n M b = ⟨(M - 1) * 2 ^ b, 0, (M - 1) * 2 ^ b * (36 * n + 4),
      (M - 1) * 2 ^ b, 0⟩ := by
  have hq := (counted_offgrid_qpe_clean_flag M hM (1 : Operator (2 ^ n))
    (0 : QState (Fin (2 ^ n)))).2.1
  have h := numericCopyResources_eq n b (countedPhaseCircuit (I := Fin (2 ^ n)) M)
  simp [numericCopyLedger, FreshLedger.local, h, hq, Nat.mul_comm]
end
noncomputable section

/-- The two-species ledger has `2 * (M - 1) * n` copies, partial swaps, and discards, and no
local gates or bit queries. -/
theorem twoSpeciesLedger_eq (D M n : ℕ) :
    twoSpeciesLedger D M n = ⟨2 * (M - 1) * n, 2 * (M - 1) * n, 0, 2 * (M - 1) * n, 0⟩ := by
  simp [twoSpeciesLedger, FreshLedger.twoSpecies, twoSpeciesQPEResources]
end
noncomputable section

/-- For positive `M`, the two-species ledger equals the ledger extracted from the counted phase
circuit with repetition parameter `2 * n`. -/
theorem twoSpecies_same_path (D M n : ℕ) (hM : 0 < M) :
    twoSpeciesLedger D M n =
      FreshLedger.twoSpecies
        (copyQPEProgramResources (2 * n) (countedPhaseCircuit (I := Fin D) M)) := by
  rw [twoSpeciesLedger, twoSpeciesQPEResources_same_path D M n hM]
end
noncomputable section

/-- The plain-composition ledger has one copy, partial swap, and discard per angle and no local
gates or bit queries. -/
theorem plainCompositionLedger_eq (D : ℕ) (angles : List ℝ) :
    plainCompositionLedger D angles = ⟨angles.length, angles.length, 0, angles.length, 0⟩ := by
  have h := freshCopyResourceCounts_eq D angles
  simp [plainCompositionLedger, FreshLedger.plainComposition, h]
end
noncomputable section

/-- The copy, partial-swap, discard, and bit-query counts of direct compilation equal
`copyQPEProgramResources n C`. -/
theorem copyDriven_same_execution {n M : ℕ} (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    copyQPEProgramResources n C =
      ((freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).copies,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).partialSwaps,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).discards,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).bitQueries) := by
  obtain ⟨_, hcop, hdisc, hbit⟩ := compileDirect_counts n ρ C
  have hps : (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).partialSwaps
      = n * QueryCount C := by
    rw [freshWordCost_partialSwaps_eq_copies, hcop]
  rw [copyQPEProgramResources_eq]
  simp only [hcop, hps, hdisc, hbit]
  congr 1
  all_goals ac_rfl
end
noncomputable section

/-- The local-copy resource ledger agrees with local compilation on copy, discard, and bit-query
counts. -/
theorem localCopy_same_execution {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (localCopyQPEProgramResources n s C)).copies =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).copies ∧
      (FreshLedger.local (localCopyQPEProgramResources n s C)).discards =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).discards ∧
      (FreshLedger.local (localCopyQPEProgramResources n s C)).bitQueries =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).bitQueries := by
  obtain ⟨_, hcop, hdisc, hbit⟩ := compileLocal_counts s ρ C
  have hres := localCopyQPEProgramResources_eq n s C
  rw [hres] at ⊢
  simp only [FreshLedger.local] at ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hcop]
    show QueryCount C * s = s * QueryCount C
    exact (Nat.mul_comm s (QueryCount C)).symm
  · rw [hdisc]
    show QueryCount C * s = s * QueryCount C
    exact (Nat.mul_comm s (QueryCount C)).symm
  · rw [hbit]
end
noncomputable section

/-- The numeric-copy resource ledger agrees with numeric compilation on copy, discard, and
bit-query counts. -/
theorem numericCopy_same_execution {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    (FreshLedger.local (numericCopyResources n b C)).copies =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).copies ∧
      (FreshLedger.local (numericCopyResources n b C)).discards =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).discards ∧
      (FreshLedger.local (numericCopyResources n b C)).bitQueries =
        (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).bitQueries := by
  obtain ⟨_, hcop, hdisc, hbit⟩ := compileNumeric_counts b k ρ C
  have hres := numericCopyResources_eq n b C
  rw [hres] at ⊢
  simp only [FreshLedger.local] at ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hcop]
    show QueryCount C * 2 ^ b = 2 ^ b * QueryCount C
    exact (Nat.mul_comm (2 ^ b) (QueryCount C)).symm
  · rw [hdisc]
    show QueryCount C * 2 ^ b = 2 ^ b * QueryCount C
    exact (Nat.mul_comm (2 ^ b) (QueryCount C)).symm
  · rw [hbit]
end
noncomputable section

/-- The copy, partial-swap, discard, and bit-query counts of two-species compilation equal
`copyQPEProgramResources (2 * n) C`. -/
theorem twoSpecies_same_execution {n M : ℕ} (ρ σ : Operator (2 ^ n))
    (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)) :
    copyQPEProgramResources (2 * n) C =
      ((freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).copies,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).partialSwaps,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).discards,
       (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).bitQueries) := by
  obtain ⟨_, hcop, hdisc, hbit⟩ := compileTwo_counts n ρ σ C
  have hps : (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).partialSwaps
      = 2 * n * QueryCount C := by
    rw [freshWordCost_partialSwaps_eq_copies, hcop]
  rw [copyQPEProgramResources_eq]
  simp only [hcop, hps, hdisc, hbit]
  congr 1
  all_goals ac_rfl
end
noncomputable section

/-- The counts returned by plain execution with the given angles equal the fresh-copy resource
counts for that angle list. -/
theorem plainComposition_same_execution (D : ℕ) (ρ : Operator D) (angles : List ℝ)
    (X : Operator D) :
    freshCopyResourceCounts D angles =
      ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.copies,
       (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.partialSwaps,
       (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.discards,
       (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.bitQueries) := by
  obtain ⟨hcost, _⟩ := runPlain_cost (angles.map (fun θ => (ρ, θ))) X
  rw [hcost]
  obtain ⟨hc, hps, hd, hb⟩ := freshPlainCost_counts (angles.map (fun θ => (ρ, θ)))
  rw [hc, hps, hd, hb, List.length_map]
  exact freshCopyResourceCounts_eq D angles
end
noncomputable section

/-- Conversion of a fresh ledger assigns bit queries to forward queries, local gates to basic
gates, discards to classical bits, and the supplied macro and peak budgets to their account
fields, with the remaining query and Hamiltonian counters zero. -/
theorem freshLedger_account_ledgers (l : FreshLedger) (fm pf pc : ℕ) :
    (l.account fm pf pc).queries = l.bitQueries ∧
      (l.account fm pf pc).adjointQueries = 0 ∧
      (l.account fm pf pc).hamiltonianCount = 0 ∧
      (l.account fm pf pc).macroGates = fm ∧
      (l.account fm pf pc).basicGates = l.localGates ∧
      (l.account fm pf pc).classicalBits = l.discards ∧
      (l.account fm pf pc).hamiltonianTicks = 0 ∧
      (l.account fm pf pc).livePeak = max pf pc ∧
      (l.account fm pf pc).peakWorkspace = pf + pc := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end
noncomputable section

/-- The converted account depth is the sum of copies, partial swaps, local gates, supplied macro
gates, discards, and bit queries. -/
theorem freshLedger_account_depth (l : FreshLedger) (fm pf pc : ℕ) :
    (l.account fm pf pc).depth =
      l.copies + l.partialSwaps + l.localGates + fm + l.discards + l.bitQueries := by
  rfl
end
noncomputable section

/-- Converting fresh costs to accounts preserves the live-peak field under sequential
composition. -/
theorem ofFreshCost_livePeak_transported (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).livePeak =
      (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).livePeak := by
  simp only [Account.ofFreshCost, Account.seq, Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost]
  omega
end
noncomputable section

/-- Conversion of fresh costs to accounts fails to preserve the workspace-peak field under
sequential composition for some pair of costs. -/
theorem ofFreshCost_peakWorkspace_not_transported :
    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
        (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace) := by
  intro h
  have h1 := h ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
  norm_num [Account.ofFreshCost, Account.seq, Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost] at h1
end
noncomputable section

/-- Extracting the separate fresh-register and clean-qubit peaks commutes with sequential
composition of fresh costs. -/
theorem freshPeak_transport (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    FreshPeak.ofCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b) =
      (FreshPeak.ofCost a).seq (FreshPeak.ofCost b) := by
  rfl
end
noncomputable section

/-- The work ledger of `k` repetitions is the original work ledger multiplied by `k`. -/
theorem workOf_repeat (a : Account) (k : ℕ) :
    workOf (Account.repeat a k) = (workOf a).smul k := by
  simp only [workOf, WorkLedger.smul, repeat_queries, repeat_adjointQueries,
    repeat_hamiltonianCount, repeat_macroGates, repeat_basicGates, repeat_depth,
    repeat_classicalBits, repeat_hamiltonianTicks]
end
noncomputable section

/-- Repeating an account a positive number of times preserves its peak ledger. -/
theorem peakOf_repeat_succ (a : Account) (k : ℕ) :
    peakOf (Account.repeat a (Nat.succ k)) = peakOf a := by
  induction k with
  | zero =>
    rw [repeat_succ, Account.seq_peak, repeat_zero]
    simp only [peakOf, PeakLedger.takeMax, Account.zero, PeakLedger.mk.injEq]
    exact ⟨Nat.max_eq_left (Nat.zero_le _), Nat.max_eq_left (Nat.zero_le _)⟩
  | succ k ih =>
    rw [repeat_succ, Account.seq_peak, ih]
    simp only [peakOf, PeakLedger.takeMax, PeakLedger.mk.injEq]
    exact ⟨Nat.max_self _, Nat.max_self _⟩
end
noncomputable section

/-- The unified query count of `k` repetitions is `k` times the original unified query count. -/
theorem queryCountOf_repeat (a : Account) (k : ℕ) :
    queryCountOf (Account.repeat a k) = k * queryCountOf a := by
  rw [queryCountOf, repeat_queries, repeat_adjointQueries]
  exact (Nat.mul_add _ _ _).symm
end
noncomputable section

/-- A dynamic step's profile agrees with its singleton execution account on basic-gate and
classical-bit counts. -/
theorem profileOf_execution_verified (base : ℕ) (s : DynStep) :
    (profileOf s).basicGates = (account base [s]).basicGates ∧
      (profileOf s).classicalBits = (account base [s]).classicalBits := by
  refine ⟨?_, ?_⟩
  · rw [account_basicGates, counters_cons, seq_basicGates, counters_nil]
    simp only [Account.zero, profileOf]
    exact Nat.add_zero _
  · rw [account_classicalBits, counters_cons, seq_classicalBits, counters_nil]
    simp only [Account.zero, profileOf]
    exact Nat.add_zero _
end
noncomputable section

/-- Splitting an account into work and peak ledgers preserves the public resource cost,
combining forward and adjoint queries into its query field. -/
theorem split_preserves_public_cost (a : Account) :
    (workOf a).queries + (workOf a).adjointQueries = a.toResourceCost.queries ∧
      (workOf a).macroGates = a.toResourceCost.macroGates ∧
      (workOf a).basicGates = a.toResourceCost.basicGates ∧
      (workOf a).depth = a.toResourceCost.depth ∧
      (workOf a).classicalBits = a.toResourceCost.classicalBits ∧
      ((workOf a).hamiltonianTicks : ℝ≥0∞) = a.toResourceCost.hamiltonianTime ∧
      (peakOf a).livePeak = a.toResourceCost.peakSpace := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end
noncomputable section

/-- The unified query count of a converted fresh ledger equals its bit-query count. -/
theorem freshLedger_unified_query_count (l : FreshLedger) (fm pf pc : ℕ) :
    queryCountOf (l.account fm pf pc) = l.bitQueries := by
  have h := freshLedger_account_ledgers l fm pf pc
  rw [queryCountOf, h.1, h.2.1]
  omega
end
noncomputable section

/-- For `M ≥ 2` and positive `s`, the local-copy ledger uses exactly `36 * n + 7` local gates
per copy, so its local-gate count strictly exceeds its copy count. -/
theorem uniform_reading_misreports_local (n M s : ℕ) (hM : 2 ≤ M) (hs : 0 < s) :
    (localCopyLedger n M s).localGates = (localCopyLedger n M s).copies * (36 * n + 7) ∧
      (localCopyLedger n M s).localGates > (localCopyLedger n M s).copies := by
  rw [localCopyLedger_eq n M s hM]
  constructor
  · rfl
  · have hX : 0 < (M - 1) * s := by
      have h1 : 1 ≤ M - 1 := by omega
      have h2 : 1 ≤ s := by omega
      have h3 : 1 ≤ (M - 1) * s := Nat.mul_le_mul h1 h2
      omega
    have hlt : (M - 1) * s * 1 < (M - 1) * s * (36 * n + 7) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hX
    simpa [Nat.mul_one] using! hlt
end
noncomputable section

/-- For `M ≥ 2`, the numeric-copy ledger uses exactly `36 * n + 4` local gates per copy, so its
local-gate count strictly exceeds its copy count. -/
theorem uniform_reading_misreports_numeric (n M b : ℕ) (hM : 2 ≤ M) :
    (numericCopyLedger n M b).localGates = (numericCopyLedger n M b).copies * (36 * n + 4) ∧
      (numericCopyLedger n M b).localGates > (numericCopyLedger n M b).copies := by
  rw [numericCopyLedger_eq n M b (by omega)]
  constructor
  · rfl
  · have hX : 0 < (M - 1) * 2 ^ b := by
      have h1 : 1 ≤ M - 1 := by omega
      have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      have h3 : 1 ≤ (M - 1) * 2 ^ b := Nat.mul_le_mul h1 h2
      omega
    have hlt : (M - 1) * 2 ^ b * 1 < (M - 1) * 2 ^ b * (36 * n + 4) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hX
    simpa [Nat.mul_one] using! hlt
end
noncomputable section

/-- The peak fresh-register count of sequentially composed fresh costs is the maximum of the two
component peaks. -/
theorem seqCost_peakFreshRegisters (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b).peakFreshRegisters =
      max a.peakFreshRegisters b.peakFreshRegisters := rfl
end
noncomputable section

/-- The peak clean-qubit count of sequentially composed fresh costs is the maximum of the two
component peaks. -/
theorem seqCost_peakCleanQubits (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b).peakCleanQubits =
      max a.peakCleanQubits b.peakCleanQubits := rfl
end
noncomputable section

/-- Positive repetition of a fresh cost preserves its peak fresh-register count. -/
theorem repCost_peakFresh_succ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ) :
    (repCost c (k + 1)).peakFreshRegisters = c.peakFreshRegisters := by
  induction k with
  | zero =>
      rw [repCost, seqCost_peakFreshRegisters, repCost,
          Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost]
      exact Nat.max_eq_left (Nat.zero_le _)
  | succ k ih =>
      rw [repCost, seqCost_peakFreshRegisters, ih]
      exact Nat.max_self _
end
noncomputable section

/-- Positive repetition of a fresh cost preserves its peak clean-qubit count. -/
theorem repCost_peakClean_succ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ) :
    (repCost c (k + 1)).peakCleanQubits = c.peakCleanQubits := by
  induction k with
  | zero =>
      rw [repCost, seqCost_peakCleanQubits, repCost,
          Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost]
      exact Nat.max_eq_left (Nat.zero_le _)
  | succ k ih =>
      rw [repCost, seqCost_peakCleanQubits, ih]
      exact Nat.max_self _
end
noncomputable section

/-- Positive repetition of a fresh cost preserves both its peak fresh-register count and its
peak clean-qubit count. -/
theorem repCost_peak_succ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ) :
    (repCost c (k + 1)).peakFreshRegisters = c.peakFreshRegisters ∧
      (repCost c (k + 1)).peakCleanQubits = c.peakCleanQubits :=
  ⟨repCost_peakFresh_succ c k, repCost_peakClean_succ c k⟩
end
noncomputable section

/-- Repeating a fresh cost `k` times multiplies its partial-swap count by `k`. -/
theorem repCost_partialSwaps (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ) :
    (repCost c k).partialSwaps = k * c.partialSwaps := by
  induction k with
  | zero => simp [repCost, Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost]
  | succ k ih =>
      change (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost c (repCost c k)).partialSwaps
        = (k + 1) * c.partialSwaps
      rw [seqCost_partialSwaps, ih, Nat.succ_mul, Nat.add_comm]
end
noncomputable section

/-- Repeating a fresh cost `k` times multiplies its local-gate count by `k`. -/
theorem repCost_localGates (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ) :
    (repCost c k).localGates = k * c.localGates := by
  induction k with
  | zero => simp [repCost, Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost]
  | succ k ih =>
      change (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost c (repCost c k)).localGates
        = (k + 1) * c.localGates
      rw [seqCost_localGates, ih, Nat.succ_mul, Nat.add_comm]
end
noncomputable section

/-- More than one repetition of a direct fresh-copy step consumes `s` copies but has peak
fresh-register count one, so these counts differ. -/
theorem fresh_copy_peak_not_copy_count (n M : ℕ) (ρ : Operator (2 ^ n)) (θ : ℝ)
    (s : ℕ) (hs : 1 < s) :
    (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).copies = s ∧
      (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakFreshRegisters = 1 ∧
      (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).copies
        ≠ (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakFreshRegisters := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have hstep : Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)
      = Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost 0 0 := stepCost_direct ρ θ
  have hcop : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) (k + 1)).copies = k + 1 := by
    rw [hstep, repCost_copies]
    exact Nat.mul_one _
  have hpeak : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) (k + 1)).peakFreshRegisters = 1 := by
    rw [hstep, repCost_peakFresh_succ]
    rfl
  refine ⟨hcop, hpeak, ?_⟩
  rw [hcop, hpeak]
  omega
end
noncomputable section

/-- The account of `s` direct fresh-copy steps has depth `3 * s` and live peak one for positive
`s`, or zero when `s` is zero. -/
theorem fresh_copy_account_sum_and_max (n M : ℕ) (ρ : Operator (2 ^ n)) (θ : ℝ)
    (s : ℕ) :
    (Account.ofFreshCost (repCost
        (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s)).depth
          = 3 * s ∧
      (Account.ofFreshCost (repCost
        (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s)).livePeak
          = if 0 < s then 1 else 0 := by
  have hstep : Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)
      = Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost 0 0 := stepCost_direct ρ θ
  have hcop : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).copies = s := by
    rw [hstep, repCost_copies]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hps : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).partialSwaps = s := by
    rw [hstep, repCost_partialSwaps]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hdisc : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).discards = s := by
    rw [hstep, repCost_discards]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hloc : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).localGates = 0 := by
    rw [hstep, repCost_localGates]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hmac : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).fixedMacros = 0 := by
    rw [hstep, repCost_fixedMacros]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hbit : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).bitQueries = 0 := by
    rw [hstep, repCost_bitQueries]
    simp [Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost]
  have hpf : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakFreshRegisters
        = if 0 < s then 1 else 0 := by
    by_cases hs : 0 < s
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      rw [hstep, repCost_peakFresh_succ]
      rfl
    · have hs0 : s = 0 := by omega
      subst hs0
      rfl
  have hpc : (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost
      (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakCleanQubits = 0 := by
    by_cases hs : 0 < s
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      rw [hstep, repCost_peakClean_succ]
      rfl
    · have hs0 : s = 0 := by omega
      subst hs0
      rfl
  simp only [Account.ofFreshCost]
  rw [hcop, hps, hloc, hmac, hdisc, hbit, hpf, hpc]
  constructor
  · omega
  · by_cases hs : 0 < s <;> simp [hs]
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
