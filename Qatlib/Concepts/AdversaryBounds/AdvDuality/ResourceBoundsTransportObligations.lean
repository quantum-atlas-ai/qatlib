/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportFreshCopy
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportGrowth
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportImplBounds
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire

/-!
# Completed resource-bound transport obligations

This module packages and proves four groups of resource-bound obligations: fresh-copy execution
accounting, search implementation, asymptotic growth, and dynamic live-wire accounting.
`Clause1TransportSpec` through `Clause4TransportSpec` make the relevant execution identities,
bounds, and counterexamples explicit. For the underlying quantum circuit resource model, see
[NielsenChuang2010].

The completion theorems combine each imported clause claim with its transport specification. The
size-axis statements additionally record matching query and gate growth estimates for singleton
search.

## Main statements

* `clause1_spec_complete`: The first clause claim and its fresh-copy transport specification.
* `clause2_spec_complete`: The second clause claim and its search implementation specification.
* `clause3_spec_complete`: The third clause claim and its precision- and size-growth
  specification.
* `clause4_spec_complete`: The fourth clause claim and its dynamic-wire specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportObligations
noncomputable section

/-- The conjunction of fresh-copy execution identities, work and peak transport laws, repetition
formulas, and counterexamples to identifying local-gate or peak costs with copy counts. -/
def Clause1TransportSpec : Prop :=
    (∀ {n M : ℕ} (ρ : Operator (2 ^ n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
    copyQPEProgramResources n C =
          ((freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).copies,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).partialSwaps,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).discards,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M n ρ C)).bitQueries)) ∧
    (∀ {n M : ℕ} (s : ℕ) (ρ : Operator (2 ^ n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
    (FreshLedger.local (localCopyQPEProgramResources n s C)).copies =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).copies ∧
          (FreshLedger.local (localCopyQPEProgramResources n s C)).discards =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).discards ∧
          (FreshLedger.local (localCopyQPEProgramResources n s C)).bitQueries =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).bitQueries) ∧
    (∀ {n M : ℕ} (b k : ℕ) (ρ : Operator (2 ^ n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
    (FreshLedger.local (numericCopyResources n b C)).copies =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).copies ∧
          (FreshLedger.local (numericCopyResources n b C)).discards =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).discards ∧
          (FreshLedger.local (numericCopyResources n b C)).bitQueries =
            (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).bitQueries) ∧
    (∀ {n M : ℕ} (ρ σ : Operator (2 ^ n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
    copyQPEProgramResources (2 * n) C =
          ((freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).copies,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).partialSwaps,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).discards,
           (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M n ρ σ C)).bitQueries)) ∧
    (∀ (D : ℕ) (ρ : Operator D) (angles : List ℝ) (X : Operator D),
    freshCopyResourceCounts D angles =
          ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.copies,
           (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.partialSwaps,
           (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.discards,
           (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain (angles.map (fun θ => (ρ, θ))) X).2.bitQueries)) ∧
    (∀ (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost),
    (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).livePeak =
          (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).livePeak) ∧
    (    ¬ (∀ a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost,
            (Account.ofFreshCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b)).peakWorkspace =
              (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).peakWorkspace)) ∧
    (∀ (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost),
    FreshPeak.ofCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b) =
          (FreshPeak.ofCost a).seq (FreshPeak.ofCost b)) ∧
    (∀ (a : Account) (k : ℕ),
    workOf (Account.repeat a k) = (workOf a).smul k) ∧
    (∀ (a : Account) (k : ℕ),
    peakOf (Account.repeat a (Nat.succ k)) = peakOf a) ∧
    (∀ (a : Account) (k : ℕ),
    queryCountOf (Account.repeat a k) = k * queryCountOf a) ∧
    (∀ (base : ℕ) (s : DynStep),
    (profileOf s).basicGates = (account base [s]).basicGates ∧
          (profileOf s).classicalBits = (account base [s]).classicalBits) ∧
    (∀ (a : Account),
    (workOf a).queries + (workOf a).adjointQueries = a.toResourceCost.queries ∧
          (workOf a).macroGates = a.toResourceCost.macroGates ∧
          (workOf a).basicGates = a.toResourceCost.basicGates ∧
          (workOf a).depth = a.toResourceCost.depth ∧
          (workOf a).classicalBits = a.toResourceCost.classicalBits ∧
          ((workOf a).hamiltonianTicks : ℝ≥0∞) = a.toResourceCost.hamiltonianTime ∧
          (peakOf a).livePeak = a.toResourceCost.peakSpace) ∧
    (∀ (l : FreshLedger) (fm pf pc : ℕ),
    queryCountOf (l.account fm pf pc) = l.bitQueries) ∧
    (∀ (n M s : ℕ) (_hM : 2 ≤ M) (_hs : 0 < s),
    (localCopyLedger n M s).localGates = (localCopyLedger n M s).copies * (36 * n + 7) ∧
          (localCopyLedger n M s).localGates > (localCopyLedger n M s).copies) ∧
    (∀ (n M b : ℕ) (_hM : 2 ≤ M),
    (numericCopyLedger n M b).localGates = (numericCopyLedger n M b).copies * (36 * n + 4) ∧
          (numericCopyLedger n M b).localGates > (numericCopyLedger n M b).copies) ∧
    (∀ (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost),
    (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b).peakFreshRegisters =
          max a.peakFreshRegisters b.peakFreshRegisters) ∧
    (∀ (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost),
    (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b).peakCleanQubits =
          max a.peakCleanQubits b.peakCleanQubits) ∧
    (∀ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ),
    (repCost c (k + 1)).peakFreshRegisters = c.peakFreshRegisters ∧
          (repCost c (k + 1)).peakCleanQubits = c.peakCleanQubits) ∧
    (∀ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ),
    (repCost c k).partialSwaps = k * c.partialSwaps) ∧
    (∀ (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) (k : ℕ),
    (repCost c k).localGates = k * c.localGates) ∧
    (∀ (n M : ℕ) (ρ : Operator (2 ^ n)) (θ : ℝ) (s : ℕ) (_hs : 1 < s),
    (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).copies = s ∧
          (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakFreshRegisters = 1 ∧
          (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).copies
            ≠ (repCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s).peakFreshRegisters) ∧
    (∀ (n M : ℕ) (ρ : Operator (2 ^ n)) (θ : ℝ) (s : ℕ),
    (Account.ofFreshCost (repCost
            (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s)).depth
              = 3 * s ∧
          (Account.ofFreshCost (repCost
            (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost (@Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op.direct n M ρ θ)) s)).livePeak
              = if 0 < s then 1 else 0)
end
noncomputable section

/-- The conjunction of the singleton-search Born-probability lower bound, query-count upper
bound, and resource-budget implementation statement for `n ≥ 2`. -/
def Clause2TransportSpec : Prop :=
    (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (w : W) (_hn : 2 ≤ n) (x : Reg n),
    MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
            (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
            (Ket ((ZeroStr n, false), w)))
          (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ)) ∧
    (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (_w : W) (_hn : 2 ≤ n),
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)
          ≤ ((2 ^ n : ℕ) : ℝ)) ∧
    (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (w : W) (_hn : 2 ≤ n),
    Implements (singletonSearchTask n) (searchGen n W w) (searchBudget n W))
end
noncomputable section

/-- The exact singleton-search query and macro-gate counts, angle and iteration estimates, and
matching asymptotic growth bounds along the input-size filter. -/
def Clause3SizeAxis : Prop :=

    (∀ (n : ℕ), (searchAccount n).queries = singletonSearchIterations n) ∧
    (∀ (n : ℕ), (searchAccount n).macroGates = 3 * singletonSearchIterations n + 3) ∧
    (∀ (n : ℕ), 1 ≤ n → singletonSearchAngle n ≤ Real.pi / (2 * Real.sqrt (searchSpace n))) ∧
    (∀ (n : ℕ), 4 ≤ n → (singletonSearchIterations n : ℝ) ≥ Real.sqrt (searchSpace n) / 4) ∧
    (BigO sizeFilter (fun n => (searchAccount n).queries) searchSizeCost) ∧
    (BigOmega sizeFilter (fun n => (searchAccount n).queries) searchSizeCost) ∧
    (BigTheta sizeFilter (fun n => (searchAccount n).queries) searchSizeCost) ∧
    (BigTheta sizeFilter (fun n => (searchAccount n).macroGates) searchSizeCost)
end
noncomputable section

/-- The lower-bound and matching-growth transport laws, explicit lower-cost accounting,
fixed-bit-cost transport, and the singleton-search size-axis specification. -/
def Clause3TransportSpec : Prop :=
    (∀ {α : Type*} (F : Filter α) (f : α → ℝ),
    BigOmega F f f) ∧
    (∀ {α : Type*} (F : Filter α) (f g h : α → ℝ) (_hfg : BigOmega F f g) (_hgh : BigOmega F g h),
    BigOmega F f h) ∧
    (∀ (k c : ℕ) (n : ℕ) (wordLen : GateBudget) (_hc : 1 ≤ c) (_hcert : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n, c * polylog k E ≤ wordLen n E ∧ finiteWordLegal n s.word = true),
    BigOmega precFilter (fun E => wordLen n E) (polylog k)) ∧
    (∀ (k c : ℕ) (n : ℕ) (wordLen : GateBudget) (_hc : 1 ≤ c) (_hup : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n, 0 ≤ wordLen n E ∧ wordLen n E ≤ c * polylog k E ∧ finiteWordLegal n s.word = true) (_hlow : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n, c * polylog k E ≤ wordLen n E ∧ finiteWordLegal n s.word = true),
    BigTheta precFilter (fun E => wordLen n E) (polylog k)) ∧
    (∀ (repr work aux : ℕ) (p : LowerPremises) (_h : p.reprBits = repr ∧ p.workTape = work ∧ p.auxBits = aux),
    lowerCost p = repr + work + aux) ∧
    (∀ (bits : ℕ) (F : Filter ℝ) (f : ℝ → ℝ) (_h : BigO F f (polylog 1)),
    BigO F (fun E => (bits : ℝ) * f E) (polylog 1)) ∧
    Clause3SizeAxis
end
noncomputable section

/-- The dynamic-wire specifications for reset, uncomputation, release, classical-bit charges,
concrete peak ledgers, and the LCU dynamic word. -/
def Clause4TransportSpec : Prop :=
    (∀ (live : List ℕ) (w : ℕ),
    applyLive live (DynStep.reset w) = live) ∧
    (∀ (live : List ℕ) (w : ℕ),
    applyLive live (DynStep.uncompute w) = live) ∧
    (∀ (live : List ℕ) (w : ℕ),
    applyLive live (DynStep.releaseDirty w) = live.erase w) ∧
    (∀ (w : ℕ),
    (DynStep.alloc w).stepAccount.classicalBits = 1 ∧
        (DynStep.releaseClean w).stepAccount.classicalBits = 2 ∧
        (DynStep.releaseDirty w).stepAccount.classicalBits = 4 ∧
        (DynStep.reset w).stepAccount.classicalBits = 3 ∧
        (DynStep.uncompute w).stepAccount.classicalBits = 3) ∧
    (    (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).livePeak = 1 ∧
          (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).peakWorkspace = 1 ∧
          (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).classicalBits = 5 ∧
          (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).depth = 2 ∧
          finalLive 0 [DynStep.alloc 0, DynStep.releaseDirty 0] = []) ∧
    (    finalLive 0 [DynStep.alloc 0, DynStep.reset 0] = [0] ∧
          ¬ balanced 0 [DynStep.alloc 0, DynStep.reset 0] ∧
          balanced 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]) ∧
    (    finalLive 0 [DynStep.alloc 0, DynStep.uncompute 0] = [0] ∧
          ¬ balanced 0 [DynStep.alloc 0, DynStep.uncompute 0] ∧
          balanced 0 [DynStep.alloc 0, DynStep.uncompute 0, DynStep.releaseClean 0]) ∧
    (    (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).classicalBits = 6 ∧
          (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).depth = 3 ∧
          (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).livePeak = 1 ∧
          (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).peakWorkspace = 1) ∧
    (    (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).livePeak = 1 ∧
          (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).peakWorkspace = 1 ∧
          (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).classicalBits = 9 ∧
          (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).depth = 6) ∧
    (∀ (n : ℕ),
    (account 0 (lcuDynamicWord n)).basicGates = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n ∧
        (account 0 (lcuDynamicWord n)).livePeak = 1 ∧
        (account 0 (lcuDynamicWord n)).peakWorkspace = 1)
end
noncomputable section

/-- All fresh-copy execution, resource transport, repetition, and counterexample statements in
`Clause1TransportSpec` hold. -/
theorem clause1_transport_complete : Clause1TransportSpec :=
  ⟨copyDriven_same_execution,
    localCopy_same_execution,
    numericCopy_same_execution,
    twoSpecies_same_execution,
    plainComposition_same_execution,
    ofFreshCost_livePeak_transported,
    ofFreshCost_peakWorkspace_not_transported,
    freshPeak_transport,
    workOf_repeat,
    peakOf_repeat_succ,
    queryCountOf_repeat,
    profileOf_execution_verified,
    split_preserves_public_cost,
    freshLedger_unified_query_count,
    uniform_reading_misreports_local,
    uniform_reading_misreports_numeric,
    seqCost_peakFreshRegisters,
    seqCost_peakCleanQubits,
    repCost_peak_succ,
    repCost_partialSwaps,
    repCost_localGates,
    fresh_copy_peak_not_copy_count,
    fresh_copy_account_sum_and_max⟩
end
noncomputable section

/-- The singleton-search probability, query-count, and implementation statements in
`Clause2TransportSpec` hold. -/
theorem clause2_transport_complete : Clause2TransportSpec :=
  ⟨search_born_mass,
    search_query_count_le,
    search_implements_budget⟩
end
noncomputable section

/-- The exact singleton-search resource formulas and asymptotic size bounds in `Clause3SizeAxis`
hold. -/
theorem clause3_size_axis_complete : Clause3SizeAxis :=
  ⟨search_account_queries,
    search_account_gates,
    search_angle_bound,
    search_iterations_lower,
    search_query_bigO_size,
    search_query_bigOmega_size,
    search_query_bigTheta_size,
    search_gates_bigTheta_size⟩
end
noncomputable section

/-- The precision-growth, lower-cost transport, and search size-axis statements in
`Clause3TransportSpec` hold. -/
theorem clause3_transport_complete : Clause3TransportSpec :=
  ⟨bigOmega_refl,
    bigOmega_trans,
    gate_budget_bigOmega,
    gate_budget_bigTheta,
    lower_premises_same_cost_unit,
    lower_cost_transport, clause3_size_axis_complete⟩
end
noncomputable section

/-- The dynamic-wire update, charging, peak-accounting, and LCU statements in
`Clause4TransportSpec` hold. -/
theorem clause4_transport_complete : Clause4TransportSpec :=
  ⟨applyLive_reset,
    applyLive_uncompute,
    applyLive_releaseDirty,
    dynStep_release_bitCharges,
    discard_charges_peak,
    reset_keeps_wire_live,
    uncompute_keeps_wire_live,
    reset_discharge_ledger,
    peak_not_allocation_count,
    lcu_dynamic_word⟩
end
noncomputable section

/-- Establishes the imported first resource-bound clause `Clause1Claim`. -/
theorem clause1_complete : Clause1Claim := g1
end
noncomputable section

/-- Establishes `Clause2Claim`, combining implementation counterexamples and circuit counts with
the search upper-bound and parity lower-bound consumers. -/
theorem clause2_complete : Clause2Claim :=
  ⟨never_not_implements, timeout_not_implements, constant_not_implements,
    ofCircuit_counts, search_upper_bound_consumer, parity_lower_bound_consumer⟩
end
noncomputable section

/-- Establishes `Clause3Claim`, including elementary asymptotic rules and polylogarithmic gate
and bit-time bounds. -/
theorem clause3_complete : Clause3Claim :=
  ⟨bigO_refl, bigOWith_abs, bigO_trans, bigO_smul, bigTheta_iff, polylog_bigO,
    gate_budget_bigO, bit_time_bigO, lower_premises_explicit, bit_time_bigTheta⟩
end
noncomputable section

/-- Establishes `Clause4Claim`, combining balanced-word exchange, reference-error composition,
consumer ledgers, and a dynamic peak-space example. -/
theorem clause4_complete : Clause4Claim :=
  ⟨balanced_nil, account_work_exchange_conj,
    fun base a b ha hb =>
      ⟨account_livePeak_exchange base a b ha hb,
        account_peakWorkspace_exchange base a b ha hb,
        finalLive_exchange base a b ha hb⟩,
    ref_error_combination, lqAccount_ledgers, stopping_consumer_same_execution,
    peak_space_is_dynamic⟩
end
noncomputable section

/-- The first resource-bound clause holds together with its full fresh-copy transport
specification. -/
theorem clause1_spec_complete : Clause1Claim ∧ Clause1TransportSpec :=
  ⟨clause1_complete, clause1_transport_complete⟩
end
noncomputable section

/-- The second resource-bound clause holds together with its search implementation transport
specification. -/
theorem clause2_spec_complete : Clause2Claim ∧ Clause2TransportSpec :=
  ⟨clause2_complete, clause2_transport_complete⟩
end
noncomputable section

/-- The third resource-bound clause holds together with its precision- and size-growth transport
specification. -/
theorem clause3_spec_complete : Clause3Claim ∧ Clause3TransportSpec :=
  ⟨clause3_complete, clause3_transport_complete⟩
end
noncomputable section

/-- The fourth resource-bound clause holds together with its dynamic-wire transport
specification. -/
theorem clause4_spec_complete : Clause4Claim ∧ Clause4TransportSpec :=
  ⟨clause4_complete, clause4_transport_complete⟩
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportObligations
