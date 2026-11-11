/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

/-!
# Resource-account algebra and execution counts

This module proves projection, identity, associativity, and repetition laws for resource
accounts and their dynamic interpreter. The work components computed by `account` agree with
`counters`, while trace concatenation agrees with sequential interpreter execution. Resource
ledgers provide the bookkeeping needed for estimates such as those in [RoettelerEtAl2017].

The fresh-copy results identify costs returned by the interpreters and give exact macro, copy,
discard, and bit-query counts for direct, local, numeric, and two-species compilation. The
theorem `g1` assembles these results with outcome sequencing and resource-cost conversion into
`Clause1Claim`.

## Main statements

* `counters_append`, `runTrace_append`: composition of counters and executions.
* `counters_repeatWord`: counters for repeated words.
* `compileDirect_counts`, `compileNumeric_counts`: exact compilation counts.
* `fresh_run_cost`, `runPlain_cost`: interpreter costs agree with word costs.
* `g1`: the combined accounting specification.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open scoped ENNReal
open Qatlib

/-- The forward query count of a sequential composition is the sum of the corresponding
components. -/
theorem seq_queries (a b : Account) :
    (Account.seq a b).queries = a.queries + b.queries := rfl

/-- The adjoint query count of a sequential composition is the sum of the corresponding
components. -/
theorem seq_adjointQueries (a b : Account) :
    (Account.seq a b).adjointQueries = a.adjointQueries + b.adjointQueries := rfl

/-- The Hamiltonian evolution count of a sequential composition is the sum of the corresponding
components. -/
theorem seq_hamiltonianCount (a b : Account) :
    (Account.seq a b).hamiltonianCount = a.hamiltonianCount + b.hamiltonianCount := rfl

/-- The macro-gate count of a sequential composition is the sum of the corresponding components. -/
theorem seq_macroGates (a b : Account) :
    (Account.seq a b).macroGates = a.macroGates + b.macroGates := rfl

/-- The basic-gate count of a sequential composition is the sum of the corresponding components. -/
theorem seq_basicGates (a b : Account) :
    (Account.seq a b).basicGates = a.basicGates + b.basicGates := rfl

/-- The depth of a sequential composition is the sum of the corresponding components. -/
theorem seq_depth (a b : Account) :
    (Account.seq a b).depth = a.depth + b.depth := rfl

/-- The live-wire peak of a sequential composition is the maximum of the two live-wire peaks. -/
theorem seq_livePeak (a b : Account) :
    (Account.seq a b).livePeak = max a.livePeak b.livePeak := rfl

/-- The workspace peak of a sequential composition is the maximum of the two workspace peaks. -/
theorem seq_peakWorkspace (a b : Account) :
    (Account.seq a b).peakWorkspace = max a.peakWorkspace b.peakWorkspace := rfl

/-- The classical-bit count of a sequential composition is the sum of the corresponding
components. -/
theorem seq_classicalBits (a b : Account) :
    (Account.seq a b).classicalBits = a.classicalBits + b.classicalBits := rfl

/-- The Hamiltonian tick count of a sequential composition is the sum of the corresponding
components. -/
theorem seq_hamiltonianTicks (a b : Account) :
    (Account.seq a b).hamiltonianTicks = a.hamiltonianTicks + b.hamiltonianTicks := rfl

/-- The zero account is a left identity for sequential composition. -/
theorem seq_zero_left (a : Account) : Account.seq Account.zero a = a := by
  ext <;> simp [Account.seq, Account.zero]

/-- The zero account is a right identity for sequential composition. -/
theorem seq_zero_right (a : Account) : Account.seq a Account.zero = a := by
  ext <;> simp [Account.seq, Account.zero]

/-- Sequential composition of resource accounts is associative. -/
theorem seq_assoc (a b c : Account) :
    Account.seq (Account.seq a b) c = Account.seq a (Account.seq b c) := by
  ext <;> simp only [Account.seq]
  all_goals first | omega | exact max_assoc ..

/-- Parallel composition of resource accounts is commutative. -/
theorem par_comm (a b : Account) : Account.par a b = Account.par b a := by
  ext <;> simp only [Account.par] <;> omega

/-- Parallel composition of resource accounts is associative. -/
theorem par_assoc (a b c : Account) :
    Account.par (Account.par a b) c = Account.par a (Account.par b c) := by
  ext <;> simp only [Account.par] <;> omega

/-- The zero account is a left identity for parallel composition. -/
theorem par_zero_left (a : Account) : Account.par Account.zero a = a := by
  ext <;> simp [Account.par, Account.zero]

/-- Zero repetitions of an account give the zero account. -/
theorem repeat_zero (a : Account) : Account.repeat a 0 = Account.zero := rfl

/-- One more repetition sequentially combines the account with the account of the preceding
repetitions. -/
theorem repeat_succ (a : Account) (k : ℕ) :
    Account.repeat a (k + 1) = Account.seq a (Account.repeat a k) := rfl

/-- Repeating an account `k` times multiplies its forward query count by `k`. -/
theorem repeat_queries (a : Account) (k : ℕ) :
    (Account.repeat a k).queries = k * a.queries := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_queries, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its adjoint query count by `k`. -/
theorem repeat_adjointQueries (a : Account) (k : ℕ) :
    (Account.repeat a k).adjointQueries = k * a.adjointQueries := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_adjointQueries, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its Hamiltonian evolution count by `k`. -/
theorem repeat_hamiltonianCount (a : Account) (k : ℕ) :
    (Account.repeat a k).hamiltonianCount = k * a.hamiltonianCount := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_hamiltonianCount, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its macro-gate count by `k`. -/
theorem repeat_macroGates (a : Account) (k : ℕ) :
    (Account.repeat a k).macroGates = k * a.macroGates := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_macroGates, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its basic-gate count by `k`. -/
theorem repeat_basicGates (a : Account) (k : ℕ) :
    (Account.repeat a k).basicGates = k * a.basicGates := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_basicGates, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its depth by `k`. -/
theorem repeat_depth (a : Account) (k : ℕ) :
    (Account.repeat a k).depth = k * a.depth := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_depth, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its classical-bit count by `k`. -/
theorem repeat_classicalBits (a : Account) (k : ℕ) :
    (Account.repeat a k).classicalBits = k * a.classicalBits := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_classicalBits, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating an account `k` times multiplies its Hamiltonian tick count by `k`. -/
theorem repeat_hamiltonianTicks (a : Account) (k : ℕ) :
    (Account.repeat a k).hamiltonianTicks = k * a.hamiltonianTicks := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih => simp [repeat_succ, seq_hamiltonianTicks, ih, Nat.succ_mul, Nat.add_comm]

/-- An accounting step adds the step account's forward query count to the current account's
corresponding component. -/
theorem step_queries (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.queries = st.acc.queries + s.stepAccount.queries := rfl

/-- An accounting step adds the step account's adjoint query count to the current account's
corresponding component. -/
theorem step_adjointQueries (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.adjointQueries =
      st.acc.adjointQueries + s.stepAccount.adjointQueries := rfl

/-- An accounting step adds the step account's Hamiltonian evolution count to the current
account's corresponding component. -/
theorem step_hamiltonianCount (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.hamiltonianCount =
      st.acc.hamiltonianCount + s.stepAccount.hamiltonianCount := rfl

/-- An accounting step adds the step account's macro-gate count to the current account's
corresponding component. -/
theorem step_macroGates (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.macroGates = st.acc.macroGates + s.stepAccount.macroGates := rfl

/-- An accounting step adds the step account's basic-gate count to the current account's
corresponding component. -/
theorem step_basicGates (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.basicGates = st.acc.basicGates + s.stepAccount.basicGates := rfl

/-- An accounting step adds the step account's depth to the current account's corresponding
component. -/
theorem step_depth (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.depth = st.acc.depth + s.stepAccount.depth := rfl

/-- An accounting step adds the step account's classical-bit count to the current account's
corresponding component. -/
theorem step_classicalBits (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.classicalBits =
      st.acc.classicalBits + s.stepAccount.classicalBits := rfl

/-- An accounting step adds the step account's Hamiltonian tick count to the current account's
corresponding component. -/
theorem step_hamiltonianTicks (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.hamiltonianTicks =
      st.acc.hamiltonianTicks + s.stepAccount.hamiltonianTicks := rfl

/-- The live-wire list after an accounting step is obtained by `applyLive`. -/
theorem step_live (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).live = applyLive st.live s := rfl

/-- Running an empty dynamic word from a supplied state leaves the state unchanged. -/
theorem runFrom_nil (base : ℕ) (st : RunState) : runFrom base st [] = st := rfl

/-- Running a nonempty dynamic word first executes its head step and then runs its tail. -/
theorem runFrom_cons (base : ℕ) (st : RunState) (s : DynStep) (ops : List DynStep) :
    runFrom base st (s :: ops) = runFrom base (step base st s) ops := rfl

/-- Running a concatenation of dynamic words equals running the first word and then the second. -/
theorem runFrom_append (base : ℕ) (st : RunState) (a b : List DynStep) :
    runFrom base st (a ++ b) = runFrom base (runFrom base st a) b := by
  simp only [runFrom, List.foldl_append]

/-- The live-wire list produced by `runFrom` equals the fold of `applyLive` over the word. -/
theorem runFrom_live (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).live = liveAfter st.live ops := by
  induction ops generalizing st with
  | nil => rfl
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_live]
      simp [liveAfter]

/-- The counters of an empty dynamic word form the zero account. -/
theorem counters_nil : counters [] = Account.zero := rfl

/-- The counters of a nonempty word sequentially combine its head's step account with the tail's
counters. -/
theorem counters_cons (s : DynStep) (ops : List DynStep) :
    counters (s :: ops) = Account.seq s.stepAccount (counters ops) := rfl

/-- The counters of a concatenation equal the sequential composition of the two counter
accounts. -/
theorem counters_append (a b : List DynStep) :
    counters (a ++ b) = Account.seq (counters a) (counters b) := by
  induction a with
  | nil => simp [counters_nil, seq_zero_left]
  | cons s a ih => simp [List.cons_append, counters_cons, ih, seq_assoc]

/-- Running a dynamic word adds its counter account's forward query count to the initial
account's corresponding component. -/
theorem runFrom_queries (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.queries = st.acc.queries + (counters ops).queries := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_queries, counters_cons, seq_queries]
      omega

/-- Running a dynamic word adds its counter account's adjoint query count to the initial
account's corresponding component. -/
theorem runFrom_adjointQueries (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.adjointQueries =
      st.acc.adjointQueries + (counters ops).adjointQueries := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_adjointQueries, counters_cons, seq_adjointQueries]
      omega

/-- Running a dynamic word adds its counter account's Hamiltonian evolution count to the initial
account's corresponding component. -/
theorem runFrom_hamiltonianCount (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.hamiltonianCount =
      st.acc.hamiltonianCount + (counters ops).hamiltonianCount := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_hamiltonianCount, counters_cons, seq_hamiltonianCount]
      omega

/-- Running a dynamic word adds its counter account's macro-gate count to the initial account's
corresponding component. -/
theorem runFrom_macroGates (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.macroGates = st.acc.macroGates + (counters ops).macroGates := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_macroGates, counters_cons, seq_macroGates]
      omega

/-- Running a dynamic word adds its counter account's basic-gate count to the initial account's
corresponding component. -/
theorem runFrom_basicGates (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.basicGates = st.acc.basicGates + (counters ops).basicGates := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_basicGates, counters_cons, seq_basicGates]
      omega

/-- Running a dynamic word adds its counter account's depth to the initial account's
corresponding component. -/
theorem runFrom_depth (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.depth = st.acc.depth + (counters ops).depth := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_depth, counters_cons, seq_depth]
      omega

/-- Running a dynamic word adds its counter account's classical-bit count to the initial
account's corresponding component. -/
theorem runFrom_classicalBits (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.classicalBits =
      st.acc.classicalBits + (counters ops).classicalBits := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_classicalBits, counters_cons, seq_classicalBits]
      omega

/-- Running a dynamic word adds its counter account's Hamiltonian tick count to the initial
account's corresponding component. -/
theorem runFrom_hamiltonianTicks (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.hamiltonianTicks =
      st.acc.hamiltonianTicks + (counters ops).hamiltonianTicks := by
  induction ops generalizing st with
  | nil => simp [runFrom_nil, counters_nil, Account.zero]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_hamiltonianTicks, counters_cons, seq_hamiltonianTicks]
      omega

/-- Running a trace equals `runFrom` applied to the base initial state. -/
theorem runTrace_eq (base : ℕ) (ops : List DynStep) :
    runTrace base ops = runFrom base (initState base) ops := rfl

/-- Running a concatenated trace equals running its second word from the state produced by its
first. -/
theorem runTrace_append (base : ℕ) (a b : List DynStep) :
    runTrace base (a ++ b) = runFrom base (runTrace base a) b := by
  simp only [runTrace_eq, runFrom_append]

/-- The forward query count computed by the trace interpreter equals the corresponding component
of the word's counters. -/
theorem account_queries (base : ℕ) (ops : List DynStep) :
    (account base ops).queries = (counters ops).queries := by
  rw [account, runTrace_eq, runFrom_queries]
  simp [initState, Account.initAccount, Account.zero]

/-- The adjoint query count computed by the trace interpreter equals the corresponding component
of the word's counters. -/
theorem account_adjointQueries (base : ℕ) (ops : List DynStep) :
    (account base ops).adjointQueries = (counters ops).adjointQueries := by
  rw [account, runTrace_eq, runFrom_adjointQueries]
  simp [initState, Account.initAccount, Account.zero]

/-- The Hamiltonian evolution count computed by the trace interpreter equals the corresponding
component of the word's counters. -/
theorem account_hamiltonianCount (base : ℕ) (ops : List DynStep) :
    (account base ops).hamiltonianCount = (counters ops).hamiltonianCount := by
  rw [account, runTrace_eq, runFrom_hamiltonianCount]
  simp [initState, Account.initAccount, Account.zero]

/-- The macro-gate count computed by the trace interpreter equals the corresponding component of
the word's counters. -/
theorem account_macroGates (base : ℕ) (ops : List DynStep) :
    (account base ops).macroGates = (counters ops).macroGates := by
  rw [account, runTrace_eq, runFrom_macroGates]
  simp [initState, Account.initAccount, Account.zero]

/-- The basic-gate count computed by the trace interpreter equals the corresponding component of
the word's counters. -/
theorem account_basicGates (base : ℕ) (ops : List DynStep) :
    (account base ops).basicGates = (counters ops).basicGates := by
  rw [account, runTrace_eq, runFrom_basicGates]
  simp [initState, Account.initAccount, Account.zero]

/-- The depth computed by the trace interpreter equals the corresponding component of the word's
counters. -/
theorem account_depth (base : ℕ) (ops : List DynStep) :
    (account base ops).depth = (counters ops).depth := by
  rw [account, runTrace_eq, runFrom_depth]
  simp [initState, Account.initAccount, Account.zero]

/-- The classical-bit count computed by the trace interpreter equals the corresponding component
of the word's counters. -/
theorem account_classicalBits (base : ℕ) (ops : List DynStep) :
    (account base ops).classicalBits = (counters ops).classicalBits := by
  rw [account, runTrace_eq, runFrom_classicalBits]
  simp [initState, Account.initAccount, Account.zero]

/-- The Hamiltonian tick count computed by the trace interpreter equals the corresponding
component of the word's counters. -/
theorem account_hamiltonianTicks (base : ℕ) (ops : List DynStep) :
    (account base ops).hamiltonianTicks = (counters ops).hamiltonianTicks := by
  rw [account, runTrace_eq, runFrom_hamiltonianTicks]
  simp [initState, Account.initAccount, Account.zero]

/-- The account of an empty trace is the base initial account. -/
theorem account_nil (base : ℕ) : account base [] = Account.initAccount base := rfl

/-- The empty trace with zero base wires has the zero account. -/
theorem account_zero_nil : account 0 [] = Account.zero := by
  simp [account_nil, Account.initAccount, Account.zero]

/-- The counters of a repeated word equal the repeated sequential account of that word. -/
theorem counters_repeatWord (s : List DynStep) (k : ℕ) :
    counters (repeatWord s k) = Account.repeat (counters s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [repeatWord, counters_append, ih, repeat_succ]

/-- A macro step contributes exactly one basic gate and one macro gate. -/
theorem macro_step_account (g : FiniteGateCode) :
    ((DynStep.macro g).stepAccount).basicGates = 1 ∧
      ((DynStep.macro g).stepAccount).macroGates = 1 :=
  ⟨rfl, rfl⟩

/-- A step profile preserves the basic-gate and classical-bit components of the step account. -/
theorem profileOf_eq (s : DynStep) :
    (profileOf s).basicGates = s.stepAccount.basicGates ∧
      (profileOf s).classicalBits = s.stepAccount.classicalBits :=
  ⟨rfl, rfl⟩

/-- Sequencing a completed outcome with an always-nonterminating continuation yields
nontermination. -/
theorem bind_done_never {α : Type*} (a : α) :
    Outcome.bind (.done a) (fun _ => (.never : Outcome α)) = .never := rfl

/-- Sequencing a timeout with an always-nonterminating continuation preserves the timeout. -/
theorem bind_timeout_never {α β : Type*} :
    Outcome.bind (.timeout : Outcome α) (fun _ : α => (.never : Outcome β)) = .timeout := rfl

/-- Assigning a branch flag twice has the same effect as assigning only the last flag. -/
theorem branchMap_overwrite {α : Type*} (o : Outcome α) (b b' : Bool) :
    Outcome.branchMap (Outcome.branchMap o b') b = Outcome.branchMap o b := by
  cases o <;> rfl

/-- Assigning a branch flag before sequencing equals assigning it to the sequenced outcome. -/
theorem bind_branchMap {α β : Type*} (b : Bool) (o : Outcome α) (f : α → Outcome β) :
    Outcome.bind (Outcome.branchMap o b) f = Outcome.branchMap (Outcome.bind o f) b := by
  cases o with
  | done a => rfl
  | branch b' a => exact (branchMap_overwrite (f a) b b').symm
  | timeout => rfl
  | never => rfl

/-- Sequencing outcomes with `Outcome.bind` is associative. -/
theorem bind_assoc' {α β γ : Type*} (o : Outcome α) (f : α → Outcome β) (g : β → Outcome γ) :
    Outcome.bind (Outcome.bind o f) g = Outcome.bind o (fun x => Outcome.bind (f x) g) := by
  cases o with
  | done a => rfl
  | branch b a => exact bind_branchMap b (f a) g
  | timeout => rfl
  | never => rfl

/-- Converting a circuit account to `ResourceCost` preserves its query count, gate count as
macro gates, and size as depth. -/
theorem ofCircuit_toResourceCost {I : Type*} (C : Circuit I) :
    (Account.ofCircuit C).toResourceCost.queries = QueryCount C ∧
      (Account.ofCircuit C).toResourceCost.macroGates = GateCount C ∧
      (Account.ofCircuit C).toResourceCost.depth = Size C :=
  ⟨by simp [Account.ofCircuit], by simp [Account.ofCircuit], by simp [Account.ofCircuit]⟩

/-- A circuit account records its exact query count, gate count as macro gates, and size as
depth. -/
theorem ofCircuit_counts {I : Type*} (C : Circuit I) :
    (Account.ofCircuit C).queries = QueryCount C ∧
      (Account.ofCircuit C).macroGates = GateCount C ∧
      (Account.ofCircuit C).depth = Size C :=
  ⟨rfl, rfl, rfl⟩

open Qatlib

/-- Sequential composition of fresh-copy costs adds their copy counts. -/
theorem seqCost_copies (a b : Cost) :
    (seqCost a b).copies = a.copies + b.copies := rfl

/-- Sequential composition of fresh-copy costs adds their partial-swap counts. -/
theorem seqCost_partialSwaps (a b : Cost) :
    (seqCost a b).partialSwaps = a.partialSwaps + b.partialSwaps := rfl

/-- Sequential composition of fresh-copy costs adds their local-gate counts. -/
theorem seqCost_localGates (a b : Cost) :
    (seqCost a b).localGates = a.localGates + b.localGates := rfl

/-- Sequential composition of fresh-copy costs adds their fixed-macro counts. -/
theorem seqCost_fixedMacros (a b : Cost) :
    (seqCost a b).fixedMacros = a.fixedMacros + b.fixedMacros := rfl

/-- Sequential composition of fresh-copy costs adds their discard counts. -/
theorem seqCost_discards (a b : Cost) :
    (seqCost a b).discards = a.discards + b.discards := rfl

/-- Sequential composition of fresh-copy costs adds their bit-query counts. -/
theorem seqCost_bitQueries (a b : Cost) :
    (seqCost a b).bitQueries = a.bitQueries + b.bitQueries := rfl

/-- Sequential composition of fresh-copy costs is associative. -/
theorem seqCost_assoc (a b c : Cost) :
    seqCost (seqCost a b) c = seqCost a (seqCost b c) := by
  cases a
  cases b
  cases c
  simp only [seqCost]
  congr 1
  all_goals omega

/-- The zero fresh-copy cost is a left identity for sequential cost composition. -/
theorem seqCost_zero_left (a : Cost) : seqCost zeroCost a = a := by
  cases a
  simp only [seqCost, zeroCost]
  congr 1
  all_goals omega

/-- The fresh-copy cost obtained by sequentially composing a cost with itself the specified
number of times. -/
noncomputable def repCost (c : Cost) : ℕ → Cost
  | 0 => zeroCost
  | k + 1 => seqCost c (repCost c k)

/-- Repeating a fresh-copy cost `k` times multiplies its copy count by `k`. -/
theorem repCost_copies (c : Cost) (k : ℕ) :
    (repCost c k).copies = k * c.copies := by
  induction k with
  | zero => simp [repCost, zeroCost]
  | succ k ih =>
      change (seqCost c (repCost c k)).copies = (k + 1) * c.copies
      rw [seqCost_copies, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating a fresh-copy cost `k` times multiplies its fixed-macro count by `k`. -/
theorem repCost_fixedMacros (c : Cost) (k : ℕ) :
    (repCost c k).fixedMacros = k * c.fixedMacros := by
  induction k with
  | zero => simp [repCost, zeroCost]
  | succ k ih =>
      change (seqCost c (repCost c k)).fixedMacros = (k + 1) * c.fixedMacros
      rw [seqCost_fixedMacros, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating a fresh-copy cost `k` times multiplies its discard count by `k`. -/
theorem repCost_discards (c : Cost) (k : ℕ) :
    (repCost c k).discards = k * c.discards := by
  induction k with
  | zero => simp [repCost, zeroCost]
  | succ k ih =>
      change (seqCost c (repCost c k)).discards = (k + 1) * c.discards
      rw [seqCost_discards, ih, Nat.succ_mul, Nat.add_comm]

/-- Repeating a fresh-copy cost `k` times multiplies its bit-query count by `k`. -/
theorem repCost_bitQueries (c : Cost) (k : ℕ) :
    (repCost c k).bitQueries = k * c.bitQueries := by
  induction k with
  | zero => simp [repCost, zeroCost]
  | succ k ih =>
      change (seqCost c (repCost c k)).bitQueries = (k + 1) * c.bitQueries
      rw [seqCost_bitQueries, ih, Nat.succ_mul, Nat.add_comm]

/-- The cost of a nonempty fresh-copy word sequentially combines the head's step cost with the
tail's cost. -/
theorem freshWordCost_cons {n M : ℕ} (op : Op n M) (ops : List (Op n M)) :
    freshWordCost (op :: ops) = seqCost (stepCost op) (freshWordCost ops) := rfl

/-- The cost of repeating one fresh-copy operation is the repeated sequential cost of that
operation. -/
theorem freshWordCost_replicate {n M : ℕ} (op : Op n M) (k : ℕ) :
    freshWordCost (List.replicate k op) = repCost (stepCost op) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change seqCost (stepCost op) (freshWordCost (List.replicate k op))
        = repCost (stepCost op) (k + 1)
      rw [ih]
      rfl

/-- The cost of concatenated fresh-copy words is the sequential composition of their costs. -/
theorem freshWordCost_append {n M : ℕ} (a b : List (Op n M)) :
    freshWordCost (a ++ b) = seqCost (freshWordCost a) (freshWordCost b) := by
  induction a with
  | nil => exact (seqCost_zero_left _).symm
  | cons op a ih =>
      change seqCost (stepCost op) (freshWordCost (a ++ b))
        = seqCost (seqCost (stepCost op) (freshWordCost a)) (freshWordCost b)
      rw [ih, seqCost_assoc]

/-- The cost of repeating a two-operation block is the repeated sequential cost of that pair. -/
theorem freshWordCost_flatten_pair {n M : ℕ} (op1 op2 : Op n M) (s : ℕ) :
    freshWordCost ((List.replicate s [op1, op2]).flatten)
      = repCost (seqCost (stepCost op1) (stepCost op2)) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [List.replicate_succ, List.flatten_cons]
      change seqCost (stepCost op1) (seqCost (stepCost op2)
          (freshWordCost ((List.replicate s [op1, op2]).flatten)))
        = repCost (seqCost (stepCost op1) (stepCost op2)) (s + 1)
      rw [ih, ← seqCost_assoc]
      rfl

/-- A direct fresh-copy evolution step has cost `freshCost 0 0`. -/
theorem stepCost_direct {n M : ℕ} (ρ : Operator (2^n)) (θ : ℝ) :
    stepCost (@Op.direct n M ρ θ) = freshCost 0 0 := rfl

/-- A single fresh-copy cost consumes one copy. -/
theorem freshCost_copies (g clean : ℕ) : (freshCost g clean).copies = 1 := rfl

/-- A single fresh-copy cost records one discard. -/
theorem freshCost_discards (g clean : ℕ) : (freshCost g clean).discards = 1 := rfl

/-- A single fresh-copy cost has no fixed-macro charge. -/
theorem freshCost_fixedMacros (g clean : ℕ) : (freshCost g clean).fixedMacros = 0 := rfl

/-- A single fresh-copy cost has no bit-query charge. -/
theorem freshCost_bitQueries (g clean : ℕ) : (freshCost g clean).bitQueries = 0 := rfl

/-- The macro cost records exactly one fixed macro. -/
theorem macroCost_fixedMacros : macroCost.fixedMacros = 1 := rfl

/-- The macro cost consumes no fresh copies. -/
theorem macroCost_copies : macroCost.copies = 0 := rfl

/-- The macro cost records no discards. -/
theorem macroCost_discards : macroCost.discards = 0 := rfl

/-- The macro cost records no bit queries. -/
theorem macroCost_bitQueries : macroCost.bitQueries = 0 := rfl

/-- A fixed gate in a fresh-copy word has cost `macroCost`. -/
theorem stepCost_gate {n M : ℕ} (U : Matrix (Register n M) (Register n M) ℂ) :
    stepCost (Op.gate U) = macroCost := rfl

/-- A local fresh-copy step charges the compiled controlled-swap gate count and `n + 1` clean
qubits through `freshCost`. -/
theorem stepCost_localStep {n M : ℕ} (ρ : Operator (2^n)) (θ : ℝ) :
    stepCost (@Op.localStep n M ρ θ) = freshCost
      (GateCount (reflectionCompile (localControlledSwapSteps n θ))) (n + 1) := rfl

/-- A numeric fresh-copy step charges the compiled numeric controlled-swap gate count and `n +
1` clean qubits through `freshCost`. -/
theorem stepCost_numeric {n M : ℕ} (ρ : Operator (2^n)) (b k : ℕ) :
    stepCost (@Op.numeric n M ρ b k) = freshCost
      (GateCount (reflectionCompile (numericControlledSwapSteps n b k))) (n + 1) := rfl

/-- Direct compilation preserves the source gate count as fixed macros, consumes and discards
`s` copies per query, and uses no bit queries. -/
theorem compileDirect_counts {n M : ℕ} (s : ℕ) (ρ : Operator (2^n))
    (C : Circuit (Register n M)) :
    (freshWordCost (compileDirect n M s ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (compileDirect n M s ρ C)).copies = s * QueryCount C ∧
      (freshWordCost (compileDirect n M s ρ C)).discards = s * QueryCount C ∧
      (freshWordCost (compileDirect n M s ρ C)).bitQueries = 0 := by
  induction C with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  | cons st C ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      cases st with
      | gate U =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileDirect, freshWordCost_cons, stepCost_gate,
            seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            macroCost_fixedMacros, macroCost_copies, macroCost_discards, macroCost_bitQueries,
            GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring
      | query =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileDirect, freshWordCost_append, freshWordCost_replicate,
            stepCost_direct, seqCost_fixedMacros, seqCost_copies, seqCost_discards,
            seqCost_bitQueries, repCost_fixedMacros, repCost_copies, repCost_discards,
            repCost_bitQueries, freshCost_fixedMacros, freshCost_copies, freshCost_discards,
            freshCost_bitQueries, Nat.mul_one, GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring

/-- Local compilation preserves the source gate count as fixed macros, consumes and discards `s`
copies per query, and uses no bit queries. -/
theorem compileLocal_counts {n M : ℕ} (s : ℕ) (ρ : Operator (2^n))
    (C : Circuit (Register n M)) :
    (freshWordCost (compileLocal n M s ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (compileLocal n M s ρ C)).copies = s * QueryCount C ∧
      (freshWordCost (compileLocal n M s ρ C)).discards = s * QueryCount C ∧
      (freshWordCost (compileLocal n M s ρ C)).bitQueries = 0 := by
  induction C with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  | cons st C ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      cases st with
      | gate U =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileLocal, freshWordCost_cons, stepCost_gate,
            seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            macroCost_fixedMacros, macroCost_copies, macroCost_discards, macroCost_bitQueries,
            GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring
      | query =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileLocal, freshWordCost_append, freshWordCost_replicate,
            stepCost_localStep, seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            repCost_fixedMacros, repCost_copies, repCost_discards, repCost_bitQueries,
            freshCost_fixedMacros, freshCost_copies, freshCost_discards, freshCost_bitQueries,
            Nat.mul_one, GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring

/-- Numeric compilation preserves the source gate count as fixed macros, consumes and discards
`2 ^ b` copies per query, and uses no bit queries. -/
theorem compileNumeric_counts {n M : ℕ} (b k : ℕ) (ρ : Operator (2^n))
    (C : Circuit (Register n M)) :
    (freshWordCost (compileNumeric n M b k ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (compileNumeric n M b k ρ C)).copies = 2 ^ b * QueryCount C ∧
      (freshWordCost (compileNumeric n M b k ρ C)).discards = 2 ^ b * QueryCount C ∧
      (freshWordCost (compileNumeric n M b k ρ C)).bitQueries = 0 := by
  induction C with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  | cons st C ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      cases st with
      | gate U =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileNumeric, freshWordCost_cons, stepCost_gate,
            seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            macroCost_fixedMacros, macroCost_copies, macroCost_discards, macroCost_bitQueries,
            GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring
      | query =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileNumeric, freshWordCost_append, freshWordCost_replicate,
            stepCost_numeric, seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            repCost_fixedMacros, repCost_copies, repCost_discards, repCost_bitQueries,
            freshCost_fixedMacros, freshCost_copies, freshCost_discards, freshCost_bitQueries,
            GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring

/-- Two-species compilation preserves the source gate count as fixed macros, consumes and
discards `2 * s` copies per query, and uses no bit queries. -/
theorem compileTwo_counts {n M : ℕ} (s : ℕ) (ρ σ : Operator (2^n))
    (C : Circuit (Register n M)) :
    (freshWordCost (compileTwo n M s ρ σ C)).fixedMacros = GateCount C ∧
      (freshWordCost (compileTwo n M s ρ σ C)).copies = 2 * s * QueryCount C ∧
      (freshWordCost (compileTwo n M s ρ σ C)).discards = 2 * s * QueryCount C ∧
      (freshWordCost (compileTwo n M s ρ σ C)).bitQueries = 0 := by
  induction C with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  | cons st C ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      cases st with
      | gate U =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileTwo, freshWordCost_cons, stepCost_gate,
            seqCost_fixedMacros, seqCost_copies, seqCost_discards, seqCost_bitQueries,
            macroCost_fixedMacros, macroCost_copies, macroCost_discards, macroCost_bitQueries,
            GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring
      | query =>
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals simp only [compileTwo, freshWordCost_append, freshWordCost_flatten_pair,
            stepCost_direct, seqCost_fixedMacros, seqCost_copies, seqCost_discards,
            seqCost_bitQueries, repCost_fixedMacros, repCost_copies, repCost_discards,
            repCost_bitQueries, freshCost_fixedMacros, freshCost_copies, freshCost_discards,
            freshCost_bitQueries, GateCount, QueryCount, ih1, ih2, ih3, ih4]
          all_goals first | omega | ring

/-- The cost returned by the fresh-copy interpreter equals `freshWordCost` for its operation
list. -/
theorem fresh_run_cost {n M : ℕ} (ops : List (Op n M)) (X : State n M) :
    (run ops X).2 = freshWordCost ops := by
  induction ops generalizing X with
  | nil => rfl
  | cons op ops ih =>
      change seqCost (stepCost op) (run ops (stepMap op X)).2
        = seqCost (stepCost op) (freshWordCost ops)
      rw [ih]

/-- The plain fresh-copy interpreter returns `freshPlainCost` and consumes exactly one copy per
operator-angle pair. -/
theorem runPlain_cost {D : ℕ} (ops : List (Operator D × ℝ)) (X : Operator D) :
    (runPlain ops X).2 = freshPlainCost ops ∧
      (runPlain ops X).2.copies = ops.length := by
  induction ops generalizing X with
  | nil => refine ⟨rfl, rfl⟩
  | cons p ops ih =>
      obtain ⟨ih1, ih2⟩ := ih _
      refine ⟨?_, ?_⟩
      · change seqCost (freshCost 0 0) (runPlain ops (partialSwapOutput p.1 p.2 X)).2
          = seqCost (freshCost 0 0) (freshPlainCost ops)
        rw [ih1]
      · change (seqCost (freshCost 0 0) (runPlain ops (partialSwapOutput p.1 p.2 X)).2).copies
          = (p :: ops).length
        rw [seqCost_copies, freshCost_copies, ih2, List.length_cons]
        omega

/-- Converting sequential fresh-copy costs to accounts preserves sequential composition in all
eight work components. -/
theorem ofFreshCost_seq_work (a b : Cost) :
    (Account.ofFreshCost (seqCost a b)).queries
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).queries ∧
      (Account.ofFreshCost (seqCost a b)).adjointQueries
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).adjointQueries ∧
      (Account.ofFreshCost (seqCost a b)).hamiltonianCount
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).hamiltonianCount ∧
      (Account.ofFreshCost (seqCost a b)).macroGates
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).macroGates ∧
      (Account.ofFreshCost (seqCost a b)).basicGates
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).basicGates ∧
      (Account.ofFreshCost (seqCost a b)).depth
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).depth ∧
      (Account.ofFreshCost (seqCost a b)).classicalBits
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).classicalBits ∧
      (Account.ofFreshCost (seqCost a b)).hamiltonianTicks
        = (Account.seq (Account.ofFreshCost a) (Account.ofFreshCost b)).hamiltonianTicks := by
  cases a
  cases b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [seqCost, Account.ofFreshCost, Account.seq]
  all_goals first | omega | trivial

/-- The zero fresh-copy cost converts to the zero account. -/
theorem ofFreshCost_zero : Account.ofFreshCost zeroCost = Account.zero := rfl

/-- Establishes `Clause1Claim`, collecting the account algebra, dynamic interpreter identities,
fresh-copy compilation counts, execution costs, and outcome laws. -/
theorem g1 : Clause1Claim :=
  ⟨account_nil, account_zero_nil, account_queries, account_adjointQueries,
    account_hamiltonianCount, account_macroGates, account_basicGates, account_depth,
    account_classicalBits, account_hamiltonianTicks, macro_step_account, profileOf_eq,
    counters_append, runTrace_append, repeat_queries, counters_repeatWord,
    par_comm, par_assoc, par_zero_left,
    fun a => ⟨seq_zero_left a, seq_zero_right a⟩,
    seq_assoc,
    compileDirect_counts, compileLocal_counts, compileNumeric_counts, compileTwo_counts,
    fun ops X => ⟨(runPlain_cost ops X).2, (runPlain_cost ops X).1⟩,
    fresh_run_cost,
    bind_done_never, bind_timeout_never, bind_assoc',
    toResourceCost_seq, toResourceCost_zero, ofCircuit_toResourceCost⟩

end Qatlib.Concepts.ResourceBounds.AsymBounds
