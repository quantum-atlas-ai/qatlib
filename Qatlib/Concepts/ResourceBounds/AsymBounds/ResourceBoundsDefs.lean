/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyExecutionDefs
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.ResourceBounds.AsymBounds.WeightedStoppingConsumers
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.ResourceBounds.AsymBounds.GatesBitDefs

/-!
# Resource accounts and asymptotic specifications

This module defines `Account`, a resource ledger combining query, gate, depth, space,
classical-bit, and Hamiltonian counters. Sequential composition adds work and takes maxima of
space peaks; `Account.par` adds every component, including depth. `runTrace` computes accounts
and live-wire lists for dynamic words. General resource-estimation context is provided by
[RoettelerEtAl2017].

The module also defines outcome-based task correctness and implementation predicates, query
upper and lower bounds, fresh-copy and circuit-cost conversions, and filter-based asymptotic
relations. The four `Clause1Claim` through `Clause4Claim` propositions collect the laws proved
by later modules.

## Main statements

* `Account.seq`: sequential resource composition.
* `account`: resource accounting with live-wire tracking.
* `Implements`: completed task execution within a componentwise budget.
* `BigO`, `BigOmega`, `BigTheta`: eventual asymptotic comparisons.
* `Clause1Claim`: the accounting and execution-cost specification.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

namespace Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib
open scoped ENNReal

/-- A resource record counting forward and adjoint queries, Hamiltonian evolutions and ticks,
macro and basic gates, depth, peak live and workspace sizes, and classical bits. -/
@[ext] structure Account where

  queries : ℕ

  adjointQueries : ℕ

  hamiltonianCount : ℕ

  macroGates : ℕ

  basicGates : ℕ

  depth : ℕ

  livePeak : ℕ

  peakWorkspace : ℕ

  classicalBits : ℕ

  hamiltonianTicks : ℕ
  deriving DecidableEq, Repr

/-- The resource account with every component equal to zero. -/
def Account.zero : Account :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The zero-work resource account whose live-wire peak is initialized to `base`. -/
def Account.initAccount (base : ℕ) : Account :=
  { Account.zero with livePeak := base }

/-- Combines resource accounts by adding work and depth components and taking maxima of live and
workspace peaks. -/
def Account.seq (a b : Account) : Account :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth, max a.livePeak b.livePeak,
    max a.peakWorkspace b.peakWorkspace, a.classicalBits + b.classicalBits,
    a.hamiltonianTicks + b.hamiltonianTicks⟩

/-- Combines resource accounts by componentwise addition, including depth and both space peaks. -/
def Account.par (a b : Account) : Account :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth, a.livePeak + b.livePeak,
    a.peakWorkspace + b.peakWorkspace, a.classicalBits + b.classicalBits,
    a.hamiltonianTicks + b.hamiltonianTicks⟩

/-- The resource account for a specified number of sequential repetitions, starting from the
zero account. -/
def Account.repeat (a : Account) : ℕ → Account
  | 0 => Account.zero
  | k + 1 => Account.seq a (Account.repeat a k)

/-- Componentwise comparison of all ten resource-account fields. -/
def accountLE (a b : Account) : Prop :=
  a.queries ≤ b.queries ∧ a.adjointQueries ≤ b.adjointQueries ∧
    a.hamiltonianCount ≤ b.hamiltonianCount ∧ a.macroGates ≤ b.macroGates ∧
    a.basicGates ≤ b.basicGates ∧ a.depth ≤ b.depth ∧ a.livePeak ≤ b.livePeak ∧
    a.peakWorkspace ≤ b.peakWorkspace ∧ a.classicalBits ≤ b.classicalBits ∧
    a.hamiltonianTicks ≤ b.hamiltonianTicks

/-- The zero account is componentwise bounded by every account. -/
@[simp] theorem accountLE_zero (a : Account) : accountLE Account.zero a :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- Componentwise comparison of resource accounts is reflexive. -/
@[simp] theorem accountLE_refl (a : Account) : accountLE a a :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _,
    le_refl _, le_refl _, le_refl _⟩

/-- Componentwise comparison of resource accounts is transitive. -/
theorem accountLE_trans {a b c : Account} (hab : accountLE a b) (hbc : accountLE b c) :
    accountLE a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.1.trans hbc.2.2.1,
    hab.2.2.2.1.trans hbc.2.2.2.1, hab.2.2.2.2.1.trans hbc.2.2.2.2.1,
    hab.2.2.2.2.2.1.trans hbc.2.2.2.2.2.1, hab.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.2.2.trans hbc.2.2.2.2.2.2.2.2.2⟩

/-- Converts an account to `ResourceCost`, combining forward and adjoint queries, using the live
peak for space and Hamiltonian ticks for time. -/
def Account.toResourceCost (a : Account) : ResourceCost :=
  ⟨a.queries + a.adjointQueries, a.macroGates, a.basicGates, a.depth, a.livePeak,
    (a.hamiltonianTicks : ℝ≥0∞), a.classicalBits⟩

/-- Converting an account to `ResourceCost` adds its forward and adjoint query counts. -/
@[simp] theorem toResourceCost_queries (a : Account) :
    a.toResourceCost.queries = a.queries + a.adjointQueries := rfl

/-- Conversion to `ResourceCost` preserves the macro-gate count. -/
@[simp] theorem toResourceCost_macroGates (a : Account) :
    a.toResourceCost.macroGates = a.macroGates := rfl

/-- Conversion to `ResourceCost` preserves the basic-gate count. -/
@[simp] theorem toResourceCost_basicGates (a : Account) :
    a.toResourceCost.basicGates = a.basicGates := rfl

/-- Conversion to `ResourceCost` preserves depth. -/
@[simp] theorem toResourceCost_depth (a : Account) :
    a.toResourceCost.depth = a.depth := rfl

/-- The peak space of the converted resource cost equals the account's live-wire peak. -/
@[simp] theorem toResourceCost_peakSpace (a : Account) :
    a.toResourceCost.peakSpace = a.livePeak := rfl

/-- The Hamiltonian time of the converted resource cost equals the account's Hamiltonian ticks. -/
@[simp] theorem toResourceCost_hamiltonianTime (a : Account) :
    a.toResourceCost.hamiltonianTime = a.hamiltonianTicks :=
  rfl

/-- Conversion to `ResourceCost` preserves the classical-bit count. -/
@[simp] theorem toResourceCost_classicalBits (a : Account) :
    a.toResourceCost.classicalBits = a.classicalBits := rfl

/-- The zero account converts to the zero resource cost. -/
theorem toResourceCost_zero : Account.zero.toResourceCost = (0 : ResourceCost) := by
  simp only [Account.zero, Account.toResourceCost, Nat.cast_zero]
  rfl

/-- Converting a sequential combination of accounts equals adding their converted resource
costs. -/
theorem toResourceCost_seq (a b : Account) :
    (Account.seq a b).toResourceCost = a.toResourceCost + b.toResourceCost := by
  cases a
  cases b
  apply ResourceCost.ext <;>
    simp only [Account.seq, Account.toResourceCost, ResourceCost.add_queries,
      ResourceCost.add_macroGates, ResourceCost.add_basicGates, ResourceCost.add_depth,
      ResourceCost.add_peakSpace, ResourceCost.add_hamiltonianTime,
      ResourceCost.add_classicalBits]
  all_goals first | omega | simp [Nat.cast_add]

/-- Dynamic resource steps for forward or adjoint queries, fixed macros, Hamiltonian evolution,
classical work, and wire management. -/
inductive DynStep where

  | oracle (adjoint : Bool) (ws : List ℕ)

  | macro (g : FiniteGateCode)

  | evolve (ticks : ℕ)

  | classical (bits : ℕ)

  | alloc (w : ℕ)

  | releaseClean (w : ℕ)

  | releaseDirty (w : ℕ)

  | reset (w : ℕ)

  | uncompute (w : ℕ)
  deriving DecidableEq, Repr

/-- Concatenates a dynamic-step word with itself the specified number of times. -/
def repeatWord (s : List DynStep) : ℕ → List DynStep
  | 0 => []
  | k + 1 => s ++ repeatWord s k

/-- Assigns bit charges to dynamic steps according to their query-wire lists, classical-bit
payloads, and wire-management operations. -/
def DynStep.bitCharge : DynStep → ℕ
  | .oracle _ ws => 1 + ws.length
  | .macro _ => 1
  | .evolve _ => 0
  | .classical bits => bits
  | .alloc _ => 1
  | .releaseClean _ => 2
  | .releaseDirty _ => 4
  | .reset _ => 3
  | .uncompute _ => 3

/-- Assigns a single-step resource account, distinguishing forward queries, adjoint queries,
gates, evolution ticks, classical work, and wire-management charges. -/
def DynStep.stepAccount : DynStep → Account
  | .oracle false _ => { Account.zero with queries := 1, depth := 1 }
  | .oracle true _ => { Account.zero with adjointQueries := 1, depth := 1 }
  | .macro _ => { Account.zero with macroGates := 1, basicGates := 1, depth := 1 }
  | .evolve t =>
      { Account.zero with hamiltonianCount := 1, hamiltonianTicks := t, depth := 1 }
  | .classical bits => { Account.zero with classicalBits := bits, depth := 1 }
  | s => { Account.zero with classicalBits := s.bitCharge, depth := 1 }

/-- Extracts basic-gate, workspace, Hamiltonian-time, and classical-bit components of a dynamic
step into a `StepProfile`. -/
def profileOf (s : DynStep) : StepProfile :=
  ⟨s.stepAccount.basicGates, s.stepAccount.peakWorkspace,
    (s.stepAccount.hamiltonianTicks : ℝ≥0∞), s.stepAccount.classicalBits⟩

/-- Sequentially combines the single-step accounts of a dynamic word, without tracking a
live-wire list. -/
def counters : List DynStep → Account
  | [] => Account.zero
  | s :: rest => Account.seq s.stepAccount (counters rest)

/-- The accounting interpreter state, consisting of a resource account and a list of live wire
labels. -/
structure RunState where
  acc : Account
  live : List ℕ
  deriving DecidableEq, Repr

/-- Initializes the interpreter with zero work and the base wires `List.range base`. -/
def initState (base : ℕ) : RunState :=
  ⟨Account.initAccount base, List.range base⟩

/-- Updates the live-wire list by adding an allocated wire or erasing a released wire; other
steps leave it unchanged. -/
def applyLive (live : List ℕ) : DynStep → List ℕ
  | .alloc w => w :: live
  | .releaseClean w | .releaseDirty w => live.erase w
  | _ => live

/-- Executes one accounting step, updating work counters, the live-wire list, and maxima of live
and workspace sizes. -/
def step (base : ℕ) (st : RunState) (s : DynStep) : RunState :=
  let live' := applyLive st.live s
  let acc' := Account.seq st.acc s.stepAccount
  let acc'' :=
    { acc' with
      livePeak := max acc'.livePeak live'.length
      peakWorkspace := max acc'.peakWorkspace (live'.length - base) }
  ⟨acc'', live'⟩

/-- Folds the accounting interpreter over a dynamic word from its base initial state. -/
def runTrace (base : ℕ) (ops : List DynStep) : RunState :=
  ops.foldl (step base) (initState base)

/-- Folds the accounting interpreter over a dynamic word from a supplied state. -/
def runFrom (base : ℕ) (st : RunState) (ops : List DynStep) : RunState :=
  ops.foldl (step base) st

/-- The accumulated resource account produced by `runTrace`. -/
def account (base : ℕ) (ops : List DynStep) : Account :=
  (runTrace base ops).acc

/-- The final live-wire list produced by `runTrace`. -/
def finalLive (base : ℕ) (ops : List DynStep) : List ℕ :=
  (runTrace base ops).live

/-- Requires the final live-wire list to equal the initial base-wire list. -/
def balanced (base : ℕ) (ops : List DynStep) : Prop :=
  finalLive base ops = List.range base

/-- Checks allocation freshness and live-workspace requirements recursively through a dynamic
word. -/
def legalOps (base : ℕ) : List DynStep → List ℕ → Bool
  | [], _ => true
  | .alloc w :: rest, live =>
      decide (base ≤ w) && !(live.contains w) && legalOps base rest (w :: live)
  | .releaseClean w :: rest, live =>
      decide (base ≤ w && live.contains w) && legalOps base rest (live.erase w)
  | .releaseDirty w :: rest, live =>
      decide (base ≤ w && live.contains w) && legalOps base rest (live.erase w)
  | .reset w :: rest, live =>
      decide (base ≤ w && live.contains w) && legalOps base rest live
  | .uncompute w :: rest, live =>
      decide (base ≤ w && live.contains w) && legalOps base rest live
  | .oracle _ ws :: rest, live =>
      decide (ws.all (fun w => base ≤ w && live.contains w)) && legalOps base rest live
  | .macro _ :: rest, live => legalOps base rest live
  | .evolve _ :: rest, live => legalOps base rest live
  | .classical _ :: rest, live => legalOps base rest live

/-- Checks a dynamic word for legality starting from the base-wire list. -/
def legal (base : ℕ) (ops : List DynStep) : Bool :=
  legalOps base ops (List.range base)

/-- Folds only the live-wire updates through a dynamic word. -/
def liveAfter (live : List ℕ) (ops : List DynStep) : List ℕ :=
  ops.foldl applyLive live

/-- An execution outcome carrying a completed value, a value with a branch flag, a timeout, or
nontermination. -/
inductive Outcome (α : Type*) where
  | done (value : α)
  | branch (taken : Bool) (value : α)
  | timeout
  | never

/-- Attaches or replaces a branch flag on a value-bearing outcome, preserving timeout and
nontermination. -/
def Outcome.branchMap {α : Type*} : Outcome α → Bool → Outcome α
  | .done a, b => .branch b a
  | .branch _ a, b => .branch b a
  | .timeout, _ => .timeout
  | .never, _ => .never

/-- Sequences value-bearing outcomes through a continuation, propagating branch flags and
preserving timeout or nontermination. -/
def Outcome.bind {α β : Type*} : Outcome α → (α → Outcome β) → Outcome β
  | .done a, f => f a
  | .branch b a, f => (f a).branchMap b
  | .timeout, _ => .timeout
  | .never, _ => .never

/-- Extracts the account from a completed or branch outcome, returning the zero account for
timeout or nontermination. -/
def Outcome.accountOf : Outcome Account → Account
  | .done a | .branch _ a => a
  | .timeout | .never => Account.zero

/-- Translates fresh-copy costs into an account using bit queries, gate counts, summed operation
depth, fresh and clean peaks, and discard charges. -/
noncomputable def Account.ofFreshCost (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : Account :=
  ⟨c.bitQueries, 0, 0, c.fixedMacros, c.localGates,
    c.copies + c.partialSwaps + c.localGates + c.fixedMacros + c.discards + c.bitQueries,
    max c.peakFreshRegisters c.peakCleanQubits,
    c.peakFreshRegisters + c.peakCleanQubits, c.discards, 0⟩

/-- Accumulates the sequential fresh-copy cost of an operation list. -/
noncomputable def freshWordCost {n M : ℕ} :
    List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M) → Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost
  | [] => Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost
  | op :: ops => Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost op) (freshWordCost ops)

/-- Charges one `freshCost 0 0` for each operator-angle pair in a plain fresh-copy word. -/
noncomputable def freshPlainCost {D : ℕ} :
    List (Operator D × ℝ) → Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost
  | [] => Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost
  | _p :: ops => Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost 0 0) (freshPlainCost ops)

/-- Records a circuit's query count, gate count, and size as an account, using the gate count
for both macro and basic gates. -/
def Account.ofCircuit {I : Type*} (C : Circuit I) : Account :=
  ⟨QueryCount C, 0, 0, GateCount C, GateCount C, Size C, 0, 0, 0, 0⟩

/-- A task specification consisting of a legal-input predicate and an acceptable-output
relation. -/
structure TaskSpec (Inst Out : Type*) where

  legal : Inst → Prop

  ok : Inst → Out → Prop

/-- An input-indexed computation returning an outcome containing an output and a resource
account. -/
abbrev Gen (Inst Out : Type*) := Inst → Outcome (Out × Account)

/-- Requires two legal inputs for which no output is acceptable for both. -/
def TaskSpec.nontrivial {Inst Out : Type*} (T : TaskSpec Inst Out) : Prop :=
  ∃ i j : Inst, T.legal i ∧ T.legal j ∧ (∀ o : Out, ¬(T.ok i o ∧ T.ok j o))

/-- Requires every legal input to return a completed acceptable output with some resource
account. -/
def Correct {Inst Out : Type*} (T : TaskSpec Inst Out) (G : Gen Inst Out) : Prop :=
  ∀ i : Inst, T.legal i → ∃ o acc, G i = .done (o, acc) ∧ T.ok i o

/-- Requires every legal input to return a completed acceptable output with a resource account
componentwise bounded by `B`. -/
def Implements {Inst Out : Type*} (T : TaskSpec Inst Out) (G : Gen Inst Out)
    (B : Account) : Prop :=
  ∀ i : Inst, T.legal i →
    ∃ o acc, G i = .done (o, acc) ∧ T.ok i o ∧ accountLE acc B

/-- Requires a correct generator whose total forward and adjoint queries are bounded by `c *
work i` on every legal input. -/
def QueryUpper {Inst Out : Type*} (T : TaskSpec Inst Out) (work : Inst → ℕ)
    (c : ℕ) : Prop :=
  ∃ G : Gen Inst Out, Correct T G ∧
    ∀ i acc o, T.legal i → G i = .done (o, acc) →
      acc.queries + acc.adjointQueries ≤ c * work i

/-- Requires every correct program in the supplied execution model to have a legal input whose
completed runs use at least `c * work i` total queries. -/
def QueryLower {Inst Out Prog : Type*} (runProg : Prog → Gen Inst Out)
    (T : TaskSpec Inst Out) (work : Inst → ℕ) (c : ℕ) : Prop :=
  ∀ P : Prog, Correct T (runProg P) →
    ∃ i : Inst, T.legal i ∧ ∀ o acc, runProg P i = .done (o, acc) →
      c * work i ≤ acc.queries + acc.adjointQueries

/-- The task of returning the marked register together with a real value at least `1 - 1 / card
(Reg n)`. -/
def singletonSearchTask (n : ℕ) : TaskSpec (Reg n) (Reg n × ℝ) :=
  ⟨fun _ => True, fun x yr => yr.1 = x ∧
    1 - 1 / (Fintype.card (Reg n) : ℝ) ≤ yr.2⟩

/-- Returns the marked register and its measured Grover-search success probability, together
with the account of the workspace Grover circuit. -/
noncomputable def searchGen (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (w : W) :
    Gen (Reg n) (Reg n × ℝ) :=
  fun x =>
    let C := workspaceGroverCircuit (W := W) n (singletonSearchIterations n)
    .done ((x, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          C (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) x)),
      Account.ofCircuit C)

/-- The real-valued indicator that a Boolean function has an odd number of true entries. -/
def parityIndicator {I : Type} [Fintype I] (f : I → Bool) : ℝ :=
  if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0

/-- The task of approximating `parityIndicator` within `1 / 3` on every Boolean input function. -/
def parityTask (I : Type) [Fintype I] : TaskSpec (I → Bool) ℝ :=
  ⟨fun _ => True, fun f p => |p - parityIndicator f| ≤ 1 / 3⟩

/-- A unitary query circuit with a normalized input state and an acceptance event whose
probability approximates parity within `1 / 3` for every oracle. -/
structure ParityProgram (I W : Type) [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] where

  circuit : Circuit (PolynomialWorkspace I W)

  psi : QState (PolynomialWorkspace I W)

  accept : Finset (PolynomialWorkspace I W)

  unitary : IsUnitaryCircuit circuit

  normalized : Normalized psi

  approx : ∀ f : I → Bool,
    |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) circuit psi) accept
      - parityIndicator f| ≤ 1 / 3

/-- Runs a parity program against the workspace bit oracle and returns its acceptance
probability with its circuit account. -/
noncomputable def parityGen {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] : ParityProgram I W → Gen (I → Bool) ℝ
  | P => fun f =>
    .done (MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) P.circuit P.psi) P.accept,
      Account.ofCircuit P.circuit)

/-- The eventual inequality `|f x| ≤ c * |g x|` along the filter `F`. -/
def BigOWith {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ) : Prop :=
  F.Eventually (fun x => |f x| ≤ c * |g x|)

/-- An eventual absolute-value bound by a nonnegative constant multiple along a filter. -/
def BigO {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ BigOWith c F f g

/-- The reverse big-O relation, defined by `BigO F g f`. -/
def BigOmega {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  BigO F g f

/-- The conjunction of big-O and big-Omega bounds along a filter. -/
def BigTheta {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  BigO F f g ∧ BigOmega F f g

/-- The filter `atTop` on natural input sizes. -/
def sizeFilter : Filter ℕ := Filter.atTop

/-- The filter `atTop` on real precision-growth parameters. -/
def precFilter : Filter ℝ := Filter.atTop

/-- The function `E ↦ (log E) ^ k`. -/
noncomputable def polylog (k : ℕ) (E : ℝ) : ℝ := (Real.log E) ^ k

/-- A finite gate-code word certified to be legal on `n` wires. -/
structure SynthCertificate (n : ℕ) where

  word : List FiniteGateCode

  legalWord : finiteWordLegal n word = true

/-- A real-valued gate budget depending on a natural size and a real precision parameter. -/
abbrev GateBudget := ℕ → ℝ → ℝ

/-- A real-valued bit-time budget depending on a natural size and a real precision parameter. -/
abbrev BitTimeBudget := ℕ → ℝ → ℝ

/-- Natural-number parameters for representation bits, work-tape space, and auxiliary bits. -/
structure LowerPremises where

  reprBits : ℕ

  workTape : ℕ

  auxBits : ℕ
  deriving DecidableEq, Repr

/-- The sum of the complex norms of a finite vector's entries. -/
noncomputable def vnorm {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i : Fin n, ‖v i‖

/-- Requires a matrix to be nonexpansive for the vector norm `vnorm`. -/
def Nonexpansive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ v : Fin n → ℂ, vnorm (A.mulVec v) ≤ vnorm v

/-- Requires the difference of two matrices to expand `vnorm` by at most the factor `ε` on every
vector. -/
def RefBounded {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : Prop :=
  ∀ v : Fin n → ℂ, vnorm ((A - B).mulVec v) ≤ ε * vnorm v

/-- The account charging LCU-QSVT synthesis and Jacobi-Anger truncation operation counts to
basic gates and depth, and truncation operations to macro gates. -/
def lqAccount (n q : ℕ) : Account :=
  { Account.zero with
    basicGates := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q
    macroGates := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q
    depth := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q }

/-- The account with `prep + trial` classical bits and depth two, all other fields being zero. -/
def stoppingAccount (prep trial : ℕ) : Account :=
  { Account.zero with classicalBits := prep + trial, depth := 2 }

/-- Collects resource-account algebra, interpreter counter identities, repetition and fresh-copy
compilation counts, execution-cost identities, and outcome sequencing laws. -/
def Clause1Claim : Prop :=

  (∀ base : ℕ, account base [] = Account.initAccount base) ∧
  (account 0 [] = Account.zero) ∧

  (∀ (base : ℕ) (ops : List DynStep), (account base ops).queries = (counters ops).queries) ∧
  (∀ (base : ℕ) (ops : List DynStep),
      (account base ops).adjointQueries = (counters ops).adjointQueries) ∧
  (∀ (base : ℕ) (ops : List DynStep),
      (account base ops).hamiltonianCount = (counters ops).hamiltonianCount) ∧
  (∀ (base : ℕ) (ops : List DynStep), (account base ops).macroGates = (counters ops).macroGates) ∧
  (∀ (base : ℕ) (ops : List DynStep), (account base ops).basicGates = (counters ops).basicGates) ∧
  (∀ (base : ℕ) (ops : List DynStep), (account base ops).depth = (counters ops).depth) ∧
  (∀ (base : ℕ) (ops : List DynStep),
      (account base ops).classicalBits = (counters ops).classicalBits) ∧
  (∀ (base : ℕ) (ops : List DynStep),
      (account base ops).hamiltonianTicks = (counters ops).hamiltonianTicks) ∧

  (∀ g : FiniteGateCode, ((DynStep.macro g).stepAccount).basicGates = 1 ∧
      ((DynStep.macro g).stepAccount).macroGates = 1) ∧
  (∀ s : DynStep, (profileOf s).basicGates = s.stepAccount.basicGates ∧
      (profileOf s).classicalBits = s.stepAccount.classicalBits) ∧

  (∀ (a b : List DynStep), counters (a ++ b) = Account.seq (counters a) (counters b)) ∧
  (∀ (base : ℕ) (a b : List DynStep),
      runTrace base (a ++ b) = runFrom base (runTrace base a) b) ∧

  (∀ (a : Account) (k : ℕ), (Account.repeat a k).queries = k * a.queries) ∧
  (∀ (s : List DynStep) (k : ℕ),
      counters (repeatWord s k) = Account.repeat (counters s) k) ∧

  (∀ (a b : Account), Account.par a b = Account.par b a) ∧
  (∀ (a b c : Account), Account.par (Account.par a b) c = Account.par a (Account.par b c)) ∧
  (∀ (a : Account), Account.par Account.zero a = a) ∧
  (∀ (a : Account), Account.seq Account.zero a = a ∧ Account.seq a Account.zero = a) ∧
  (∀ (a b c : Account),
      Account.seq (Account.seq a b) c = Account.seq a (Account.seq b c)) ∧

  (∀ {n M : ℕ} (s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M s ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M s ρ C)).copies = s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M s ρ C)).discards = s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileDirect n M s ρ C)).bitQueries = 0) ∧
  (∀ {n M : ℕ} (s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).copies = s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).discards = s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileLocal n M s ρ C)).bitQueries = 0) ∧
  (∀ {n M : ℕ} (b k : ℕ) (ρ : Operator (2^n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).fixedMacros = GateCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).copies =
        2 ^ b * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).discards =
        2 ^ b * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileNumeric n M b k ρ C)).bitQueries = 0) ∧
  (∀ {n M : ℕ} (s : ℕ) (ρ σ : Operator (2^n)) (C : Circuit (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Register n M)),
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M s ρ σ C)).fixedMacros = GateCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M s ρ σ C)).copies = 2 * s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M s ρ σ C)).discards = 2 * s * QueryCount C ∧
      (freshWordCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.compileTwo n M s ρ σ C)).bitQueries = 0) ∧
  (∀ {D : ℕ} (ops : List (Operator D × ℝ)) (X : Operator D),
      (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain ops X).2.copies = ops.length ∧
      (Qatlib.Concepts.FreshCopyExec.QpeConsumers.runPlain ops X).2 = freshPlainCost ops) ∧

  (∀ {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M)) (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M),
      (Qatlib.Concepts.FreshCopyExec.QpeConsumers.run ops X).2 = freshWordCost ops) ∧

  (∀ {α : Type*} (a : α),
      Outcome.bind (.done a) (fun _ => (.never : Outcome α)) = .never) ∧
  (∀ {α β : Type*},
      Outcome.bind (.timeout : Outcome α) (fun _ : α => (.never : Outcome β))
        = (.timeout : Outcome β)) ∧
  (∀ {α β γ : Type*} (o : Outcome α) (f : α → Outcome β) (g : β → Outcome γ),
      Outcome.bind (Outcome.bind o f) g = Outcome.bind o (fun x => Outcome.bind (f x) g)) ∧

  (∀ a b : Account, (Account.seq a b).toResourceCost = a.toResourceCost + b.toResourceCost) ∧
  (Account.zero.toResourceCost = (0 : ResourceCost)) ∧
  (∀ {I : Type*} (C : Circuit I),
      (Account.ofCircuit C).toResourceCost.queries = QueryCount C ∧
      (Account.ofCircuit C).toResourceCost.macroGates = GateCount C ∧
      (Account.ofCircuit C).toResourceCost.depth = Size C)

/-- Collects impossibility results for nonterminating, timed-out, or constant-output
implementations, circuit-count identities, search correctness, and a parity query lower
bound. -/
def Clause2Claim : Prop :=

  (∀ {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account) (i : Inst),
      T.legal i → ¬Implements T (fun _ => (.never : Outcome (Out × Account))) B) ∧
  (∀ {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account),
      T.nontrivial →
        ¬Implements T (fun _ => (.timeout : Outcome (Out × Account))) B) ∧

  (∀ {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account) (o0 : Out)
      (K : Inst → Account), T.nontrivial →
        ¬Implements T (fun i => .done (o0, K i)) B) ∧

  (∀ {I : Type*} (C : Circuit I),
      (Account.ofCircuit C).queries = QueryCount C ∧
      (Account.ofCircuit C).macroGates = GateCount C ∧
      (Account.ofCircuit C).depth = Size C) ∧

  (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (w : W) (_hn : 2 ≤ n),
      Correct (singletonSearchTask n) (searchGen n W w) ∧
        QueryUpper (singletonSearchTask n) (fun _ => 2 ^ n) 1) ∧

  (∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W],
      QueryLower (parityGen : ParityProgram I W → Gen (I → Bool) ℝ) (parityTask I)
        (fun _ => Fintype.card I / 2) 1)

/-- Collects big-O and big-Theta laws, polylogarithmic synthesis and bit-cost bounds, and the
construction of lower-bound premise records. -/
def Clause3Claim : Prop :=

  (∀ {α : Type*} (F : Filter α) (f : α → ℝ), BigO F f f) ∧
  (∀ {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ), BigOWith c F f g →
      BigOWith (|c|) F f g) ∧
  (∀ {α : Type*} (F : Filter α) (f g h : α → ℝ),
      BigO F f g → BigO F g h → BigO F f h) ∧
  (∀ {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ),
      0 ≤ c → BigO F f g → BigO F (fun x => c * f x) g) ∧
  (∀ {α : Type*} (F : Filter α) (f g : α → ℝ),
      BigTheta F f g ↔ (BigO F f g ∧ BigO F g f)) ∧
  (∀ (k : ℕ), BigO precFilter (polylog k) (polylog (k + 1))) ∧

  (∀ (k c : ℕ) (n : ℕ) (wordLen : GateBudget)
      (_cert : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n,
        0 ≤ wordLen n E ∧ wordLen n E ≤ c * polylog k E ∧ finiteWordLegal n s.word = true),
      BigO precFilter (fun E => wordLen n E) (polylog k)) ∧

  (∀ (k c bitCost n : ℕ) (wordLen : GateBudget)
      (_hbound : ∀ E : ℝ, 1 ≤ E → |wordLen n E| ≤ c * polylog k E),
      BigO precFilter (fun E => (bitCost : ℝ) * wordLen n E) (polylog k)) ∧

  (∀ (repr work aux : ℕ),
      (∃ p : LowerPremises, p.reprBits = repr ∧ p.workTape = work ∧ p.auxBits = aux)) ∧
  (∀ (k : ℕ) (bitCost : ℕ), 1 ≤ bitCost →
      BigTheta precFilter (fun E => (bitCost : ℝ) * polylog k E) (polylog k))

/-- Collects balanced-trace reordering laws, composition of `RefBounded` errors, LCU-QSVT and
stopping accounts, and an example separating word length from peak space. -/
def Clause4Claim : Prop :=

  (∀ base : ℕ, balanced base []) ∧

  (∀ (base : ℕ) (a b : List DynStep),
      (account base (a ++ b)).queries = (account base (b ++ a)).queries ∧
      (account base (a ++ b)).adjointQueries = (account base (b ++ a)).adjointQueries ∧
      (account base (a ++ b)).hamiltonianCount = (account base (b ++ a)).hamiltonianCount ∧
      (account base (a ++ b)).macroGates = (account base (b ++ a)).macroGates ∧
      (account base (a ++ b)).basicGates = (account base (b ++ a)).basicGates ∧
      (account base (a ++ b)).depth = (account base (b ++ a)).depth ∧
      (account base (a ++ b)).classicalBits = (account base (b ++ a)).classicalBits ∧
      (account base (a ++ b)).hamiltonianTicks = (account base (b ++ a)).hamiltonianTicks) ∧
  (∀ (base : ℕ) (a b : List DynStep),
      balanced base a → balanced base b →
        (account base (a ++ b)).livePeak = (account base (b ++ a)).livePeak ∧
        (account base (a ++ b)).peakWorkspace = (account base (b ++ a)).peakWorkspace ∧
        finalLive base (a ++ b) = finalLive base (b ++ a)) ∧

  (∀ (d r : ℕ) (A A' B B' : Matrix (Fin (d * r)) (Fin (d * r)) ℂ) (εA εB : ℝ),
      0 ≤ εA → 0 ≤ εB →
        Nonexpansive A → Nonexpansive B' →
          RefBounded A A' εA → RefBounded B B' εB →
            RefBounded (A * B) (A' * B') (εA + εB)) ∧

  (∀ (n q : ℕ),
      (lqAccount n q).basicGates = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q ∧
      (lqAccount n q).queries = 0 ∧ (lqAccount n q).adjointQueries = 0 ∧
      (lqAccount n q).hamiltonianCount = 0 ∧ (lqAccount n q).livePeak = 0) ∧

  (∀ (prep trial : ℕ),
      (stoppingAccount prep trial).classicalBits = prep + trial ∧
      (Account.seq (stoppingAccount 2 3) (stoppingAccount 2 3)).classicalBits = 10 ∧
      weightedExpectedCost alternatingRetryKernel alternatingRetryCost (.inr false) = 10) ∧

  (∃ (a b : List DynStep),
      b.length < a.length ∧ (account 0 a).livePeak < (account 0 b).livePeak)

end Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
