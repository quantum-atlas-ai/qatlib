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
set_option warningAsError false
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

def Account.zero : Account :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def Account.initAccount (base : ℕ) : Account :=
  { Account.zero with livePeak := base }

def Account.seq (a b : Account) : Account :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth, max a.livePeak b.livePeak,
    max a.peakWorkspace b.peakWorkspace, a.classicalBits + b.classicalBits,
    a.hamiltonianTicks + b.hamiltonianTicks⟩

def Account.par (a b : Account) : Account :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth, a.livePeak + b.livePeak,
    a.peakWorkspace + b.peakWorkspace, a.classicalBits + b.classicalBits,
    a.hamiltonianTicks + b.hamiltonianTicks⟩

def Account.repeat (a : Account) : ℕ → Account
  | 0 => Account.zero
  | k + 1 => Account.seq a (Account.repeat a k)

def accountLE (a b : Account) : Prop :=
  a.queries ≤ b.queries ∧ a.adjointQueries ≤ b.adjointQueries ∧
    a.hamiltonianCount ≤ b.hamiltonianCount ∧ a.macroGates ≤ b.macroGates ∧
    a.basicGates ≤ b.basicGates ∧ a.depth ≤ b.depth ∧ a.livePeak ≤ b.livePeak ∧
    a.peakWorkspace ≤ b.peakWorkspace ∧ a.classicalBits ≤ b.classicalBits ∧
    a.hamiltonianTicks ≤ b.hamiltonianTicks

@[simp] theorem accountLE_zero (a : Account) : accountLE Account.zero a :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

@[simp] theorem accountLE_refl (a : Account) : accountLE a a :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _,
    le_refl _, le_refl _, le_refl _⟩

theorem accountLE_trans {a b c : Account} (hab : accountLE a b) (hbc : accountLE b c) :
    accountLE a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.1.trans hbc.2.2.1,
    hab.2.2.2.1.trans hbc.2.2.2.1, hab.2.2.2.2.1.trans hbc.2.2.2.2.1,
    hab.2.2.2.2.2.1.trans hbc.2.2.2.2.2.1, hab.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.2.1.trans hbc.2.2.2.2.2.2.2.2.1,
    hab.2.2.2.2.2.2.2.2.2.trans hbc.2.2.2.2.2.2.2.2.2⟩

def Account.toResourceCost (a : Account) : ResourceCost :=
  ⟨a.queries + a.adjointQueries, a.macroGates, a.basicGates, a.depth, a.livePeak,
    (a.hamiltonianTicks : ℝ≥0∞), a.classicalBits⟩

@[simp] theorem toResourceCost_queries (a : Account) :
    a.toResourceCost.queries = a.queries + a.adjointQueries := rfl

@[simp] theorem toResourceCost_macroGates (a : Account) :
    a.toResourceCost.macroGates = a.macroGates := rfl

@[simp] theorem toResourceCost_basicGates (a : Account) :
    a.toResourceCost.basicGates = a.basicGates := rfl

@[simp] theorem toResourceCost_depth (a : Account) :
    a.toResourceCost.depth = a.depth := rfl

@[simp] theorem toResourceCost_peakSpace (a : Account) :
    a.toResourceCost.peakSpace = a.livePeak := rfl

@[simp] theorem toResourceCost_hamiltonianTime (a : Account) :
    a.toResourceCost.hamiltonianTime = a.hamiltonianTicks :=
  rfl

@[simp] theorem toResourceCost_classicalBits (a : Account) :
    a.toResourceCost.classicalBits = a.classicalBits := rfl

theorem toResourceCost_zero : Account.zero.toResourceCost = (0 : ResourceCost) := by
  simp only [Account.zero, Account.toResourceCost, Nat.cast_zero]
  rfl

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

def repeatWord (s : List DynStep) : ℕ → List DynStep
  | 0 => []
  | k + 1 => s ++ repeatWord s k

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

def DynStep.stepAccount : DynStep → Account
  | .oracle false _ => { Account.zero with queries := 1, depth := 1 }
  | .oracle true _ => { Account.zero with adjointQueries := 1, depth := 1 }
  | .macro _ => { Account.zero with macroGates := 1, basicGates := 1, depth := 1 }
  | .evolve t =>
      { Account.zero with hamiltonianCount := 1, hamiltonianTicks := t, depth := 1 }
  | .classical bits => { Account.zero with classicalBits := bits, depth := 1 }
  | s => { Account.zero with classicalBits := s.bitCharge, depth := 1 }

def profileOf (s : DynStep) : StepProfile :=
  ⟨s.stepAccount.basicGates, s.stepAccount.peakWorkspace,
    (s.stepAccount.hamiltonianTicks : ℝ≥0∞), s.stepAccount.classicalBits⟩

def counters : List DynStep → Account
  | [] => Account.zero
  | s :: rest => Account.seq s.stepAccount (counters rest)

structure RunState where
  acc : Account
  live : List ℕ
  deriving DecidableEq, Repr

def initState (base : ℕ) : RunState :=
  ⟨Account.initAccount base, List.range base⟩

def applyLive (live : List ℕ) : DynStep → List ℕ
  | .alloc w => w :: live
  | .releaseClean w | .releaseDirty w => live.erase w
  | _ => live

def step (base : ℕ) (st : RunState) (s : DynStep) : RunState :=
  let live' := applyLive st.live s
  let acc' := Account.seq st.acc s.stepAccount
  let acc'' :=
    { acc' with
      livePeak := max acc'.livePeak live'.length
      peakWorkspace := max acc'.peakWorkspace (live'.length - base) }
  ⟨acc'', live'⟩

def runTrace (base : ℕ) (ops : List DynStep) : RunState :=
  ops.foldl (step base) (initState base)

def runFrom (base : ℕ) (st : RunState) (ops : List DynStep) : RunState :=
  ops.foldl (step base) st

def account (base : ℕ) (ops : List DynStep) : Account :=
  (runTrace base ops).acc

def finalLive (base : ℕ) (ops : List DynStep) : List ℕ :=
  (runTrace base ops).live

def balanced (base : ℕ) (ops : List DynStep) : Prop :=
  finalLive base ops = List.range base

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

def legal (base : ℕ) (ops : List DynStep) : Bool :=
  legalOps base ops (List.range base)

def liveAfter (live : List ℕ) (ops : List DynStep) : List ℕ :=
  ops.foldl applyLive live

inductive Outcome (α : Type*) where
  | done (value : α)
  | branch (taken : Bool) (value : α)
  | timeout
  | never

def Outcome.branchMap {α : Type*} : Outcome α → Bool → Outcome α
  | .done a, b => .branch b a
  | .branch _ a, b => .branch b a
  | .timeout, _ => .timeout
  | .never, _ => .never

def Outcome.bind {α β : Type*} : Outcome α → (α → Outcome β) → Outcome β
  | .done a, f => f a
  | .branch b a, f => (f a).branchMap b
  | .timeout, _ => .timeout
  | .never, _ => .never

def Outcome.accountOf : Outcome Account → Account
  | .done a | .branch _ a => a
  | .timeout | .never => Account.zero

noncomputable def Account.ofFreshCost (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : Account :=
  ⟨c.bitQueries, 0, 0, c.fixedMacros, c.localGates,
    c.copies + c.partialSwaps + c.localGates + c.fixedMacros + c.discards + c.bitQueries,
    max c.peakFreshRegisters c.peakCleanQubits,
    c.peakFreshRegisters + c.peakCleanQubits, c.discards, 0⟩

noncomputable def freshWordCost {n M : ℕ} :
    List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M) → Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost
  | [] => Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost
  | op :: ops => Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.stepCost op) (freshWordCost ops)

noncomputable def freshPlainCost {D : ℕ} :
    List (Operator D × ℝ) → Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost
  | [] => Qatlib.Concepts.FreshCopyExec.QpeConsumers.zeroCost
  | _p :: ops => Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.freshCost 0 0) (freshPlainCost ops)

def Account.ofCircuit {I : Type*} (C : Circuit I) : Account :=
  ⟨QueryCount C, 0, 0, GateCount C, GateCount C, Size C, 0, 0, 0, 0⟩

structure TaskSpec (Inst Out : Type*) where

  legal : Inst → Prop

  ok : Inst → Out → Prop

abbrev Gen (Inst Out : Type*) := Inst → Outcome (Out × Account)

def TaskSpec.nontrivial {Inst Out : Type*} (T : TaskSpec Inst Out) : Prop :=
  ∃ i j : Inst, T.legal i ∧ T.legal j ∧ (∀ o : Out, ¬(T.ok i o ∧ T.ok j o))

def Correct {Inst Out : Type*} (T : TaskSpec Inst Out) (G : Gen Inst Out) : Prop :=
  ∀ i : Inst, T.legal i → ∃ o acc, G i = .done (o, acc) ∧ T.ok i o

def Implements {Inst Out : Type*} (T : TaskSpec Inst Out) (G : Gen Inst Out)
    (B : Account) : Prop :=
  ∀ i : Inst, T.legal i →
    ∃ o acc, G i = .done (o, acc) ∧ T.ok i o ∧ accountLE acc B

def QueryUpper {Inst Out : Type*} (T : TaskSpec Inst Out) (work : Inst → ℕ)
    (c : ℕ) : Prop :=
  ∃ G : Gen Inst Out, Correct T G ∧
    ∀ i acc o, T.legal i → G i = .done (o, acc) →
      acc.queries + acc.adjointQueries ≤ c * work i

def QueryLower {Inst Out Prog : Type*} (runProg : Prog → Gen Inst Out)
    (T : TaskSpec Inst Out) (work : Inst → ℕ) (c : ℕ) : Prop :=
  ∀ P : Prog, Correct T (runProg P) →
    ∃ i : Inst, T.legal i ∧ ∀ o acc, runProg P i = .done (o, acc) →
      c * work i ≤ acc.queries + acc.adjointQueries

def singletonSearchTask (n : ℕ) : TaskSpec (Reg n) (Reg n × ℝ) :=
  ⟨fun _ => True, fun x yr => yr.1 = x ∧
    1 - 1 / (Fintype.card (Reg n) : ℝ) ≤ yr.2⟩

noncomputable def searchGen (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (w : W) :
    Gen (Reg n) (Reg n × ℝ) :=
  fun x =>
    let C := workspaceGroverCircuit (W := W) n (singletonSearchIterations n)
    .done ((x, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          C (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) x)),
      Account.ofCircuit C)

def parityIndicator {I : Type} [Fintype I] (f : I → Bool) : ℝ :=
  if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0

def parityTask (I : Type) [Fintype I] : TaskSpec (I → Bool) ℝ :=
  ⟨fun _ => True, fun f p => |p - parityIndicator f| ≤ 1 / 3⟩

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

noncomputable def parityGen {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] : ParityProgram I W → Gen (I → Bool) ℝ
  | P => fun f =>
    .done (MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) P.circuit P.psi) P.accept,
      Account.ofCircuit P.circuit)

def BigOWith {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ) : Prop :=
  F.Eventually (fun x => |f x| ≤ c * |g x|)

def BigO {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ BigOWith c F f g

def BigOmega {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  BigO F g f

def BigTheta {α : Type*} (F : Filter α) (f g : α → ℝ) : Prop :=
  BigO F f g ∧ BigOmega F f g

def sizeFilter : Filter ℕ := Filter.atTop

def precFilter : Filter ℝ := Filter.atTop

noncomputable def polylog (k : ℕ) (E : ℝ) : ℝ := (Real.log E) ^ k

structure SynthCertificate (n : ℕ) where

  word : List FiniteGateCode

  legalWord : finiteWordLegal n word = true

abbrev GateBudget := ℕ → ℝ → ℝ

abbrev BitTimeBudget := ℕ → ℝ → ℝ

structure LowerPremises where

  reprBits : ℕ

  workTape : ℕ

  auxBits : ℕ
  deriving DecidableEq, Repr

noncomputable def vnorm {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i : Fin n, ‖v i‖

def Nonexpansive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ v : Fin n → ℂ, vnorm (A.mulVec v) ≤ vnorm v

def RefBounded {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : Prop :=
  ∀ v : Fin n → ℂ, vnorm ((A - B).mulVec v) ≤ ε * vnorm v

def lqAccount (n q : ℕ) : Account :=
  { Account.zero with
    basicGates := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q
    macroGates := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q
    depth := Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q }

def stoppingAccount (prep trial : ℕ) : Account :=
  { Account.zero with classicalBits := prep + trial, depth := 2 }

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
