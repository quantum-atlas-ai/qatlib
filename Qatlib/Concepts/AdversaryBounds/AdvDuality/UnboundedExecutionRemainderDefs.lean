/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped ENNReal
abbrev SamplerRecord (N : ℕ) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ

structure CappedFeedback (D N : ℕ) where
  first : ObservedCircuit (Fin D)
  weights : Fin (observedLeafCount first) → Fin N → ℕ
  width : Fin (observedLeafCount first) → ℕ
  next : Fin (observedLeafCount first) → SamplerRecord N → ObservedCircuit (Fin D)

namespace CappedFeedback
variable {D N : ℕ}
def compile (M : CappedFeedback D N) (cap : ℕ) : FairFeedback D (SamplerRecord N) where
  first := M.first
  choose i := weightedSampler (M.weights i) (M.width i) cap
  next := M.next

def Legal (M : CappedFeedback D N) : Prop :=
  observedWellFormed M.first ∧ ∀ i a, observedWellFormed (M.next i a)

noncomputable def instrument (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) :=
  (M.compile cap).instrument O hO hM

noncomputable def timeoutMass (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
    (if rejectionOutcome (((M.compile cap).record O z).value.1) = .inr () then 1 else 0))

noncomputable def expectedReadCost (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
    (((M.compile cap).record O z).coinWord.length : ℝ))

noncomputable def neverMass (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ⨅ cap, M.timeoutMass cap O hO hM ρ

noncomputable def limitingReadCost (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ∑ i : Fin (observedLeafCount M.first),
    ENNReal.ofReal (instrumentProb (observedInstrument O hO M.first hM.1) ρ i) *
      ((M.width i : ℝ≥0∞) / (1 - rationalRejectMass (M.weights i) (M.width i)))

end CappedFeedback

noncomputable def rejectingFeedback : CappedFeedback 2 2 where
  first := measuredFeedbackFirst
  weights i j := if i.val = 0 then (if j = 0 then 1 else 0) else (if j = 0 then 1 else 2)
  width i := if i.val = 0 then 0 else 2
  next i a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => measuredFeedbackNext i (some j, 0)

def rejectingPending : (rejectingFeedback.compile 1).Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

def rejectingRecovered : (rejectingFeedback.compile 2).Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

namespace NativeTape

inductive Command (Γ Λ : Type)
  | halt
  | det (next : Λ) (stmt : Turing.TM0.Stmt Γ)
  | coin (next : Bool → Λ × Turing.TM0.Stmt Γ)

abbrev Program (Γ Λ : Type) := Λ → Γ → Command Γ Λ

def statementDisplacement {Γ : Type} : Turing.TM0.Stmt Γ → ℤ
  | .write _ => 0
  | .move .left => -1
  | .move .right => 1

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

def table (M : Program Γ Λ) (bit : Bool) : Turing.TM0.Machine Γ Λ := fun q a =>
  match M q a with
  | .halt => none
  | .det q' s => some (q', s)
  | .coin k => some (k bit)

def advance (cfg : Turing.TM0.Cfg Γ Λ) (p : Λ × Turing.TM0.Stmt Γ) : Turing.TM0.Cfg Γ Λ :=
  ⟨p.1, TM0StmtApply cfg.Tape p.2⟩

inductive Stop
  | halted | fuel | needBits
  deriving DecidableEq, Repr

abbrev Tick (Γ Λ : Type) [Inhabited Γ] := Turing.TM0.Cfg Γ Λ × Option Bool

def tickDisplacement {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Program Γ Λ) (e : Tick Γ Λ) : ℤ :=
  match table M (e.2.getD false) e.1.q e.1.Tape.head with
  | none => 0
  | some p => statementDisplacement p.2

def cursorTrace {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Program Γ Λ) (p : ℤ) (es : List (Tick Γ Λ)) : List ℤ :=
  es.scanl (fun i e => i+tickDisplacement M e) p
structure Result (Γ Λ : Type) [Inhabited Γ] where
  cfg : Turing.TM0.Cfg Γ Λ
  unread : List Bool
  stop : Stop
  trace : List (Tick Γ Λ)

def Result.prepend (e : Tick Γ Λ) (r : Result Γ Λ) : Result Γ Λ :=
  { r with trace := e :: r.trace }

def Result.steps (r : Result Γ Λ) : ℕ := r.trace.length

def Result.bits (r : Result Γ Λ) : List Bool := r.trace.filterMap Prod.snd

def Result.observe (r : Result Γ Λ) :
    Turing.TM0.Cfg Γ Λ × Stop × List Bool × List Bool × ℕ :=
  (r.cfg, r.stop, r.unread, r.bits, r.steps)

def run (M : Program Γ Λ) : ℕ → List Bool → Turing.TM0.Cfg Γ Λ → Result Γ Λ
  | 0, bits, cfg => match M cfg.q cfg.Tape.head with
    | .halt => ⟨cfg, bits, .halted, []⟩
    | _ => ⟨cfg, bits, .fuel, []⟩
  | n+1, bits, cfg => match M cfg.q cfg.Tape.head with
    | .halt => ⟨cfg, bits, .halted, []⟩
    | .det q' s => (run M n bits (advance cfg (q', s))).prepend (cfg, none)
    | .coin k => match bits with
      | [] => ⟨cfg, [], .needBits, []⟩
      | b :: bs => (run M n bs (advance cfg (k b))).prepend (cfg, some b)

noncomputable def law (M : Program Γ Λ) : ℕ → Turing.TM0.Cfg Γ Λ → PMF (Result Γ Λ)
  | 0, cfg => match M cfg.q cfg.Tape.head with
    | .halt => PMF.pure ⟨cfg, [], .halted, []⟩
    | _ => PMF.pure ⟨cfg, [], .fuel, []⟩
  | n+1, cfg => match M cfg.q cfg.Tape.head with
    | .halt => PMF.pure ⟨cfg, [], .halted, []⟩
    | .det q' s => (law M n (advance cfg (q', s))).map (Result.prepend (cfg, none))
    | .coin k => (PMF.uniformOfFintype' Bool).bind fun b =>
      (law M n (advance cfg (k b))).map (Result.prepend (cfg, some b))

def Result.appendTrace (es : List (Tick Γ Λ)) (r : Result Γ Λ) : Result Γ Λ :=
  {r with trace := es++r.trace}

noncomputable def continueLaw (M : Program Γ Λ) (m : ℕ) (r : Result Γ Λ) : PMF (Result Γ Λ) :=
  if r.stop = .fuel then (law M m r.cfg).map (Result.appendTrace r.trace) else PMF.pure r

def truncate (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) : Result Γ Λ :=
  {run M n r.bits cfg with unread := []}

noncomputable def finishedMass (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) : ℝ≥0∞ := if r.stop = .halted then law M n cfg r else 0

noncomputable def haltedMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) : ℝ≥0∞ := ⨆ n, finishedMass M n cfg r

noncomputable def neverMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : ℝ≥0∞ :=
  1 - ∑' r, haltedMass M cfg r

noncomputable def terminalMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : Option (Result Γ Λ) → ℝ≥0∞
  | none => neverMass M cfg
  | some r => haltedMass M cfg r

def Step (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (b : Option Bool)
    (next : Turing.TM0.Cfg Γ Λ) : Prop :=
  (match M cfg.q cfg.Tape.head, b with
    | .det _ _, none => True
    | .coin _, some _ => True
    | _, _ => False) ∧
  Turing.TM0.step (table M (b.getD false)) cfg = some next

inductive Path (M : Program Γ Λ) : Turing.TM0.Cfg Γ Λ → List (Tick Γ Λ) →
    Turing.TM0.Cfg Γ Λ → Prop
  | nil (cfg) : Path M cfg [] cfg
  | cons {cfg next last b es} : Step M cfg b next → Path M next es last →
      Path M cfg ((cfg, b) :: es) last

def resume (M : Program Γ Λ) (extra : ℕ) (r : Result Γ Λ) : Result Γ Λ :=
  if r.stop = .fuel then
    let s := run M extra r.unread r.cfg
    { s with trace := r.trace ++ s.trace }
  else r

def supply (M : Program Γ Λ) (budget : ℕ) (more : List Bool) (r : Result Γ Λ) : Result Γ Λ :=
  if r.stop = .needBits then
    let s := run M (budget-r.steps) (r.unread ++ more) r.cfg
    { s with trace := r.trace ++ s.trace }
  else { r with unread := r.unread ++ more }

def spin : Program Γ Unit := fun _ _ => .det () (.move .right)

end NativeTape

end Qatlib.Concepts.AdversaryBounds.AdvDuality
