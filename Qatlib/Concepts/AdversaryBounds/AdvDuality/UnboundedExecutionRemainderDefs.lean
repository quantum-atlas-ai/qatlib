/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder

/-!
# Capped feedback and native tape execution data

This module defines `CappedFeedback`, which couples an initial observed circuit to
leaf-dependent weighted rejection sampling and record-dependent continuation circuits. Its
compiled instrument, timeout mass, read cost, and candidate limiting read cost describe the
interaction between classical sampling and quantum branches. Background on the instrument
formalism appears in [Watrous2018]. The concrete `rejectingFeedback` scheme supplies pending and
recovered outcomes for later calculations.

The namespace `NativeTape` defines programs with halt, deterministic, and coin instructions,
together with explicit-bit execution, a fair-bit execution law, traces, stopping reasons, and
continuation operations. Halted-result masses and residual nontermination mass specify candidate
terminal masses. These classical machine constructions use the computational setting of
[KitaevShenVyalyi2002].

## Main statements

* `CappedFeedback.compile`: capped fair-feedback sampling.
* `CappedFeedback.timeoutMass` and `CappedFeedback.expectedReadCost`: finite-cap branch mass and
  read cost.
* `NativeTape.run` and `NativeTape.law`: explicit-bit and probabilistic bounded execution.
* `NativeTape.resume` and `NativeTape.supply`: continuation with additional fuel or random bits.
* `NativeTape.terminalMass`: masses for returned results and nontermination.

## References

* [Watrous, 2018][Watrous2018]
* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

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
/-- A capped sampler configuration or returned value, paired with its accumulated read count. -/
abbrev SamplerRecord (N : ℕ) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ

/-- A feedback scheme consisting of an observed initial circuit, leaf-dependent integer sampling
weights and bit widths, and a continuation circuit for each sampler record. -/
structure CappedFeedback (D N : ℕ) where
  first : ObservedCircuit (Fin D)
  weights : Fin (observedLeafCount first) → Fin N → ℕ
  width : Fin (observedLeafCount first) → ℕ
  next : Fin (observedLeafCount first) → SamplerRecord N → ObservedCircuit (Fin D)

namespace CappedFeedback
variable {D N : ℕ}
/-- Compile a capped feedback scheme by using a weighted rejection sampler with the given cap at
each initial circuit leaf. -/
def compile (M : CappedFeedback D N) (cap : ℕ) : FairFeedback D (SamplerRecord N) where
  first := M.first
  choose i := weightedSampler (M.weights i) (M.width i) cap
  next := M.next

/-- Require the initial observed circuit and every record-dependent continuation circuit to be
well formed. -/
def Legal (M : CappedFeedback D N) : Prop :=
  observedWellFormed M.first ∧ ∀ i a, observedWellFormed (M.next i a)

/-- The instrument of the capped feedback compilation for a unitary oracle and a legal feedback
scheme. -/
noncomputable def instrument (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) :=
  (M.compile cap).instrument O hO hM

/-- The extended nonnegative mass of compiled outcomes whose rejection sampler remains pending
at the cap. -/
noncomputable def timeoutMass (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
    (if rejectionOutcome (((M.compile cap).record O z).value.1) = .inr () then 1 else 0))

/-- The extended nonnegative instrument-weighted cost of the coin-word lengths recorded by the
capped compilation. -/
noncomputable def expectedReadCost (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
    (((M.compile cap).record O z).coinWord.length : ℝ))

/-- The infimum of timeout masses over all rejection-sampling caps. -/
noncomputable def neverMass (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ⨅ cap, M.timeoutMass cap O hO hM ρ

/-- The sum over initial circuit leaves of their nonnegative masses times the sampling width
divided by one minus the rejection mass. -/
noncomputable def limitingReadCost (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D) : ℝ≥0∞ :=
  ∑ i : Fin (observedLeafCount M.first),
    ENNReal.ofReal (instrumentProb (observedInstrument O hO M.first hM.1) ρ i) *
      ((M.width i : ℝ≥0∞) / (1 - rationalRejectMass (M.weights i) (M.width i)))

end CappedFeedback

/-- A two-dimensional feedback example whose second initial branch uses two-bit rejection
sampling with weights `1` and `2`. -/
noncomputable def rejectingFeedback : CappedFeedback 2 2 where
  first := measuredFeedbackFirst
  weights i j := if i.val = 0 then (if j = 0 then 1 else 0) else (if j = 0 then 1 else 2)
  width i := if i.val = 0 then 0 else 2
  next i a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => measuredFeedbackNext i (some j, 0)

/-- A specified outcome of the one-round rejecting feedback compilation used to witness a
pending sampler branch. -/
def rejectingPending : (rejectingFeedback.compile 1).Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

/-- A specified outcome of the two-round rejecting feedback compilation used to witness recovery
after rejection. -/
def rejectingRecovered : (rejectingFeedback.compile 2).Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

namespace NativeTape

/-- A native tape instruction that halts, performs a deterministic transition, or selects a
transition using one Boolean coin. -/
inductive Command (Γ Λ : Type)
  | halt
  | det (next : Λ) (stmt : Turing.TM0.Stmt Γ)
  | coin (next : Bool → Λ × Turing.TM0.Stmt Γ)

/-- A native tape program assigning an instruction to each control label and tape-head symbol. -/
abbrev Program (Γ Λ : Type) := Λ → Γ → Command Γ Λ

/-- The integer cursor displacement of a tape statement: zero for writing, minus one for moving
left, and one for moving right. -/
def statementDisplacement {Γ : Type} : Turing.TM0.Stmt Γ → ℤ
  | .write _ => 0
  | .move .left => -1
  | .move .right => 1

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- Interpret a native tape program as a Turing-machine table for a fixed coin bit. -/
def table (M : Program Γ Λ) (bit : Bool) : Turing.TM0.Machine Γ Λ := fun q a =>
  match M q a with
  | .halt => none
  | .det q' s => some (q', s)
  | .coin k => some (k bit)

/-- Apply a tape statement and replace the control label by the supplied successor label. -/
def advance (cfg : Turing.TM0.Cfg Γ Λ) (p : Λ × Turing.TM0.Stmt Γ) : Turing.TM0.Cfg Γ Λ :=
  ⟨p.1, TM0StmtApply cfg.Tape p.2⟩

/-- The three stopping reasons: program halting, fuel exhaustion, and insufficient random bits. -/
inductive Stop
  | halted | fuel | needBits
  deriving DecidableEq, Repr

/-- A trace entry recording the configuration before a transition and the optional coin bit
consumed by that transition. -/
abbrev Tick (Γ Λ : Type) [Inhabited Γ] := Turing.TM0.Cfg Γ Λ × Option Bool

/-- The cursor displacement of the program transition recorded by a trace entry, using `false`
as the default for an absent coin. -/
def tickDisplacement {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Program Γ Λ) (e : Tick Γ Λ) : ℤ :=
  match table M (e.2.getD false) e.1.q e.1.Tape.head with
  | none => 0
  | some p => statementDisplacement p.2

/-- Reconstruct all cursor positions by accumulating trace-entry displacements from the initial
position `p`. -/
def cursorTrace {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Program Γ Λ) (p : ℤ) (es : List (Tick Γ Λ)) : List ℤ :=
  es.scanl (fun i e => i+tickDisplacement M e) p
/-- A finite execution result containing the final configuration, unread bits, stopping reason,
and transition trace. -/
structure Result (Γ Λ : Type) [Inhabited Γ] where
  cfg : Turing.TM0.Cfg Γ Λ
  unread : List Bool
  stop : Stop
  trace : List (Tick Γ Λ)

/-- Prepend a trace entry to a result without changing its other fields. -/
def Result.prepend (e : Tick Γ Λ) (r : Result Γ Λ) : Result Γ Λ :=
  { r with trace := e :: r.trace }

/-- The number of executed transitions, measured by the trace length. -/
def Result.steps (r : Result Γ Λ) : ℕ := r.trace.length

/-- The list of coin bits recorded in the execution trace, omitting deterministic transitions. -/
def Result.bits (r : Result Γ Λ) : List Bool := r.trace.filterMap Prod.snd

/-- Observe the final configuration, stopping reason, unread bits, consumed bits, and transition
count of a result. -/
def Result.observe (r : Result Γ Λ) :
    Turing.TM0.Cfg Γ Λ × Stop × List Bool × List Bool × ℕ :=
  (r.cfg, r.stop, r.unread, r.bits, r.steps)

/-- Execute a native tape program with bounded fuel and an explicit coin list, consuming bits
only at coin instructions and recording every transition. -/
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

/-- The bounded execution law obtained by sampling an independent uniform Boolean bit at each
coin instruction and recording the transition trace. -/
noncomputable def law (M : Program Γ Λ) : ℕ → Turing.TM0.Cfg Γ Λ → PMF (Result Γ Λ)
  | 0, cfg => match M cfg.q cfg.Tape.head with
    | .halt => PMF.pure ⟨cfg, [], .halted, []⟩
    | _ => PMF.pure ⟨cfg, [], .fuel, []⟩
  | n+1, cfg => match M cfg.q cfg.Tape.head with
    | .halt => PMF.pure ⟨cfg, [], .halted, []⟩
    | .det q' s => (law M n (advance cfg (q', s))).map (Result.prepend (cfg, none))
    | .coin k => (PMF.uniformOfFintype' Bool).bind fun b =>
      (law M n (advance cfg (k b))).map (Result.prepend (cfg, some b))

/-- Prepend a list of trace entries to the result's existing trace. -/
def Result.appendTrace (es : List (Tick Γ Λ)) (r : Result Γ Λ) : Result Γ Λ :=
  {r with trace := es++r.trace}

/-- Continue the random execution law for `m` more transitions only after fuel exhaustion,
preserving the accumulated trace. -/
noncomputable def continueLaw (M : Program Γ Λ) (m : ℕ) (r : Result Γ Λ) : PMF (Result Γ Λ) :=
  if r.stop = .fuel then (law M m r.cfg).map (Result.appendTrace r.trace) else PMF.pure r

/-- Rerun from `cfg` for `n` transitions using a result's recorded coin bits, and clear the
unread-bit field. -/
def truncate (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) : Result Γ Λ :=
  {run M n r.bits cfg with unread := []}

/-- The bounded-law mass of a specified result if its stopping reason is program halting, and
zero otherwise. -/
noncomputable def finishedMass (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) : ℝ≥0∞ := if r.stop = .halted then law M n cfg r else 0

/-- The supremum over fuel bounds of the finished mass of a specified result. -/
noncomputable def haltedMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) : ℝ≥0∞ := ⨆ n, finishedMass M n cfg r

/-- The residual mass after subtracting the total mass of all halted results from one. -/
noncomputable def neverMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : ℝ≥0∞ :=
  1 - ∑' r, haltedMass M cfg r

/-- Assign halted-result masses to `some` values and residual nontermination mass to `none`. -/
noncomputable def terminalMass (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : Option (Result Γ Λ) → ℝ≥0∞
  | none => neverMass M cfg
  | some r => haltedMass M cfg r

/-- A valid native tape step pairs deterministic instructions with no coin and coin instructions
with a supplied bit, and reaches the specified successor configuration. -/
def Step (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (b : Option Bool)
    (next : Turing.TM0.Cfg Γ Λ) : Prop :=
  (match M cfg.q cfg.Tape.head, b with
    | .det _ _, none => True
    | .coin _, some _ => True
    | _, _ => False) ∧
  Turing.TM0.step (table M (b.getD false)) cfg = some next

/-- A finite sequence of valid native tape steps with a trace of the source configuration and
optional coin at each step. -/
inductive Path (M : Program Γ Λ) : Turing.TM0.Cfg Γ Λ → List (Tick Γ Λ) →
    Turing.TM0.Cfg Γ Λ → Prop
  | nil (cfg) : Path M cfg [] cfg
  | cons {cfg next last b es} : Step M cfg b next → Path M next es last →
      Path M cfg ((cfg, b) :: es) last

/-- Resume a fuel-exhausted result with extra fuel and its unread bits, concatenating traces;
preserve results with other stopping reasons. -/
def resume (M : Program Γ Λ) (extra : ℕ) (r : Result Γ Λ) : Result Γ Λ :=
  if r.stop = .fuel then
    let s := run M extra r.unread r.cfg
    { s with trace := r.trace ++ s.trace }
  else r

/-- Supply additional bits, resuming a bit-starved result within the remaining transition budget
and otherwise appending them to its unread bits. -/
def supply (M : Program Γ Λ) (budget : ℕ) (more : List Bool) (r : Result Γ Λ) : Result Γ Λ :=
  if r.stop = .needBits then
    let s := run M (budget-r.steps) (r.unread ++ more) r.cfg
    { s with trace := r.trace ++ s.trace }
  else { r with unread := r.unread ++ more }

/-- A deterministic native tape program that moves right forever without consuming random bits. -/
def spin : Program Γ Unit := fun _ _ => .det () (.move .right)

end NativeTape

end Qatlib.Concepts.AdversaryBounds.AdvDuality
