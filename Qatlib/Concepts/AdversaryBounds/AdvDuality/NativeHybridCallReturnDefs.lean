/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridExecution

/-!
# Native call-return records and probability laws

This module defines `ReturnCall`, whose halted native configuration can decode to a value
selecting a `HybridProgram`, and `JointRecord`, which records the native result, decoded value,
quantum leaf, and resource ledger. `JointRecord.branch` and `JointRecord.bornMass` use the
standard instrument and trace interpretation described in [Watrous2018].

The definitions also provide resumed execution, additional bit supply, and a joint probability
law with explicit nontermination and failed-decoding outcomes.

## Main statements

* `ReturnCall.decoded` and `ReturnCall.selected` select a continuation only after native
  halting.
* `ReturnCall.run`, `ReturnCall.resume`, and `ReturnCall.supply` assemble execution records and
  clocks.
* `Ledger`, `nativeCpuTime`, and `nativePeakSpace` separate native work, quantum counts, space,
  and communication.
* `leafLaw`, `conditionalLaw`, and `jointLaw` combine native terminal outcomes with quantum leaf
  probabilities.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace NativeHybridCallReturn

open Qatlib
open scoped ENNReal

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A V : Type}

/-- A bounded native call with supplied bits and an initial configuration, together with a
partial return decoder, value-indexed quantum continuations, and communication widths. -/
structure ReturnCall (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (D : ℕ) (A : Type) (V : Type) where

  program : NativeTape.Program Γ Λ

  budget : ℕ

  bits : List Bool

  config : Turing.TM0.Cfg Γ Λ

  decode : Turing.TM0.Cfg Γ Λ → Option V

  next : V → HybridProgram D A

  decodeWidth : V → ℕ

/-- Execute the call's native program from its configuration using its step budget and supplied
bits. -/
def ReturnCall.native {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) : NativeTape.Result Γ Λ :=
  NativeTape.run c.program c.budget c.bits c.config

/-- Apply the return decoder to a native result's final configuration if the result halted, and
return no value otherwise. -/
def ReturnCall.decoded {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (r : NativeTape.Result Γ Λ) : Option V :=
  if r.stop = NativeTape.Stop.halted then c.decode r.cfg else none

/-- Select the continuation associated with the halted native result's decoded value, if one
exists. -/
def ReturnCall.selected {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (r : NativeTape.Result Γ Λ) : Option (HybridProgram D A) :=
  (c.decoded r).map c.next

/-- Build a return-decoding call from a native hybrid call, retaining its execution inputs and
supplying a decoder, value-indexed continuations, and communication widths. -/
def ReturnCall.ofCall {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : NativeHybrid.Call Γ Λ D A) (decode : Turing.TM0.Cfg Γ Λ → Option V)
    (next : V → HybridProgram D A) (decodeWidth : V → ℕ) : ReturnCall Γ Λ D A V :=
  { program := c.program, budget := c.budget, bits := c.bits, config := c.config,
    decode := decode, next := next, decodeWidth := decodeWidth }

/-- Charge one unit for a native tick plus the absolute displacement of its cursor movement. -/
def nativeInstructionCost (M : NativeTape.Program Γ Λ) (e : NativeTape.Tick Γ Λ) : ℕ :=
  1 + (NativeTape.tickDisplacement M e).natAbs

/-- Sum the native instruction costs over a result's recorded trace. -/
def nativeCpuTime (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ) : ℕ :=
  (r.trace.map (nativeInstructionCost M)).sum

/-- Count the distinct cursor positions in the result's native cursor trace starting at zero. -/
def nativePeakSpace (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ) : ℕ :=
  (NativeTape.cursorTrace M 0 r.trace).eraseDups.length

/-- Resource totals for native steps and bits, quantum operation counts, native CPU time, native
and quantum space, and communication. -/
structure Ledger where

  nativeSteps : ℕ

  nativeBits : ℕ

  quantum : HybridCounts

  nativeCpu : ℕ

  nativeSpace : ℕ

  quantumSpace : ℕ

  communication : ℕ

/-- Combine the ledger's native and quantum space costs by addition. -/
def Ledger.peakSpace (l : Ledger) : ℕ := l.nativeSpace + l.quantumSpace

/-- Read the query count from the ledger's quantum operation counts. -/
def Ledger.queries (l : Ledger) : ℕ := l.quantum.queries

/-- Assemble a ledger from a native result, an optional quantum leaf, and a communication cost,
using zero quantum counts when no leaf is present. -/
def runClocks {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ)
    (leaf : Option (HybridLeaf D A)) (channel : ℕ) : Ledger :=
  { nativeSteps := r.steps
    nativeBits := r.bits.length
    quantum := (leaf.map (fun t => t.counts)).getD HybridCounts.zero
    nativeCpu := nativeCpuTime M r
    nativeSpace := nativePeakSpace M r
    quantumSpace := D
    communication := channel }

/-- Outcomes of the combined probability law: nontermination, a native result with no decoded
return, or a native result paired with a returned value and quantum leaf. -/
inductive JointOutcome (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (D : ℕ) (A : Type) (V : Type) : Type where

  | never : JointOutcome Γ Λ D A V

  | undecoded (r : NativeTape.Result Γ Λ) : JointOutcome Γ Λ D A V

  | returned (r : NativeTape.Result Γ Λ) (v : V) (t : HybridLeaf D A) : JointOutcome Γ Λ D A V

/-- An execution record containing a native result, optional decoded value and quantum leaf, a
communication cost, and a resource ledger. -/
structure JointRecord (Γ Λ : Type) [Inhabited Γ] (D : ℕ) (A : Type) (V : Type) where

  native : NativeTape.Result Γ Λ

  value : Option V

  leaf : Option (HybridLeaf D A)

  channel : ℕ

  clocks : Ledger

/-- Run the native call and, if it halts and decodes successfully, record the chosen
continuation path, decoded value, and communication width. Otherwise retain the native
result with no value or leaf and zero communication. -/
noncomputable def ReturnCall.run {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) : JointRecord Γ Λ D A V :=
  let r := c.native
  match c.decoded r with
  | none => ⟨r, none, none, 0, runClocks (D := D) (A := A) c.program r none 0⟩
  | some v =>
    let t := (paths v).record O
    ⟨r, some v, some t, c.decodeWidth v, runClocks c.program r (some t) (c.decodeWidth v)⟩

/-- Resume native execution with additional fuel, then assemble a joint record using its
halted-only decoded value and chosen continuation path. -/
noncomputable def ReturnCall.resume {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (extra : ℕ)
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) : JointRecord Γ Λ D A V :=
  let r := NativeTape.resume c.program extra c.native
  match c.decoded r with
  | none => ⟨r, none, none, 0, runClocks (D := D) (A := A) c.program r none 0⟩
  | some v =>
    let t := (paths v).record O
    ⟨r, some v, some t, c.decodeWidth v, runClocks c.program r (some t) (c.decodeWidth v)⟩

/-- Supply additional bits to native execution using the call's budget, then assemble a joint
record from any successfully decoded halted result. -/
noncomputable def ReturnCall.supply {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (more : List Bool)
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) : JointRecord Γ Λ D A V :=
  let r := NativeTape.supply c.program c.budget more c.native
  match c.decoded r with
  | none => ⟨r, none, none, 0, runClocks (D := D) (A := A) c.program r none 0⟩
  | some v =>
    let t := (paths v).record O
    ⟨r, some v, some t, c.decodeWidth v, runClocks c.program r (some t) (c.decodeWidth v)⟩

/-- Represent native computation on the quantum operator by left multiplication with the
identity operator. -/
noncomputable def nativeAction (D : ℕ) (ρ : Operator D) : Operator D := 1 * ρ

/-- Apply the recorded leaf's operator after the native identity action, or return zero when no
leaf is recorded. -/
noncomputable def JointRecord.action {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A V : Type}
    (rec : JointRecord Γ Λ D A V) (ρ : Operator D) : Operator D :=
  match rec.leaf with
  | none => 0
  | some t => t.operator * nativeAction D ρ

/-- Apply the recorded leaf's conjugation branch weighted by its fair-coin word probability, or
return zero when no leaf is recorded. -/
noncomputable def JointRecord.branch {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A V : Type}
    (rec : JointRecord Γ Λ D A V) (ρ : Operator D) : Operator D :=
  match rec.leaf with
  | none => 0
  | some t => ((CoinCode.wordWeight t.coins : ℝ) : ℂ) • conjBranch t.operator ρ

/-- Take the real part of the trace of the joint record's weighted branch. -/
noncomputable def JointRecord.bornMass {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A V : Type}
    (rec : JointRecord Γ Λ D A V) (ρ : Operator D) : ℝ :=
  (Matrix.trace (rec.branch ρ)).re

/-- Evaluate the chosen path's conjugation branch and weight it by the probability of the path's
fair-coin word. -/
noncomputable def selectedBranch {D : ℕ} {A : Type} {p : HybridProgram D A}
    (O : Operator D) (path : HybridProgram.Path p) (ρ : Operator D) : Operator D :=
  ((CoinCode.wordWeight (path.record O).coins : ℝ) : ℂ) • conjBranch (path.record O).operator ρ

/-- Form a probability mass function on a legal hybrid program's leaves by mapping its
instrument outcome probabilities to leaf records for a unitary oracle and density operator. -/
noncomputable def leafLaw {D : ℕ} {A : Type} (p : HybridProgram D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : p.Legal) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : PMF (HybridLeaf D A) :=
  (PMF.ofFintype
    (fun i => ENNReal.ofReal (instrumentProb (p.instrument O hO hp) ρ i))
    (by
      classical
      have hsum : (∑ i : Fin p.leafCount, ENNReal.ofReal (instrumentProb (p.instrument O hO hp) ρ i))
          = ENNReal.ofReal (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) ρ i) := by
        have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin p.leafCount)),
            0 ≤ instrumentProb (p.instrument O hO hp) ρ i :=
          fun i _ => (instrumentProb_nonneg (p.instrument O hO hp) hρ.1 i)
        symm
        exact ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin p.leafCount)))
          (f := fun i => instrumentProb (p.instrument O hO hp) ρ i) hnonneg
      calc
        (∑ i : Fin p.leafCount, ENNReal.ofReal (instrumentProb (p.instrument O hO hp) ρ i))
            = ENNReal.ofReal (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) ρ i) := hsum
        _ = ENNReal.ofReal 1 := by rw [sum_instrumentProb_isDensityOperator (p.instrument O hO hp) hρ]
        _ = 1 := ENNReal.ofReal_one)).map (fun i => p.leaf O i)

/-- Map a native terminal outcome to nontermination, a fixed undecoded result, or the quantum
leaf law for its decoded continuation. -/
noncomputable def conditionalLaw {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (z : Option (NativeTape.Result Γ Λ))
    : PMF (JointOutcome Γ Λ D A V) :=
  match z with
  | none => PMF.pure .never
  | some r =>
    match c.decode r.cfg with
    | none => PMF.pure (.undecoded r)
    | some v => (leafLaw (c.next v) O hO (hp v) ρ hρ).map (fun t => .returned r v t)

/-- Bind the native terminal law to the conditional joint-outcome law, combining native
execution with decoded quantum continuations. -/
noncomputable def jointLaw {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) : PMF (JointOutcome Γ Λ D A V) :=
  (NativeTape.terminalLaw c.program c.config).bind (conditionalLaw c O hO hp ρ hρ)

/-- Concatenate the native result's consumed bits with the quantum leaf's fair-coin word. -/
def fairWord {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (r : NativeTape.Result Γ Λ) (t : HybridLeaf D A) : List Bool :=
  r.bits ++ t.coins

/-- The extended nonnegative probability weight of a prescribed fair-bit word of the given
length. -/
noncomputable def fairWeight (k : ℕ) : ℝ≥0∞ := (1 / 2 : ℝ≥0∞)^k

end NativeHybridCallReturn

end Qatlib.Concepts.AdversaryBounds.AdvDuality
