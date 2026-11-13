/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder

/-!
# Native calls with quantum continuations

This module defines `NativeHybrid.Call` and `NativeHybrid.Record` to connect bounded native tape
execution with a chosen path of the halted quantum continuation. `Record.branch` and
`Record.bornMass` represent a fair-coin-weighted quantum operation and its trace mass, following
the standard quantum-operation semantics in [Watrous2018].

A record retains its native result and includes a quantum leaf when native execution halts;
`Record.ledger` extracts native step and bit counts together with the available quantum counts.

## Main statements

* `Call.native` evaluates the native program with its budget and supplied bits.
* `Record.run` records the selected quantum path after native halting.
* `Record.action`, `Record.branch`, and `Record.bornMass` give operator and probability-mass
  semantics.
* `Record.resume` reruns the halting check after resuming native execution with additional fuel.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace NativeHybrid

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A : Type}

/-- A native program invocation with a step budget, supplied bits, initial configuration, and a
quantum continuation for each native stopping reason. -/
structure Call (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (D : ℕ) (A : Type) where

  program : NativeTape.Program Γ Λ

  budget : ℕ

  bits : List Bool

  config : Turing.TM0.Cfg Γ Λ

  next : NativeTape.Stop → HybridProgram D A

/-- Run the call's native program from its initial configuration with its supplied budget and
bits. -/
def Call.native {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) : NativeTape.Result Γ Λ :=
  NativeTape.run c.program c.budget c.bits c.config

/-- A combined execution record retaining a native result and an optional quantum leaf. -/
structure Record (Γ Λ : Type) [Inhabited Γ] (D : ℕ) (A : Type) where

  native : NativeTape.Result Γ Λ

  quantum : Option (HybridLeaf D A)

/-- Run a native call and attach the chosen path's quantum leaf if the native execution halts,
retaining the native result in either case. -/
noncomputable def Record.run {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) (O : Operator D)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) : Record Γ Λ D A :=
  let r := c.native
  if r.stop = .halted then ⟨r, some (p.record O)⟩ else ⟨r, none⟩

/-- A resource ledger recording native steps, consumed native bits, and quantum operation
counts. -/
structure Ledger where

  nativeSteps : ℕ

  nativeBits : ℕ

  quantum : HybridCounts

/-- Extract native step and consumed-bit counts from a record, using its leaf's quantum counts
when present and zero otherwise. -/
def Record.ledger {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) : Ledger :=
  { nativeSteps := rec.native.steps
    nativeBits := rec.native.bits.length
    quantum := (rec.quantum.map (fun t => t.counts)).getD HybridCounts.zero }

/-- Represent native computation on the quantum operator by left multiplication with the
identity operator. -/
noncomputable def nativeAction (D : ℕ) (ρ : Operator D) : Operator D := 1 * ρ

/-- Apply the optional quantum leaf's operator after the native identity action, returning zero
if the record has no leaf. -/
noncomputable def Record.action {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : Operator D :=
  match rec.quantum with
  | none => 0
  | some t => t.operator * nativeAction D ρ

/-- Evaluate the optional leaf's conjugation branch weighted by its fair-coin word probability,
returning zero when no leaf is recorded. -/
noncomputable def Record.branch {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : Operator D :=
  match rec.quantum with
  | none => 0
  | some t => ((CoinCode.wordWeight t.coins : ℝ) : ℂ) • conjBranch t.operator ρ

/-- Take the real part of the trace of a record's weighted branch. -/
noncomputable def Record.bornMass {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : ℝ :=
  (Matrix.trace (rec.branch ρ)).re

/-- Resume the call's native result with additional fuel and attach the chosen quantum leaf if
that resumed result halts. -/
noncomputable def Record.resume {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) (O : Operator D) (extra : ℕ)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) : Record Γ Λ D A :=
  let r := NativeTape.resume c.program extra c.native
  if r.stop = .halted then ⟨r, some (p.record O)⟩ else ⟨r, none⟩

end NativeHybrid

end Qatlib.Concepts.AdversaryBounds.AdvDuality
