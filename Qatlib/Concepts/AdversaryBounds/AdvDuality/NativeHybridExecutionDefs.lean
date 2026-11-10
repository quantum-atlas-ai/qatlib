/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

structure Call (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (D : ℕ) (A : Type) where

  program : NativeTape.Program Γ Λ

  budget : ℕ

  bits : List Bool

  config : Turing.TM0.Cfg Γ Λ

  next : NativeTape.Stop → HybridProgram D A

def Call.native {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) : NativeTape.Result Γ Λ :=
  NativeTape.run c.program c.budget c.bits c.config

structure Record (Γ Λ : Type) [Inhabited Γ] (D : ℕ) (A : Type) where

  native : NativeTape.Result Γ Λ

  quantum : Option (HybridLeaf D A)

noncomputable def Record.run {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) (O : Operator D)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) : Record Γ Λ D A :=
  let r := c.native
  if r.stop = .halted then ⟨r, some (p.record O)⟩ else ⟨r, none⟩

structure Ledger where

  nativeSteps : ℕ

  nativeBits : ℕ

  quantum : HybridCounts

def Record.ledger {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) : Ledger :=
  { nativeSteps := rec.native.steps
    nativeBits := rec.native.bits.length
    quantum := (rec.quantum.map (fun t => t.counts)).getD HybridCounts.zero }

noncomputable def nativeAction (D : ℕ) (ρ : Operator D) : Operator D := 1 * ρ

noncomputable def Record.action {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : Operator D :=
  match rec.quantum with
  | none => 0
  | some t => t.operator * nativeAction D ρ

noncomputable def Record.branch {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : Operator D :=
  match rec.quantum with
  | none => 0
  | some t => ((CoinCode.wordWeight t.coins : ℝ) : ℂ) • conjBranch t.operator ρ

noncomputable def Record.bornMass {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (rec : Record Γ Λ D A) (ρ : Operator D) : ℝ :=
  (Matrix.trace (rec.branch ρ)).re

noncomputable def Record.resume {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A : Type}
    (c : Call Γ Λ D A) (O : Operator D) (extra : ℕ)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) : Record Γ Λ D A :=
  let r := NativeTape.resume c.program extra c.native
  if r.stop = .halted then ⟨r, some (p.record O)⟩ else ⟨r, none⟩

end NativeHybrid

end Qatlib.Concepts.AdversaryBounds.AdvDuality
