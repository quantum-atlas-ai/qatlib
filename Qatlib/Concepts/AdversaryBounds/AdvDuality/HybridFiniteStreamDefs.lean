/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridCallReturn
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridCallReturn
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace HybridFiniteStream

open scoped ENNReal

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A V : Type}

def streamPath {D : ℕ} {A : Type} :
    (p : HybridProgram D A) → List Bool → Option (HybridProgram.Path p)
  | .ret a, _ => some (.ret a)
  | .step s p, bs => (streamPath p bs).map (fun h => .step s h)
  | .bit _ _, [] => none
  | .bit p q, b :: bs =>
      if b then (streamPath q bs).map (fun h => .bitTrue h)
      else (streamPath p bs).map (fun h => .bitFalse h)
  | .measure _ _ _, _ => none
  | .project _ _ _, _ => none

noncomputable def execStream {D : ℕ} {A : Type} (O : Operator D) :
    (p : HybridProgram D A) → List Bool → Option (HybridLeaf D A)
  | .ret a, _ => some ⟨a, 1, 0, 0, 0, [], [], []⟩
  | .step (.gate U) p, bs => (execStream O p bs).map (fun t => t.quantum U 0 1 0 [])
  | .step .query p, bs => (execStream O p bs).map (fun t => t.quantum O 1 0 0 [])
  | .bit _ _, [] => none
  | .bit p _, false :: bs => (execStream O p bs).map (fun t => t.coin false)
  | .bit _ q, true :: bs => (execStream O q bs).map (fun t => t.coin true)
  | .measure _ _ _, _ => none
  | .project _ _ _, _ => none

def CoinOnly : HybridProgram D A → Prop
  | .ret _ => True
  | .step _ p => CoinOnly p
  | .bit p q => CoinOnly p ∧ CoinOnly q
  | .measure _ _ _ => False
  | .project _ _ _ => False

inductive ScheduleOutcome (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (D : ℕ) (A : Type) (V : Type)
    where

  | pendingNative (r : NativeTape.Result Γ Λ)

  | pendingQuantum (r : NativeTape.Result Γ Λ) (v : V)

  | undecoded (r : NativeTape.Result Γ Λ)

  | returned (r : NativeTape.Result Γ Λ) (v : V) (t : HybridLeaf D A)

noncomputable def scheduleOf {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (r : NativeTape.Result Γ Λ) :
    ScheduleOutcome Γ Λ D A V :=
  match c.decoded r with
  | none =>
      if r.stop = NativeTape.Stop.halted then .undecoded r else .pendingNative r
  | some v =>
      match execStream O (c.next v) r.unread with
      | some t => .returned r v t
      | none => .pendingQuantum r v

noncomputable def schedule {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) : ScheduleOutcome Γ Λ D A V :=
  scheduleOf c O c.native

noncomputable def scheduleResume {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (extra : ℕ) :
    ScheduleOutcome Γ Λ D A V :=
  scheduleOf c O (NativeTape.resume c.program extra c.native)

noncomputable def scheduleSupply {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (more : List Bool) :
    ScheduleOutcome Γ Λ D A V :=
  scheduleOf c O (NativeTape.supply c.program c.budget more c.native)

noncomputable def scheduleLedger {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) : Ledger :=
  let r := c.native
  match scheduleOf c O r with
  | .returned _ v t => runClocks (D := D) (A := A) c.program r (some t) (c.decodeWidth v)
  | _ => runClocks (D := D) (A := A) c.program r none 0

noncomputable def scheduleConditional {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (r : NativeTape.Result Γ Λ) :
    PMF (ScheduleOutcome Γ Λ D A V) :=
  if r.stop = NativeTape.Stop.halted then
    match c.decode r.cfg with
    | none => PMF.pure (.undecoded r)
    | some v => (leafLaw (c.next v) O hO (hp v) ρ hρ).map (fun t => .returned r v t)
  else PMF.pure (.pendingNative r)

noncomputable def scheduleLaw {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (n : ℕ) :
    PMF (ScheduleOutcome Γ Λ D A V) :=
  (NativeTape.law c.program n c.config).bind (scheduleConditional c O hO hp ρ hρ)

noncomputable def scheduleContinueFuel {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (extra : ℕ) :
    ScheduleOutcome Γ Λ D A V → PMF (ScheduleOutcome Γ Λ D A V)
  | .pendingNative r =>
      (NativeTape.continueLaw c.program extra r).bind (scheduleConditional c O hO hp ρ hρ)
  | .pendingQuantum r v => PMF.pure (.pendingQuantum r v)
  | .undecoded r => PMF.pure (.undecoded r)
  | .returned r v t => PMF.pure (.returned r v t)

noncomputable def scheduleLawFuel {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (n extra : ℕ) :
    PMF (ScheduleOutcome Γ Λ D A V) :=
  (scheduleLaw c O hO hp ρ hρ n).bind (scheduleContinueFuel c O hO hp ρ hρ extra)

noncomputable def scheduleTerminalConditional {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {D : ℕ} {A V : Type} (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (z : Option (NativeTape.Result Γ Λ)) :
    PMF (NativeHybridCallReturn.JointOutcome Γ Λ D A V) :=
  match z with
  | none => PMF.pure .never
  | some r =>
      match c.decoded r with
      | none => PMF.pure (.undecoded r)
      | some v => (leafLaw (c.next v) O hO (hp v) ρ hρ).map (fun t => .returned r v t)

noncomputable def scheduleTerminalLaw {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    PMF (NativeHybridCallReturn.JointOutcome Γ Λ D A V) :=
  (NativeTape.terminalLaw c.program c.config).bind
    (scheduleTerminalConditional c O hO hp ρ hρ)

end HybridFiniteStream

end Qatlib.Concepts.AdversaryBounds.AdvDuality
