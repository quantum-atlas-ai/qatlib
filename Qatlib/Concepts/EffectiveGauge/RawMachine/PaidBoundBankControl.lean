/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundMachineCall

/-!
# Paid Bound Bank Control

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Local`, `rawSlot`.
Proves `begin_call`, `source_call`, `transfer_execution`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open CanonicalCodec.TM

namespace PaidBoundBank

/-- Abbreviation for Slot in the Raw Machine construction. -/
abbrev Slot := RawCall.Slot ⊕ (Fin 9 ⊕ Fin 1)
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := RawCall.Local
/-- Abbreviation for raw Slot in the Raw Machine construction. -/
abbrev rawSlot : Slot := .inl RawCall.rawSlot
/-- Abbreviation for output Slot in the Raw Machine construction. -/
abbrev outputSlot : Slot := .inr (.inr 0)
/-- Definition of saved Slot in the Raw Machine construction. -/
def savedSlot (i : Fin 9) : Slot := .inr (.inl i)

/-- Constructors for Label in the Raw Machine construction. -/
inductive Label (states : ℕ) where
  | begin (i : Fin 9)
  | call (i : Fin 9) (l : RawCall.Label states)
  | store (i : Fin 9) (l : Fin 1)
  | emit (i : Fin 9) (l : Fin 1)
  | done
  deriving DecidableEq, Fintype
/-- Initialize the machine label at its first instruction. -/
instance (states : ℕ) : Inhabited (Label states) := ⟨.begin 0⟩

/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config (states : ℕ) := TM2.Cfg (fun _ : Slot => Bool) (Label states) Local

/-- Definition of frozen in the Raw Machine construction. -/
def frozen (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) : Fin 9 ⊕ Fin 1 → CanonicalCodec.Bits :=
  Sum.elim saved (fun _ => out)
/-- Definition of frame in the Raw Machine construction. -/
def frame (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits)
    (work : RawCall.Slot → CanonicalCodec.Bits) : Slot → CanonicalCodec.Bits :=
  StackCall.leftFrame (frozen saved out) work

/-- Definition of query Bits in the Raw Machine construction. -/
def queryBits (i : Fin 9) : CanonicalCodec.Bits := CanonicalCodec.natBits (i.val+1)
/-- Definition of next Source in the Raw Machine construction. -/
def nextSource {states : ℕ} (i : Fin 9) : Label states :=
  if h : i.val+1<9 then .begin ⟨i.val+1,h⟩ else .emit 0 0
/-- Definition of next Emit in the Raw Machine construction. -/
def nextEmit {states : ℕ} (i : Fin 9) : Label states :=
  if h : i.val+1<9 then .emit ⟨i.val+1,h⟩ 0 else .done

/-- Definition of store Code in the Raw Machine construction. -/
def storeCode (i : Fin 9) : Fin 2 → Slot | 0 => .inl RawCall.outputSlot | _ => savedSlot i
/-- Definition of emit Code in the Raw Machine construction. -/
def emitCode (i : Fin 9) : Fin 2 → Slot | 0 => savedSlot i | _ => outputSlot

/-- Definition of program in the Raw Machine construction. -/
def program {states : ℕ} (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    Label states → TM2.Stmt (fun _ : Slot => Bool) (Label states) Local
  | .begin i => Stacks.pushBits rawSlot (queryBits i) (.goto (fun _ => .call i default))
  | .call i l => StackCall.stmt Sum.inl (Label.call i) (.store i 0) id (fun _ v => v) (RawCall.program machine l)
  | .store i l => StackCall.stmt (storeCode i) (Label.store i) (nextSource i)
      RawCall.getIO RawCall.putIO (Stacks.transferProgram l)
  | .emit i l => StackCall.stmt (emitCode i) (Label.emit i) (nextEmit i)
      RawCall.getIO RawCall.putIO (Stacks.transferProgram l)
  | .done => .load (fun _ => default) .halt

/-- Original `begin_call` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem begin_call {states : ℕ} (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    Stacks.Execution (program machine)
      ⟨some (.begin i),default,frame saved out (fun _ => [])⟩
      ⟨some (.call i default),default,frame saved out (RawCall.initial (q := states) (queryBits i)).stk⟩
      (1+(queryBits i).length*((queryBits i).length+2)) := by
  have hu := StackCall.leftFrame_update (frozen saved out) (fun _ : RawCall.Slot => []) RawCall.rawSlot (queryBits i).reverse
  refine ⟨1,?_,?_⟩
  · simp only [Stacks.stackRun, TM2.step, program, Stacks.pushBits_step,
      TM2.stepAux, Option.bind_some]
    congr 2
    simpa only [frame, StackCall.leftFrame_at, List.append_nil, RawCall.initial, TM2.init] using hu.symm
  · change 1+Stacks.stackClock (program machine (.begin i)) default (frame saved out (fun _ => []))+0 ≤ _
    rw [program,Stacks.pushBits_clock]
    simp only [Stacks.stackClock,frame,StackCall.leftFrame,Sum.elim,List.length_nil,mul_zero,
      Nat.zero_add,Nat.add_zero]
    exact le_rfl

/-- Original `source_call` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem source_call {states : ℕ} (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out reply : CanonicalCodec.Bits)
    (time space : ℕ) (hrun : CanonicalCodec.Runs machine (queryBits i) reply time space) :
    Stacks.Execution (program machine)
      ⟨some (.call i default),default,frame saved out (RawCall.initial (q := states) (queryBits i)).stk⟩
      ⟨some (.store i 0),default,
        frame saved out (Function.update (fun _ => []) RawCall.outputSlot reply.reverse)⟩
      (RawCall.budget (queryBits i).length time) := by
  obtain ⟨steps,hsteps,hclock⟩ := RawCall.source_exec machine (queryBits i) reply time space hrun
  obtain ⟨hr,hc⟩ := StackCall.execution Sum.inl (Label.call i) (.store i 0) id (fun _ v => v)
    (StackCall.leftFrame (frozen saved out))
    (fun S k => StackCall.leftFrame_at (frozen saved out) S k)
    (fun S k bits => StackCall.leftFrame_update (frozen saved out) S k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (RawCall.program machine) (program machine) (fun _ => rfl) default steps _ _ hsteps
  refine ⟨steps,?_,?_⟩
  · simpa only [RawCall.initial,TM2.init,StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,frame] using hr
  · simpa only [RawCall.initial,TM2.init,StackCall.cfg,Option.map_some,Option.getD_some,frame] using hc.trans_le hclock

/-- Original `transfer_execution` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
private theorem transfer_execution {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (code : Fin 2 → Slot) (hinj : Function.Injective code)
    (labels : Fin 1 → Label states) (ret : Label states)
    (hcode : ∀ l, program machine (labels l)=StackCall.stmt code labels ret
      RawCall.getIO RawCall.putIO (Stacks.transferProgram l))
    (S : Slot → CanonicalCodec.Bits) :
    Stacks.Execution (program machine) ⟨some (labels 0),default,S⟩
      ⟨some ret,default,Function.update (Function.update S (code 0) []) (code 1)
        ((S (code 0)).reverse++S (code 1))⟩
      ((S (code 0)).length*(2*((S (code 0)).length+(S (code 1)).length)+5)+3) := by
  let input := S (code 0)
  let output := S (code 1)
  let pair := Stacks.stackPair input output
  have hi : StackCall.frame code S pair=S :=
    StackCall.frame_same code S pair hinj (by intro k; fin_cases k <;> rfl)
  change StackCall.frame code S (Stacks.stackPair input output)=S at hi
  have hv : RawCall.putIO (default : Local) none=default := rfl
  have he : Stacks.stackPair [] (input.reverse++output)=
      Function.update (Function.update pair 0 []) 1 (input.reverse++output) := by
    funext k; fin_cases k <;> simp [Stacks.stackPair]
  have hf : StackCall.frame code S (Stacks.stackPair [] (input.reverse++output))=
      Function.update (Function.update S (code 0) []) (code 1) (input.reverse++output) := by
    rw [he, StackCall.frame_update code S _ hinj, StackCall.frame_update code S _ hinj,hi]
  obtain ⟨hr,hc⟩ := StackCall.execution code labels ret RawCall.getIO RawCall.putIO
    (StackCall.frame code S)
    (fun data k => StackCall.frame_at code S data hinj k)
    (fun data k bits => StackCall.frame_update code S data hinj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram (program machine) hcode default (input.length+1) _ _
    (Stacks.transfer_run input output none)
  refine ⟨input.length+1,?_,?_⟩
  · simpa only [RawCall.initial,TM2.init,StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
      Option.getD_none,hi,hf,hv] using hr
  · simpa only [RawCall.initial,TM2.init,StackCall.cfg,Option.map_some,Option.getD_some,hi,hv,
      Stacks.transfer_clock] using hc.le

/-- Original `storeCode_injective` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
private theorem storeCode_injective (i : Fin 9) : Function.Injective (storeCode i) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [storeCode,savedSlot]

/-- Original `emitCode_injective` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
private theorem emitCode_injective (i : Fin 9) : Function.Injective (emitCode i) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [emitCode,savedSlot]

/-- Original `store_transfer` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem store_transfer {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (S : Slot → CanonicalCodec.Bits) :
    Stacks.Execution (program machine) ⟨some (.store i 0),default,S⟩
      ⟨some (nextSource i),default,
        Function.update (Function.update S (.inl RawCall.outputSlot) []) (savedSlot i)
          ((S (.inl RawCall.outputSlot)).reverse++S (savedSlot i))⟩
      ((S (.inl RawCall.outputSlot)).length*
        (2*((S (.inl RawCall.outputSlot)).length+(S (savedSlot i)).length)+5)+3) :=
  transfer_execution machine (storeCode i) (storeCode_injective i)
    (Label.store i) (nextSource i) (fun _ => rfl) S

/-- Original `emit_transfer` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem emit_transfer {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (S : Slot → CanonicalCodec.Bits) :
    Stacks.Execution (program machine) ⟨some (.emit i 0),default,S⟩
      ⟨some (nextEmit i),default,
        Function.update (Function.update S (savedSlot i) []) outputSlot
          ((S (savedSlot i)).reverse++S outputSlot)⟩
      ((S (savedSlot i)).length*
        (2*((S (savedSlot i)).length+(S outputSlot).length)+5)+3) :=
  transfer_execution machine (emitCode i) (emitCode_injective i)
    (Label.emit i) (nextEmit i) (fun _ => rfl) S

/-- Definition of stage Budget in the Raw Machine construction. -/
def stageBudget (i : Fin 9) (reply : CanonicalCodec.Bits) (time : ℕ) : ℕ :=
  (1+(queryBits i).length*((queryBits i).length+2))+
    RawCall.budget (queryBits i).length time+(reply.length*(2*reply.length+5)+3)

/-- Original `source_stage` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem source_stage {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out reply : CanonicalCodec.Bits)
    (time space : ℕ) (hrun : CanonicalCodec.Runs machine (queryBits i) reply time space)
    (hempty : saved i=[]) :
    Stacks.Execution (program machine)
      ⟨some (.begin i),default,frame saved out (fun _ => [])⟩
      ⟨some (nextSource i),default,frame (Function.update saved i reply) out (fun _ => [])⟩
      (stageBudget i reply time) := by
  have ee := (begin_call machine i saved out).trans
    (source_call machine i saved out reply time space hrun)
  let S := frame saved out (Function.update (fun _ => []) RawCall.outputSlot reply.reverse)
  have e3 := store_transfer machine i S
  have hslot : S (.inl RawCall.outputSlot)=reply.reverse := by rfl
  have hsaved : S (savedSlot i)=[] := hempty
  have he : Function.update (Function.update S (.inl RawCall.outputSlot) []) (savedSlot i) reply=
      frame (Function.update saved i reply) out (fun _ => []) := by
    funext k
    cases k with
    | inl k =>
      dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
      simp only [Function.update_apply]
      dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
      grind
    | inr k =>
      cases k with
      | inl j =>
        dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
        simp only [Function.update_apply]
        dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
        simp only [Function.update_apply]
        grind
      | inr j =>
        dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
        simp only [Function.update_apply]
        dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
        grind
  rw [hslot,hsaved,List.reverse_reverse,List.append_nil,he,List.length_reverse] at e3
  simpa only [S,stageBudget,List.length_nil,Nat.add_zero] using ee.trans e3

/-- Definition of emit Budget in the Raw Machine construction. -/
def emitBudget (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) (i : Fin 9) : ℕ :=
  (saved i).length*(2*((saved i).length+out.length)+5)+3

/-- Original `emit_stage` guarantee for the `PaidBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem emit_stage {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    Stacks.Execution (program machine)
      ⟨some (.emit i 0),default,frame saved out (fun _ => [])⟩
      ⟨some (nextEmit i),default,frame (Function.update saved i []) ((saved i).reverse++out) (fun _ => [])⟩
      (emitBudget saved out i) := by
  let S := frame saved out (fun _ => [])
  have ee := emit_transfer machine i S
  have hslot : S (savedSlot i)=saved i := rfl
  have hout : S outputSlot=out := rfl
  have he : Function.update (Function.update S (savedSlot i) []) outputSlot ((saved i).reverse++out)=
      frame (Function.update saved i []) ((saved i).reverse++out) (fun _ => []) := by
    funext k
    cases k with
    | inl k =>
      dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
      simp only [Function.update_apply]
      dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
      grind
    | inr k =>
      cases k with
      | inl j =>
        dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
        simp only [Function.update_apply]
        dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
        simp only [Function.update_apply]
        grind
      | inr j =>
        fin_cases j
        dsimp only [S,frame,StackCall.leftFrame,frozen,savedSlot]
        simp only [Function.update_apply]
        dsimp only [Sum.elim,outputSlot,RawCall.outputSlot]
        grind
  rw [hslot,hout,he] at ee
  exact ee

end PaidBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
