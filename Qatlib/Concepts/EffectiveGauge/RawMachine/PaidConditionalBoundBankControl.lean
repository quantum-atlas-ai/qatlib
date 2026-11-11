/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundZeroRetention
import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundBankControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Bank Control

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Local`, `sourceRaw`.
Proves `afterStore_first`, `afterStore_last`, `zeroCode_injective`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Abbreviation for Slot in the Raw Machine construction. -/
abbrev Slot := RawCall.Slot ⊕ (PaidRationalZero.Slot ⊕ (Fin 9 ⊕ Fin 2))
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := PaidBoundZeroRetention.Local
/-- Abbreviation for source Raw in the Raw Machine construction. -/
abbrev sourceRaw : Slot := .inl RawCall.rawSlot
/-- Abbreviation for source Output in the Raw Machine construction. -/
abbrev sourceOutput : Slot := .inl RawCall.outputSlot
/-- Abbreviation for zero Slot in the Raw Machine construction. -/
abbrev zeroSlot (k : PaidRationalZero.Slot) : Slot := .inr (.inl k)
/-- Abbreviation for saved Slot in the Raw Machine construction. -/
abbrev savedSlot (i : Fin 9) : Slot := .inr (.inr (.inl i))
/-- Abbreviation for temp Slot in the Raw Machine construction. -/
abbrev tempSlot : Slot := .inr (.inr (.inr 0))
/-- Abbreviation for output Slot in the Raw Machine construction. -/
abbrev outputSlot : Slot := .inr (.inr (.inr 1))

/-- Definition of get Source in the Raw Machine construction. -/
def getSource (v : Local) : RawCall.Local := v.1.2
/-- Definition of put Source in the Raw Machine construction. -/
def putSource (v : Local) (w : RawCall.Local) : Local := ((v.1.1,w),v.2)
/-- Definition of get IO in the Raw Machine construction. -/
def getIO (v : Local) := v.2
/-- Definition of put IO in the Raw Machine construction. -/
def putIO (v : Local) (w : Option Bool) : Local := (v.1,w)

/-- Definition of zero Code in the Raw Machine construction. -/
def zeroCode : PaidBoundZeroRetention.Slot → Slot
  | .inl k => zeroSlot k
  | .inr 0 => savedSlot 0
  | .inr _ => tempSlot

/-- Definition of store Code in the Raw Machine construction. -/
def storeCode (i : Fin 9) : Fin 2 → Slot | 0 => sourceOutput | _ => savedSlot i
/-- Definition of emit Code in the Raw Machine construction. -/
def emitCode (i : Fin 9) : Fin 2 → Slot | 0 => savedSlot i | _ => outputSlot

/-- Constructors for Label in the Raw Machine construction. -/
inductive Label (states : ℕ) where
  | begin (i : Fin 9)
  | call (i : Fin 9) (l : RawCall.Label states)
  | store (i : Fin 9) (l : Fin 1)
  | zero (l : PaidBoundZeroRetention.Label)
  | decide
  | emit (stop i : Fin 9) (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
/-- Initialize the machine label at its first instruction. -/
instance (states : ℕ) : Inhabited (Label states) := ⟨.begin 0⟩
/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config (states : ℕ) := TM2.Cfg (fun _ : Slot => Bool) (Label states) Local

/-- Definition of after Store in the Raw Machine construction. -/
def afterStore {states : ℕ} (i : Fin 9) : Label states :=
  if i=0 then .zero (.copy .emit) else
    if h : i.val+1<9 then .begin ⟨i.val+1,h⟩ else .emit 8 0 0

/-- Definition of after Emit in the Raw Machine construction. -/
def afterEmit {states : ℕ} (stop i : Fin 9) : Label states :=
  if h : i.val<stop.val then .emit stop ⟨i.val+1,by omega⟩ 0 else .done

/-- Definition of branch Choice in the Raw Machine construction. -/
def branchChoice {states : ℕ} (isZero : Bool) : Label states :=
  if isZero then .emit 0 0 0 else .begin 1

/-- Definition of program in the Raw Machine construction. -/
def program {states : ℕ} (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    Label states → TM2.Stmt (fun _ : Slot => Bool) (Label states) Local
  | .begin i => Stacks.pushBits sourceRaw (PaidBoundBank.queryBits i) (.goto (fun _ => .call i default))
  | .call i l => StackCall.stmt Sum.inl (Label.call i) (.store i 0) getSource putSource (RawCall.program machine l)
  | .store i l => StackCall.stmt (storeCode i) (Label.store i) (afterStore i) getIO putIO (Stacks.transferProgram l)
  | .zero l => StackCall.stmt zeroCode Label.zero .decide id (fun _ v => v) (PaidBoundZeroRetention.program l)
  | .decide => .pop (zeroSlot PaidRationalZero.outputSlot) putIO
      (.push outputSlot (fun v => (getIO v).getD false)
        (.branch (fun v => (getIO v).getD false)
          (.load (fun _ => default) (.goto (fun _ => .emit 0 0 0)))
          (.load (fun _ => default) (.goto (fun _ => .begin 1)))))
  | .emit stop i l => StackCall.stmt (emitCode i) (Label.emit stop i) (afterEmit stop i) getIO putIO (Stacks.transferProgram l)
  | .done => .load (fun _ => default) .halt

/-- All stacks, including the saved first answer, remain explicit finite
bank data. The flag is generated by the zero subprogram, not supplied to it. -/
def state (saved : Fin 9 → CanonicalCodec.Bits) (out temp : CanonicalCodec.Bits)
    (source : RawCall.Slot → CanonicalCodec.Bits) (zero : PaidRationalZero.Slot → CanonicalCodec.Bits) :
    Slot → CanonicalCodec.Bits :=
  Sum.elim source (Sum.elim zero (Sum.elim saved (Stacks.stackPair temp out)))

/-- Original `afterStore_first` guarantee for the `PaidConditionalBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem afterStore_first {states : ℕ} : afterStore (states := states) 0=.zero (.copy .emit) := rfl
/-- Original `afterStore_last` guarantee for the `PaidConditionalBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem afterStore_last {states : ℕ} : afterStore (states := states) 8=.emit 8 0 0 := rfl

/-- Original `zeroCode_injective` guarantee for the `PaidConditionalBoundBankControl` construction; the complete source hypotheses are retained. -/
theorem zeroCode_injective : Function.Injective zeroCode := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa only [zeroCode,Sum.inr.injEq,Sum.inl.injEq] using h
    | inr b => fin_cases b <;> simp [zeroCode] at h
  | inr a =>
    cases b with
    | inl b => fin_cases a <;> simp [zeroCode] at h
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [zeroCode]

/-- Original `update_zero_flag` guarantee for the `PaidConditionalBoundBankControl` construction; the complete source hypotheses are retained. -/
private theorem update_zero_flag (saved : Fin 9 → CanonicalCodec.Bits) (out temp bits : CanonicalCodec.Bits) :
    Function.update (state saved out temp (fun _ => [])
      (Function.update (fun _ => []) PaidRationalZero.outputSlot bits))
      (zeroSlot PaidRationalZero.outputSlot) []=state saved out temp (fun _ => []) (fun _ => []) := by
  funext k
  cases k with
  | inl k => rfl
  | inr k =>
    cases k with
    | inl k =>
      by_cases h : k=PaidRationalZero.outputSlot
      · subst k; simp only [Function.update_self]; rfl
      · dsimp only [state,zeroSlot,Sum.elim]
        simp only [Function.update_apply]
        grind
    | inr k => rfl

/-- Original `update_output` guarantee for the `PaidConditionalBoundBankControl` construction; the complete source hypotheses are retained. -/
private theorem update_output (saved : Fin 9 → CanonicalCodec.Bits) (out temp bits : CanonicalCodec.Bits) :
    Function.update (state saved out temp (fun _ => []) (fun _ => [])) outputSlot bits=
      state saved bits temp (fun _ => []) (fun _ => []) := by
  funext k
  cases k with
  | inl k => rfl
  | inr k =>
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> rfl

/-- One real pop consumes the generated flag, writes the same prefix bit,
and selects either the one-answer emitter or the next positive-order call. -/
theorem decide_step {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (saved : Fin 9 → CanonicalCodec.Bits) (flag : Bool) :
    Stacks.Execution (program machine)
      ⟨some .decide,default,state saved [] [] (fun _ => [])
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [flag])⟩
      ⟨some (branchChoice flag),default,state saved [flag] [] (fun _ => []) (fun _ => [])⟩ 7 := by
  have hflag : state saved [] [] (fun _ => [])
      (Function.update (fun _ => []) PaidRationalZero.outputSlot [flag])
      (zeroSlot PaidRationalZero.outputSlot)=[flag] := by rfl
  have hs : TM2.step (program machine)
      ⟨some .decide,default,state saved [] [] (fun _ => [])
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [flag])⟩=
      some ⟨some (branchChoice flag),default,state saved [flag] [] (fun _ => []) (fun _ => [])⟩ := by
    cases flag <;> simp only [TM2.step,program,TM2.stepAux,hflag,List.head?_cons,
      putIO,getIO,List.tail_cons,update_zero_flag,Option.getD_some,
      update_output,cond_false,cond_true,branchChoice,Bool.false_eq_true,if_false,if_true] <;> rfl
  refine ⟨1,by rw [Stacks.run_one]; exact hs,?_⟩
  rw [Stacks.stackRunClock,hs]
  cases flag <;> rfl

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
