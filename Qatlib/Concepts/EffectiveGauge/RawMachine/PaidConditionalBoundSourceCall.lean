/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundZeroCall
import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundBankBudget

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Source Call

Raw Machine constructions for Effective Gauge.
Defines `sourceState`, `sourceFrame`.
Proves `begin_call`, `source_call`, `storeCode_injective`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Definition of source State in the Raw Machine construction. -/
def sourceState (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits)
    (work : RawCall.Slot → CanonicalCodec.Bits) : Slot → CanonicalCodec.Bits :=
  state saved out [] work (fun _ => [])
/-- Definition of source Frame in the Raw Machine construction. -/
private def sourceFrame (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    PaidRationalZero.Slot ⊕ (Fin 9 ⊕ Fin 2) → CanonicalCodec.Bits :=
  Sum.elim (fun _ => []) (Sum.elim saved (Stacks.stackPair [] out))

/-- Original `begin_call` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
theorem begin_call {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    Stacks.Execution (program machine)
      ⟨some (.begin i),default,sourceState saved out (fun _ => [])⟩
      ⟨some (.call i default),default,
        sourceState saved out (RawCall.initial (q := states) (PaidBoundBank.queryBits i)).stk⟩
      (1+(PaidBoundBank.queryBits i).length*((PaidBoundBank.queryBits i).length+2)) := by
  have hu := StackCall.leftFrame_update (sourceFrame saved out) (fun _ : RawCall.Slot => [])
    RawCall.rawSlot (PaidBoundBank.queryBits i).reverse
  refine ⟨1,?_,?_⟩
  · simp only [Stacks.stackRun,TM2.step,program,Stacks.pushBits_step,TM2.stepAux,Option.bind_some]
    congr 2
    simpa only [sourceState,state,sourceFrame,StackCall.leftFrame,Sum.elim,List.append_nil,
      RawCall.initial,TM2.init] using hu.symm
  · change 1+Stacks.stackClock (program machine (.begin i)) default (sourceState saved out (fun _ => []))+0≤_
    rw [program,Stacks.pushBits_clock]
    simp only [Stacks.stackClock,sourceState,state,Sum.elim,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
    exact le_rfl

/-- Original `source_call` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
theorem source_call {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out reply : CanonicalCodec.Bits)
    (time space : ℕ) (hrun : CanonicalCodec.Runs machine (PaidBoundBank.queryBits i) reply time space) :
    Stacks.Execution (program machine)
      ⟨some (.call i default),default,
        sourceState saved out (RawCall.initial (q := states) (PaidBoundBank.queryBits i)).stk⟩
      ⟨some (.store i 0),default,
        sourceState saved out (Function.update (fun _ => []) RawCall.outputSlot reply.reverse)⟩
      (RawCall.budget (PaidBoundBank.queryBits i).length time) := by
  obtain ⟨steps,hr,hc⟩ := RawCall.source_exec machine (PaidBoundBank.queryBits i) reply time space hrun
  obtain ⟨hn,hnc⟩ := StackCall.execution Sum.inl (Label.call i) (.store i 0) getSource putSource
    (StackCall.leftFrame (sourceFrame saved out))
    (fun S k => StackCall.leftFrame_at (sourceFrame saved out) S k)
    (fun S k b => StackCall.leftFrame_update (sourceFrame saved out) S k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (RawCall.program machine) (program machine)
    (fun _ => rfl) default steps _ _ hr
  have hdefault : putSource (default : Local) default = default := rfl
  refine ⟨steps,?_,?_⟩
  · simpa only [RawCall.initial,TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      sourceState,state,sourceFrame,StackCall.leftFrame] using hn
  · simpa only [RawCall.initial,TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,
      sourceState,state,sourceFrame,StackCall.leftFrame] using hnc.trans_le hc

/-- Original `storeCode_injective` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
private theorem storeCode_injective (i : Fin 9) : Function.Injective (storeCode i) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [storeCode]

/-- Original `transfer_call` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
theorem transfer_call {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (code : Fin 2 → Slot) (hinj : Function.Injective code)
    (labels : Fin 1 → Label states) (ret : Label states)
    (hcode : ∀ l,program machine (labels l)=StackCall.stmt code labels ret getIO putIO (Stacks.transferProgram l))
    (S : Slot → CanonicalCodec.Bits) :
    Stacks.Execution (program machine) ⟨some (labels 0),default,S⟩
      ⟨some ret,default,Function.update (Function.update S (code 0) []) (code 1)
        ((S (code 0)).reverse++S (code 1))⟩
      ((S (code 0)).length*(2*((S (code 0)).length+(S (code 1)).length)+5)+3) := by
  let input := S (code 0)
  let output := S (code 1)
  let pair := Stacks.stackPair input output
  have hi : StackCall.frame code S (Stacks.stackPair input output)=S :=
    StackCall.frame_same code S pair hinj (by intro k; fin_cases k <;> rfl)
  have he : Stacks.stackPair [] (input.reverse++output)=
      Function.update (Function.update pair 0 []) 1 (input.reverse++output) := by
    funext k; fin_cases k <;> simp [Stacks.stackPair]
  have hf : StackCall.frame code S (Stacks.stackPair [] (input.reverse++output))=
      Function.update (Function.update S (code 0) []) (code 1) (input.reverse++output) := by
    rw [he,StackCall.frame_update code S _ hinj,StackCall.frame_update code S _ hinj,hi]
  obtain ⟨hr,hc⟩ := StackCall.execution code labels ret getIO putIO
    (StackCall.frame code S)
    (fun data k => StackCall.frame_at code S data hinj k)
    (fun data k b => StackCall.frame_update code S data hinj k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Stacks.transferProgram (program machine) hcode
    default (input.length+1) _ _ (Stacks.transfer_run input output none)
  have hv : putIO (default : Local) none=default := rfl
  refine ⟨input.length+1,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hi,hf,hv] using hr
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi,hv,Stacks.transfer_clock] using hc.le

/-- Original `source_stage` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
theorem source_stage {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out reply : CanonicalCodec.Bits)
    (time space : ℕ) (hrun : CanonicalCodec.Runs machine (PaidBoundBank.queryBits i) reply time space)
    (hempty : saved i=[]) :
    Stacks.Execution (program machine)
      ⟨some (.begin i),default,sourceState saved out (fun _ => [])⟩
      ⟨some (afterStore i),default,sourceState (Function.update saved i reply) out (fun _ => [])⟩
      (PaidBoundBank.stageBudget i reply time) := by
  have ee := (begin_call machine i saved out).trans (source_call machine i saved out reply time space hrun)
  let S := sourceState saved out (Function.update (fun _ => []) RawCall.outputSlot reply.reverse)
  have e3 := transfer_call machine (storeCode i) (storeCode_injective i) (Label.store i) (afterStore i) (fun _ => rfl) S
  have hs : S sourceOutput=reply.reverse := rfl
  have ht : S (savedSlot i)=[] := hempty
  have hf : Function.update (Function.update S sourceOutput []) (savedSlot i) reply=
      sourceState (Function.update saved i reply) out (fun _ => []) := by
    funext k
    cases k with
    | inl k =>
      dsimp only [S,sourceState,state,sourceOutput,savedSlot,Sum.elim]
      simp only [Function.update_apply]
      grind
    | inr k =>
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | inl j =>
          dsimp only [S,sourceState,state,sourceOutput,savedSlot,Sum.elim]
          simp only [Function.update_apply]
          grind
        | inr j => fin_cases j <;> rfl
  simp only [show storeCode i 0 = sourceOutput from rfl,
    show storeCode i 1 = savedSlot i from rfl] at e3
  rw [hs,ht,List.reverse_reverse,List.append_nil,hf,List.length_reverse] at e3
  simpa only [S,PaidBoundBank.stageBudget,List.length_nil,Nat.add_zero] using ee.trans e3

/-- Original `initial_empty` guarantee for the `PaidConditionalBoundSourceCall` construction; the complete source hypotheses are retained. -/
private theorem initial_empty (states : ℕ) :
    (TM2.init sourceRaw [] : Config states)=
      ⟨some (.begin 0),default,sourceState (fun _ => []) [] (fun _ => [])⟩ := by
  have hz : sourceState (fun _ => []) [] (fun _ => [])=(fun _ : Slot => []) := by
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
  simp only [TM2.init,hz,Function.update_eq_self]
  rfl

/-- Starting from an empty native bank, invoke order one, retain that same
raw answer and pay for its zero test before selecting the continuation. -/
theorem first_and_choose {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (q : Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.RedundantRational.Frac)
    (time space : ℕ)
    (hrun : CanonicalCodec.Runs machine (CanonicalCodec.natBits 1) (PaidRationalBridge.encode q) time space) :
    Stacks.Execution (program machine) (TM2.init sourceRaw [])
      ⟨some (branchChoice (decide (q.num.1=q.num.2))),default,
        sourceState (Function.update (fun _ => []) 0 (PaidRationalBridge.encode q))
          [decide (q.num.1=q.num.2)] (fun _ => [])⟩
      (PaidBoundBank.stageBudget 0 (PaidRationalBridge.encode q) time+
        11033*(1+(PaidRationalBridge.encode q).length)^2) := by
  have hfirst := source_stage machine 0 (fun _ => []) [] (PaidRationalBridge.encode q) time space hrun rfl
  rw [afterStore_first] at hfirst
  have htest := choose_after_first machine (Function.update (fun _ => []) 0 (PaidRationalBridge.encode q)) q
    (Function.update_self _ _ _)
  rw [←initial_empty] at hfirst
  exact hfirst.trans htest

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
