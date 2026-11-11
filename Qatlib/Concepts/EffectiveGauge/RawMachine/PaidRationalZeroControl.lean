/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalZeroProtocol

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Rational Zero Control

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Local`, `rawSlot`.
Proves `state_reader`, `state_output`, `update_reader`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidRationalZero

/-- Abbreviation for Slot in the Raw Machine construction. -/
abbrev Slot := PaidFractionInverse.Slot ⊕ Fin 2
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := PaidFractionInverse.Local × (Option Bool × Option Bool)
/-- Abbreviation for raw Slot in the Raw Machine construction. -/
abbrev rawSlot : Slot := .inl .raw
/-- Abbreviation for reader Slot in the Raw Machine construction. -/
abbrev readerSlot : Slot := .inr 0
/-- Abbreviation for output Slot in the Raw Machine construction. -/
abbrev outputSlot : Slot := .inr 1
/-- Constructors for Label in the Raw Machine construction. -/
inductive Label where
  | invoke (l : PaidFractionInverse.Label)
  | transfer (l : Fin 1)
  | tag
  | drain (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
/-- Initialize the machine label at its first instruction. -/
instance : Inhabited Label := ⟨.invoke default⟩
/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Definition of state in the Raw Machine construction. -/
def state (reader out : CanonicalCodec.Bits) (work : PaidFractionInverse.Slot → CanonicalCodec.Bits) :
    Slot → CanonicalCodec.Bits := StackCall.leftFrame (Stacks.stackPair reader out) work

/-- Definition of get Native in the Raw Machine construction. -/
def getNative (v : Local) := v.1
/-- Definition of put Native in the Raw Machine construction. -/
def putNative (v : Local) (w : PaidFractionInverse.Local) : Local := (w,v.2)
/-- Definition of get IO in the Raw Machine construction. -/
def getIO (v : Local) : Option Bool := v.2.2
/-- Definition of put IO in the Raw Machine construction. -/
def putIO (v : Local) (w : Option Bool) : Local := (v.1,(v.2.1,w))
/-- Definition of transfer Code in the Raw Machine construction. -/
def transferCode : Fin 2 → Slot | 0 => .inl .output | _ => readerSlot

/-- Definition of program in the Raw Machine construction. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .invoke l => StackCall.stmt Sum.inl Label.invoke (.transfer 0) getNative putNative (PaidFractionInverse.program l)
  | .transfer l => StackCall.stmt transferCode Label.transfer .tag getIO putIO (Stacks.transferProgram l)
  | .tag => .pop readerSlot (fun v b => (v.1,(b,v.2.2)))
      (.pop readerSlot (fun v b => (v.1,(v.2.1,b)))
        (.push outputSlot (fun v => v.2.1==some false && v.2.2==some false)
          (.load (fun _ => default) (.goto (fun _ => .drain 0)))))
  | .drain l => StackCall.stmt (fun _ : Fin 1 => readerSlot) Label.drain .done getIO putIO (Normalization.drainProgram l)
  | .done => .load (fun _ => default) .halt

/-- Original `state_reader` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem state_reader (reader out : CanonicalCodec.Bits)
    (work : PaidFractionInverse.Slot → CanonicalCodec.Bits) : state reader out work readerSlot=reader := rfl
/-- Original `state_output` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem state_output (reader out : CanonicalCodec.Bits)
    (work : PaidFractionInverse.Slot → CanonicalCodec.Bits) : state reader out work outputSlot=out := rfl
/-- Original `update_reader` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem update_reader (reader out bits : CanonicalCodec.Bits)
    (work : PaidFractionInverse.Slot → CanonicalCodec.Bits) :
    Function.update (state reader out work) readerSlot bits=state bits out work := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl
/-- Original `update_output` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem update_output (reader out bits : CanonicalCodec.Bits)
    (work : PaidFractionInverse.Slot → CanonicalCodec.Bits) :
    Function.update (state reader out work) outputSlot bits=state reader bits work := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

/-- The inverse is native TM2 code, not an already-compiled machine called
through a second simulator. Its measured clock stays quadratic in raw bits. -/
theorem inverse_call (p n r s : ℕ) :
    Stacks.Execution program
      ⟨some (.invoke default),default,
        state [] [] (TM2.init PaidFractionInverse.Slot.raw (PaidFractionInverse.input p n r s).reverse : PaidFractionInverse.Config).stk⟩
      ⟨some (.transfer 0),default,
        state [] [] (Function.update (fun _ => []) .output (PaidFractionInverse.output p n r s).reverse)⟩
      (10000*(1+(PaidFractionInverse.input p n r s).length)^2) := by
  obtain ⟨steps,hr,hc⟩ := PaidFractionInverse.source_exec p n r s
  obtain ⟨hn,hnc⟩ := StackCall.execution Sum.inl Label.invoke (.transfer 0) getNative putNative
    (StackCall.leftFrame (Stacks.stackPair [] []))
    (fun S k => StackCall.leftFrame_at (Stacks.stackPair [] []) S k)
    (fun S k bits => StackCall.leftFrame_update (Stacks.stackPair [] []) S k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    PaidFractionInverse.program program (fun _ => rfl) default steps _ _ hr
  have hf : PaidFractionInverse.state (PaidFractionInverse.operands [] [] [] []) [] [] [] []
      (PaidFractionInverse.output p n r s).reverse=
      Function.update (fun _ => []) PaidFractionInverse.Slot.output (PaidFractionInverse.output p n r s).reverse := by
    funext k
    cases k with
    | arg i => fin_cases i <;> rfl
    | _ => rfl
  have hdefault : putNative (default : Local) default = default := rfl
  refine ⟨steps,?_,?_⟩
  · simpa only [TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hf,state] using hn
  · simpa only [TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,state] using hnc.trans_le hc

/-- Original `tag_step` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
theorem tag_step (bits : CanonicalCodec.Bits) :
    Stacks.Execution program ⟨some .tag,default,state bits [] (fun _ => [])⟩
      ⟨some (.drain 0),default,state bits.tail.tail [twoZeroBits bits] (fun _ => [])⟩
      (8+4*bits.length) := by
  have hs : TM2.step program ⟨some .tag,default,state bits [] (fun _ => [])⟩=
      some ⟨some (.drain 0),default,state bits.tail.tail [twoZeroBits bits] (fun _ => [])⟩ := by
    simp only [TM2.step,program,TM2.stepAux,state_reader,update_reader,state_output,
      update_output,twoZeroBits]
  refine ⟨1,by rw [Stacks.run_one]; exact hs,?_⟩
  rw [Stacks.stackRunClock,hs]
  change 1+Stacks.stackClock (program .tag) default (state bits [] (fun _ => []))+0≤_
  simp only [program,Stacks.stackClock,state_reader,update_reader,state_output,List.length_nil,
    Nat.mul_zero,Nat.add_zero,Nat.zero_add]
  simp only [List.length_tail]
  omega

/-- Original `frame_target` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem frame_target {K : Type} [DecidableEq K] (code : K → Slot)
    (hinj : Function.Injective code) (S T : Slot → CanonicalCodec.Bits)
    (data : K → CanonicalCodec.Bits) (hi : ∀ k,T (code k)=data k)
    (ho : ∀ j,(∀ k,code k≠j) → T j=S j) : StackCall.frame code S data=T := by
  classical
  funext j
  by_cases hj : ∃ k,code k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StackCall.frame_at code S data hinj,hi]
  · rw [WordValidator.frame_outside code S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- Original `transferCode_injective` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
private theorem transferCode_injective : Function.Injective transferCode := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [transferCode]

/-- Original `transfer_call` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
theorem transfer_call (bits : CanonicalCodec.Bits) :
    Stacks.Execution program
      ⟨some (.transfer 0),default,
        state [] [] (Function.update (fun _ => []) PaidFractionInverse.Slot.output bits.reverse)⟩
      ⟨some .tag,default,state bits [] (fun _ => [])⟩
      (bits.length*(2*bits.length+5)+3) := by
  let S := state [] [] (Function.update (fun _ => []) PaidFractionInverse.Slot.output bits.reverse)
  let T := state bits [] (fun _ => [])
  have hi : StackCall.frame transferCode S (Stacks.stackPair bits.reverse [])=S :=
    StackCall.frame_same transferCode S _ transferCode_injective (by intro k; fin_cases k <;> rfl)
  have hf : StackCall.frame transferCode S (Stacks.stackPair [] bits)=T := by
    apply frame_target transferCode transferCode_injective S T
    · intro k; fin_cases k <;> rfl
    · intro j hj
      cases j with
      | inl k =>
        have hk : k≠PaidFractionInverse.Slot.output := fun h => hj 0 (congrArg Sum.inl h.symm)
        dsimp only [S,T,state,StackCall.leftFrame,Sum.elim]
        simp only [Function.update_of_ne hk]
      | inr k =>
        fin_cases k
        · exact (hj 1 rfl).elim
        · rfl
  obtain ⟨hr,hc⟩ := StackCall.execution transferCode Label.transfer .tag getIO putIO
    (StackCall.frame transferCode S)
    (fun data k => StackCall.frame_at transferCode S data transferCode_injective k)
    (fun data k b => StackCall.frame_update transferCode S data transferCode_injective k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Stacks.transferProgram program (fun _ => rfl)
    default (bits.reverse.length+1) _ _ (Stacks.transfer_run bits.reverse [] none)
  simp only [List.reverse_reverse,List.append_nil] at hr
  have hv : putIO (default : Local) none=default := rfl
  refine ⟨bits.reverse.length+1,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
      Option.getD_none,hi,hf,hv] using hr
  · have hclock := Stacks.transfer_clock bits.reverse [] none
    simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hclock
    simp only [List.length_reverse] at hc
    rw [hclock] at hc
    simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi,hv,List.length_reverse] using hc.le

/-- Original `drain_call` guarantee for the `PaidRationalZeroControl` construction; the complete source hypotheses are retained. -/
theorem drain_call (bits : CanonicalCodec.Bits) (flag : Bool) :
    Stacks.Execution program ⟨some (.drain 0),default,state bits [flag] (fun _ => [])⟩
      ⟨some .done,default,state [] [flag] (fun _ => [])⟩
      (bits.length^2+3*bits.length+3) := by
  let code : Fin 1 → Slot := fun _ => readerSlot
  have hinj : Function.Injective code := fun _ _ _ => Subsingleton.elim _ _
  let S := state bits [flag] (fun _ => [])
  let T := state [] [flag] (fun _ => [])
  have hi : StackCall.frame code S (Normalization.singleStack bits)=S :=
    StackCall.frame_same code S _ hinj (by intro k; fin_cases k; rfl)
  have hf : StackCall.frame code S (Normalization.singleStack [])=T := by
    apply frame_target code hinj S T
    · intro k; fin_cases k; rfl
    · intro j hj
      cases j with
      | inl k => rfl
      | inr k =>
        fin_cases k
        · exact (hj 0 rfl).elim
        · rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code Label.drain .done getIO putIO
    (StackCall.frame code S)
    (fun data k => StackCall.frame_at code S data hinj k)
    (fun data k b => StackCall.frame_update code S data hinj k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram program (fun _ => rfl)
    default (bits.length+1) _ _ (Normalization.drain_run bits none)
  have hv : putIO (default : Local) none=default := rfl
  refine ⟨bits.length+1,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
      Option.getD_none,hi,hf,hv] using hr
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi,hv,
      Normalization.drain_clock] using hc.le

end PaidRationalZero
end Qatlib.Concepts.EffectiveGauge.RawMachine
