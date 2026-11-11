/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundThresholdOrder

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Threshold Control

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Local`, `initialCmp`.
Proves `sumCode_injective`, `frame_target`, `sum_call`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression.Threshold

/-- Constructors for Slot in the Raw Machine construction. -/
inductive Slot where
  | input (right : Bool)
  | arith (k : PaidSumProducts.Slot)
  | cmp (k : ReadonlyCompare.Slot)
  | output
  deriving DecidableEq,Fintype
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := PaidSumProducts.Local × ReadonlyCompare.Local
/-- Definition of initial Cmp in the Raw Machine construction. -/
def initialCmp : ReadonlyCompare.Local := ((.eq,none,none),none)
/-- Initialize the arithmetic and comparison registers at their default values. -/
instance : Inhabited Local := ⟨(default,initialCmp)⟩
/-- Constructors for Label in the Raw Machine construction. -/
inductive Label where
  | sum (right : Bool) (l : PaidSumProducts.Label)
  | compare (l : ReadonlyCompare.Label)
  | choose
  | drain (right : Bool) (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
/-- Initialize the machine label at its first instruction. -/
instance : Inhabited Label := ⟨.sum false default⟩
/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Definition of dest in the Raw Machine construction. -/
def dest (right : Bool) : ReadonlyCompare.Slot := if right then .second else .first

/-- Definition of sum Code in the Raw Machine construction. -/
def sumCode (right : Bool) : PaidSumProducts.Slot → Slot
  | .raw => .input right
  | .output => .cmp (dest right)
  | k => .arith k

/-- Definition of get Arith in the Raw Machine construction. -/
def getArith (v : Local) := v.1
/-- Definition of put Arith in the Raw Machine construction. -/
def putArith (v : Local) (w : PaidSumProducts.Local) : Local := (w,v.2)
/-- Definition of get Cmp in the Raw Machine construction. -/
def getCmp (v : Local) := v.2
/-- Definition of put Cmp in the Raw Machine construction. -/
def putCmp (v : Local) (w : ReadonlyCompare.Local) : Local := (v.1,w)
/-- Definition of get IO in the Raw Machine construction. -/
def getIO (v : Local) := v.2.2
/-- Definition of put IO in the Raw Machine construction. -/
def putIO (v : Local) (w : Option Bool) : Local := (v.1,(v.2.1,w))

/-- Definition of after Sum in the Raw Machine construction. -/
def afterSum (right : Bool) : Label := if right then .compare default else .sum true default

/-- Definition of program in the Raw Machine construction. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .sum right l => StackCall.stmt (sumCode right) (Label.sum right) (afterSum right) getArith putArith (PaidSumProducts.program l)
  | .compare l => StackCall.stmt Slot.cmp Label.compare .choose getCmp putCmp (ReadonlyCompare.program l)
  | .choose => .push .output (fun v => decide (v.2.1.1≠BinaryCompare.Tag.gt))
      (.load (fun _ => default) (.goto (fun _ => .drain false 0)))
  | .drain right l => StackCall.stmt (fun _ : Fin 1 => .cmp (dest right)) (Label.drain right)
      (if right then .done else .drain true 0) getIO putIO (Normalization.drainProgram l)
  | .done => .load (fun _ => default) .halt

/-- Definition of state in the Raw Machine construction. -/
def state (inputs : Bool → CanonicalCodec.Bits) (cmp : ReadonlyCompare.Slot → CanonicalCodec.Bits)
    (out : CanonicalCodec.Bits) (work : PaidSumProducts.Slot → CanonicalCodec.Bits) : Slot → CanonicalCodec.Bits
  | .input right => inputs right
  | .arith k => work k
  | .cmp k => cmp k
  | .output => out

set_option maxHeartbeats 1000000 in
/-- Original `sumCode_injective` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
private theorem sumCode_injective (right : Bool) : Function.Injective (sumCode right) := by
  intro a b h
  cases a <;> cases b <;> simp_all [sumCode]

/-- Original `frame_target` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
private theorem frame_target {K : Type} [DecidableEq K] (code : K → Slot) (hinj : Function.Injective code)
    (S T : Slot → CanonicalCodec.Bits) (data : K → CanonicalCodec.Bits)
    (hi : ∀ k,T (code k)=data k) (ho : ∀ j,(∀ k,code k≠j) → T j=S j) : StackCall.frame code S data=T := by
  classical
  funext j
  by_cases hj : ∃ k,code k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StackCall.frame_at code S data hinj,hi]
  · rw [WordValidator.frame_outside code S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- A native sum-products call consumes its already-framed argument word.
The other input, earlier result and external output remain unchanged.
Argument framing and denominator orientation are separate paid stages. -/
theorem sum_call (right : Bool) (a b c d : ℕ) (inputs : Bool → CanonicalCodec.Bits)
    (cmp : ReadonlyCompare.Slot → CanonicalCodec.Bits) (out : CanonicalCodec.Bits)
    (hinput : inputs right=(PaidSumProducts.input a b c d).reverse) (hempty : cmp (dest right)=[]) :
    Stacks.Execution program
      ⟨some (.sum right default),default,state inputs cmp out (fun _ => [])⟩
      ⟨some (afterSum right),default,
        state (Function.update inputs right [])
          (Function.update cmp (dest right) (CanonicalCodec.natBits (a*b+c*d)).reverse) out (fun _ => [])⟩
      (200000*(1+(PaidSumProducts.input a b c d).length)^3) := by
  let S := state inputs cmp out (fun _ => [])
  let T := state (Function.update inputs right [])
      (Function.update cmp (dest right) (CanonicalCodec.natBits (a*b+c*d)).reverse) out (fun _ => [])
  have hinj := sumCode_injective right
  have hi : StackCall.frame (sumCode right) S
      (TM2.init PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse : PaidSumProducts.Config).stk=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro k
    cases k with
    | raw => exact hinput
    | output => exact hempty
    | _ => rfl
  let last := PaidSumProducts.state [] [] (PaidSumProducts.operands [] [] [] []) [] [] [] [] []
      (CanonicalCodec.natBits (a*b+c*d)).reverse
  have hf : StackCall.frame (sumCode right) S last=T := by
    apply frame_target _ hinj S T last
    · intro k
      cases k with
      | raw => exact Function.update_self _ _ _
      | output => exact Function.update_self _ _ _
      | _ => rfl
    · intro j hj
      cases j with
      | input other =>
        have hn : other≠right := fun h => hj .raw (congrArg Slot.input h.symm)
        exact Function.update_of_ne hn _ _
      | cmp k =>
        have hn : k≠dest right := fun h => hj .output (congrArg Slot.cmp h.symm)
        exact Function.update_of_ne hn _ _
      | arith k => rfl
      | output => rfl
  change StackCall.frame (sumCode right) S
    (PaidSumProducts.state [] [] (PaidSumProducts.operands [] [] [] []) [] [] [] [] []
      (CanonicalCodec.natBits (a*b+c*d)).reverse)=T at hf
  obtain ⟨steps,hr,hc⟩ := PaidSumProducts.source_exec a b c d
  obtain ⟨hn,hnc⟩ := StackCall.execution (sumCode right) (Label.sum right) (afterSum right) getArith putArith
    (StackCall.frame (sumCode right) S)
    (fun data k => StackCall.frame_at _ S data hinj k)
    (fun data k bits => StackCall.frame_update _ S data hinj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) PaidSumProducts.program program (fun _ => rfl)
    default steps _ _ hr
  have hl : (TM2.init PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse : PaidSumProducts.Config).l = some default := rfl
  have hv : (TM2.init PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse : PaidSumProducts.Config).var = default := rfl
  have hd : putArith (default : Local) default = default := rfl
  refine ⟨steps,?_,?_⟩
  · simpa only [StackCall.cfg,hl,hv,hd,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hi,hf] using hn
  · simpa only [StackCall.cfg,hl,hv,hd,Option.map_some,Option.getD_some,hi] using hnc.trans_le hc

/-- Definition of cmp Final in the Raw Machine construction. -/
def cmpFinal (left right : CanonicalCodec.Bits) : Local :=
  (default,((ReadonlyCompare.order left right,none,none),none))

/-- Original `compare_call` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
theorem compare_call (left right out : CanonicalCodec.Bits) :
    Stacks.Execution program
      ⟨some (.compare default),default,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] []) out (fun _ => [])⟩
      ⟨some .choose,cmpFinal left right,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] []) out (fun _ => [])⟩
      (100*(1+left.length+right.length)^2) := by
  let S := state (fun _ => []) (ReadonlyCompare.store left right [] [] []) out (fun _ => [])
  have hinj : Function.Injective Slot.cmp := fun _ _ h => Slot.cmp.inj h
  have hi : StackCall.frame Slot.cmp S (ReadonlyCompare.store left right [] [] [])=S :=
    StackCall.frame_same Slot.cmp S _ hinj (fun _ => rfl)
  obtain ⟨steps,hr,hc⟩ := ReadonlyCompare.complete left right initialCmp
  obtain ⟨hn,hnc⟩ := StackCall.execution Slot.cmp Label.compare .choose getCmp putCmp
    (StackCall.frame Slot.cmp S)
    (fun data k => StackCall.frame_at _ S data hinj k)
    (fun data k b => StackCall.frame_update _ S data hinj k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) ReadonlyCompare.program program (fun _ => rfl)
    default steps _ _ hr
  have hl : ReadonlyCompare.Label.start = (default : ReadonlyCompare.Label) := rfl
  have hiVar : putCmp (default : Local) initialCmp = default := rfl
  have hfVar : putCmp (default : Local) ((ReadonlyCompare.order left right,none,none),none) = cmpFinal left right := rfl
  refine ⟨steps,?_,?_⟩
  · simpa only [StackCall.cfg,hl,hiVar,hfVar,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hi] using hn
  · simpa only [StackCall.cfg,hl,hiVar,Option.map_some,Option.getD_some,hi] using hnc.trans_le hc

/-- Original `state_output` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
private theorem state_output (inputs : Bool → CanonicalCodec.Bits) (cmp : ReadonlyCompare.Slot → CanonicalCodec.Bits)
    (out : CanonicalCodec.Bits) (work : PaidSumProducts.Slot → CanonicalCodec.Bits) :
    state inputs cmp out work .output=out := rfl

/-- Original `update_output` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
private theorem update_output (inputs : Bool → CanonicalCodec.Bits) (cmp : ReadonlyCompare.Slot → CanonicalCodec.Bits)
    (out bits : CanonicalCodec.Bits) (work : PaidSumProducts.Slot → CanonicalCodec.Bits) :
    Function.update (state inputs cmp out work) Slot.output bits=state inputs cmp bits work := by
  funext k
  cases k <;> rfl

/-- Original `choose_step` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
theorem choose_step (left right : CanonicalCodec.Bits) :
    Stacks.Execution program
      ⟨some .choose,cmpFinal left right,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] []) [] (fun _ => [])⟩
      ⟨some (.drain false 0),default,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] [])
          [decide (ReadonlyCompare.order left right≠BinaryCompare.Tag.gt)] (fun _ => [])⟩ 4 := by
  have hs : TM2.step program
      ⟨some .choose,cmpFinal left right,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] []) [] (fun _ => [])⟩=
      some ⟨some (.drain false 0),default,
        state (fun _ => []) (ReadonlyCompare.store left right [] [] [])
          [decide (ReadonlyCompare.order left right≠BinaryCompare.Tag.gt)] (fun _ => [])⟩ := by
    simp only [TM2.step,program,TM2.stepAux,state_output,update_output,cmpFinal]
  refine ⟨1,by rw [Stacks.run_one]; exact hs,?_⟩
  rw [Stacks.stackRunClock,hs]
  exact le_rfl

/-- Original `drain_call` guarantee for the `PaidBoundThresholdControl` construction; the complete source hypotheses are retained. -/
theorem drain_call (right : Bool) (cmp : ReadonlyCompare.Slot → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    Stacks.Execution program
      ⟨some (.drain right 0),default,state (fun _ => []) cmp out (fun _ => [])⟩
      ⟨some (if right then .done else .drain true 0),default,
        state (fun _ => []) (Function.update cmp (dest right) []) out (fun _ => [])⟩
      ((cmp (dest right)).length^2+3*(cmp (dest right)).length+3) := by
  let code : Fin 1 → Slot := fun _ => .cmp (dest right)
  have hinj : Function.Injective code := fun _ _ _ => Subsingleton.elim _ _
  let S := state (fun _ => []) cmp out (fun _ => [])
  let T := state (fun _ => []) (Function.update cmp (dest right) []) out (fun _ => [])
  have hi : StackCall.frame code S (Normalization.singleStack (cmp (dest right)))=S :=
    StackCall.frame_same code S _ hinj (by intro k; fin_cases k; rfl)
  have hf : StackCall.frame code S (Normalization.singleStack [])=T := by
    apply frame_target code hinj S T
    · intro k; fin_cases k; exact Function.update_self _ _ _
    · intro j hj
      cases j with
      | input k => rfl
      | arith k => rfl
      | output => rfl
      | cmp k =>
        have h : k≠dest right := fun h => hj 0 (congrArg Slot.cmp h.symm)
        exact Function.update_of_ne h _ _
  obtain ⟨hr,hc⟩ := StackCall.execution code (Label.drain right) (if right then .done else .drain true 0) getIO putIO
    (StackCall.frame code S)
    (fun data k => StackCall.frame_at _ S data hinj k)
    (fun data k b => StackCall.frame_update _ S data hinj k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram program (fun _ => rfl)
    default ((cmp (dest right)).length+1) _ _ (Normalization.drain_run (cmp (dest right)) none)
  have hv : putIO (default : Local) none=default := rfl
  refine ⟨(cmp (dest right)).length+1,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hi,hf,hv] using hr
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi,hv,Normalization.drain_clock] using hc.le

end PaidBoundCompression.Threshold
end Qatlib.Concepts.EffectiveGauge.RawMachine
