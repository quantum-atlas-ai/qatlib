/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore

/-!
# Binary addition between registers

The addition `program` copies two source registers, reverses their working copies, invokes
native binary addition, normalizes the result, and transfers it into an initially empty
destination. The external registers are retained apart from the designated destination, and the
working stacks are empty on termination.

The native and composed execution bounds are quadratic in one plus the combined source-word
lengths. For background on the classical computational setting, see [KitaevShenVyalyi2002].

## Main statements

* `add_exact_end`: the exact terminal state and step count of native addition.
* `normalize_call`: normalization produces the canonical reversed binary sum.
* `complete`: register addition is correct with a quadratic execution bound.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Subroutine
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareSum
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib

/-- The final addition-local state, retaining the carry after all input positions have been
processed and clearing both symbol registers. -/
def finalAddVar (x y : Bits) : AddVar :=
  ⟨(addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry,none,none⟩

/-- Binary addition halts after the maximum input length plus one steps with the reversed sum on
its output stack and clock cost bounded by `addClockBound`. -/
theorem add_exact_end (x y : Bits) :
    stackRun addProgram (max x.length y.length+1) (addStart x y)=
      some ⟨none,finalAddVar x y,addStacks [] [] (bitAdd x y).reverse⟩ ∧
    stackRunClock addProgram (max x.length y.length+1) (addStart x y)≤addClockBound x y := by
  have hs : addCfgAt 0 x y=addStart x y := by
    simp [addCfgAt,addCfgLoop,addStart,addTurns,AddVar.init]
  have he : addCfgAt (max x.length y.length+1) x y=addCfgFinal x y :=
    addCfgAt_eq_final x y (by omega)
  have hout : (bitAdd x y).reverse=
      if (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry then
        true::(addTurns (max x.length y.length) ⟨false,x,y,[]⟩).os
      else (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).os := by
    cases h : (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry <;>
      simp [bitAdd,carryAdd,carryAddAux,h]
  have h := addProgram_advance x y 0 (max x.length y.length+1) (by omega)
  simp only [hs,Nat.zero_add,he] at h
  refine ⟨?_,?_⟩
  · simpa only [addCfgFinal,finalAddVar,hout] using! h.1
  · simpa only [addClockBound,carryAddPositions] using! h.2

instance instFintypeAddVar : Fintype AddVar :=
  Fintype.ofEquiv (Bool × Option Bool × Option Bool)
    { toFun := fun v => ⟨v.1,v.2.1,v.2.2⟩
      invFun := fun v => (v.carry,v.xbit,v.ybit)
      left_inv := by rintro ⟨a,b,c⟩; rfl
      right_inv := by intro v; cases v; rfl }
instance : Inhabited AddVar := ⟨AddVar.init⟩
/-- The eight external registers available to the addition subroutine. -/
abbrev Register := Fin 8
/-- Five addition workspace stacks together with a family of external registers. -/
abbrev SlotOf (K : Type) := Fin 5 ⊕ K
/-- The addition workspace and eight external registers. -/
abbrev Slot := SlotOf Register
/-- The addition-local state paired with an input/output symbol register. -/
abbrev Local := AddVar × Symbol

/-- Control labels for copying and reversing inputs, addition, normalization, saving, and
halting. -/
inductive Label where
  | copy (which : Bool) (l : NatEmit.Label)
  | reverse (which : Bool) (l : Fin 1)
  | add (l : AddLabel)
  | normalize (l : Fin 1)
  | save (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.copy false .emit⟩

/-- Replaces the addition-local component while preserving the symbol register. -/
def putAdd (v : Local) (w : AddVar) : Local := (w,v.2)
/-- Replaces the symbol register while preserving the addition-local component. -/
def putIO (v : Local) (w : Symbol) : Local := (v.1,w)

section ArbitraryRegisters
variable {K : Type} [DecidableEq K]

/-- Maps a source-register copy to the restoration and staging stacks. -/
def copyCode (src : K) : Fin 3 → (SlotOf K) | 0 => .inr src | 1 => .inl 3 | _ => .inl 4
/-- Maps reversal from the staging stack to the selected addition-input stack. -/
def reverseCode (which : Bool) : Fin 2 →
    (SlotOf K) | 0 => .inl 4 | _ => .inl (if which then 1 else 0)
/-- Embeds the three native addition stacks into the addition workspace. -/
def addCode (i : Fin 3) : (SlotOf K) := .inl (Fin.castLE (by decide) i)
/-- Selects the sum-output workspace stack for binary normalization. -/
def normalizeCode (_ : Fin 1) : SlotOf K := .inl 2
/-- Maps transfer from the sum-output stack to the destination register. -/
def saveCode (dst : K) : Fin 2 → (SlotOf K) | 0 => .inl 2 | _ => .inr dst
/-- Selects the second input copy or the addition phase after reversing an input. -/
def nextReverse (which : Bool) : Label := if which then .add .loop else .copy true .emit

/-- The program that copies two registers, adds their binary values, normalizes the sum, and
saves it to a destination register. -/
def program (x y dst : K) : Label → TM2.Stmt (fun _ : (SlotOf K) => Bool) Label Local
  | .copy which l => StackCall.stmt (copyCode (if which then y else x)) (Label.copy which)
      (.reverse which 0) Prod.snd putIO (NatEmit.program l)
  | .reverse which l => StackCall.stmt (reverseCode which) (Label.reverse which) (nextReverse which)
      Prod.snd putIO (transferProgram l)
  | .add l => StackCall.stmt addCode Label.add (.normalize 0) Prod.fst putAdd (addProgram l)
  | .normalize l => StackCall.stmt normalizeCode Label.normalize (.save 0) Prod.snd putIO (BinaryNormalize.program l)
  | .save l => StackCall.stmt (saveCode dst) Label.save .done Prod.snd putIO (transferProgram l)
  | .done => .load (fun _ => (AddVar.init,none)) .halt

/-- Combines the five working stacks with the external register store. -/
def store (W : Fin 5 → Bits) (R : K → Bits) : (SlotOf K) → Bits := Sum.elim W R

omit [DecidableEq K] in

/-- The stack map for copying an input register is injective. -/
theorem copyCode_injective (src : K) : Function.Injective (copyCode src) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [copyCode] at h ⊢

omit [DecidableEq K] in

/-- The stack map for reversing either addition input is injective. -/
theorem reverseCode_injective (which : Bool) : Function.Injective (reverseCode (K:=K) which) := by
  intro a b h
  cases which <;> fin_cases a <;> fin_cases b <;> simp [reverseCode] at h ⊢

omit [DecidableEq K] in

/-- The embedding of the native addition stacks is injective. -/
theorem addCode_injective : Function.Injective (addCode (K:=K)) := by
  intro a b h
  exact Fin.ext (congrArg (fun s : (SlotOf K) => match s with | .inl i => i.val | .inr _ => 0) h)

omit [DecidableEq K] in

/-- The stack map for saving the sum is injective. -/
theorem saveCode_injective (dst : K) : Function.Injective (saveCode dst) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [saveCode] at h ⊢

/-- Copying an input register prepends its reversed contents to the staging stack while
preserving the register, with the stated step count and quadratic clock bound. -/
theorem copy_call (x y dst : K) (which : Bool) (S : SlotOf K → Bits) (v : Local)
    (htmp : S (.inl 3)=[]) :
    let bits := S (.inr (if which then y else x))
    stackRun (program x y dst) (2*bits.length+3) ⟨some (.copy which .emit),v,S⟩ =
      some ⟨some (.reverse which 0),putIO v none,
        Function.update S (.inl 4) (bits.reverse++S (.inl 4))⟩ ∧
    stackRunClock (program x y dst) (2*bits.length+3) ⟨some (.copy which .emit),v,S⟩ ≤
      25*(1+bits.length+(S (.inl 4)).length)^2 := by
  (try dsimp only)
  let code := copyCode (if which then y else x)
  let bits := S (.inr (if which then y else x))
  have hinj := copyCode_injective (if which then y else x)
  have hsame : StackCall.frame code S (Parsing.triple bits [] (S (.inl 4)))=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    · rfl
    · exact htmp
    · rfl
  have ht : Parsing.triple bits [] (bits.reverse++S (.inl 4))=
      Function.update (Parsing.triple bits [] (S (.inl 4))) (2 : Fin 3) (bits.reverse++S (.inl 4)) := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (Parsing.triple bits [] (bits.reverse++S (.inl 4)))=
      Function.update S (.inl 4) (bits.reverse++S (.inl 4)) := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code (Label.copy which) (.reverse which 0) Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) NatEmit.program (program x y dst) (fun _ => rfl)
    v _ _ _ (NatEmit.copy_complete bits (S (.inl 4)) v.2).1
  have hio : putIO v v.2=v := rfl
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,hio] at hr hc
  exact ⟨hr,hc.trans_le (NatEmit.copy_clock_bound bits (S (.inl 4)) v.2)⟩

/-- Selects the stack map for saving the sum or reversing one of the two inputs. -/
def transferCode (dst : K) : Option Bool → Fin 2 → SlotOf K
  | none => saveCode dst | some which => reverseCode which
/-- Selects the control-label family for saving the sum or reversing an input. -/
def transferLabel : Option Bool → Fin 1 →
    Label | none => Label.save | some which => Label.reverse which
/-- Selects the return label after saving the sum or reversing an input. -/
def transferNext : Option Bool → Label | none => .done | some which => nextReverse which

omit [DecidableEq K] in

/-- Each stack map used for input reversal or saving the sum is injective. -/
theorem transferCode_injective (dst : K) (job : Option Bool) : Function.Injective (transferCode dst job) := by
  cases job with
  | none => exact saveCode_injective dst
  | some which => exact reverseCode_injective which

/-- A reversal or save transfer clears its source and prepends the reversed source to its
destination, with a quadratic clock bound. -/
theorem transfer_call (x y dst : K) (job : Option Bool) (S : SlotOf K → Bits) (v : Local) :
    let code := transferCode dst job
    let bits := S (code 0)
    let out := S (code 1)
    stackRun (program x y dst) (bits.length+1) ⟨some (transferLabel job 0),v,S⟩ =
      some ⟨some (transferNext job),putIO v none,
        Function.update (Function.update S (code 0) []) (code 1) (bits.reverse++out)⟩ ∧
    stackRunClock (program x y dst) (bits.length+1) ⟨some (transferLabel job 0),v,S⟩ ≤
      10*(1+bits.length+out.length)^2 := by
  (try dsimp only)
  let code := transferCode dst job
  let bits := S (code 0)
  let out := S (code 1)
  have hinj := transferCode_injective dst job
  have hsame : StackCall.frame code S (stackPair bits out)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i <;> rfl
  have ht : stackPair [] (bits.reverse++out)=
      Function.update (Function.update (stackPair bits out) (0 : Fin 2) []) 1 (bits.reverse++out) := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (stackPair [] (bits.reverse++out))=
      Function.update (Function.update S (code 0) []) (code 1) (bits.reverse++out) := by
    rw [ht,StackCall.frame_update _ _ _ hinj,StackCall.frame_update _ _ _ hinj,hsame]
  have hcode (l : Fin 1) : program x y dst (transferLabel job l)=
      StackCall.stmt code (transferLabel job) (transferNext job) Prod.snd putIO (transferProgram l) := by
    cases job <;> rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code (transferLabel job) (transferNext job) Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram (program x y dst) hcode
    v _ _ _ (transfer_run bits out v.2)
  have hio : putIO v v.2=v := rfl
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,hio] at hr hc
  refine ⟨hr,?_⟩
  rw [hc,transfer_clock]
  nlinarith

/-- Embeds a native three-stack addition store while retaining the external registers and
restoration and staging stacks. -/
def addFrame (R : K → Bits) (restore staging : Bits) (S : Fin 3 → Bits) : SlotOf K → Bits :=
  store (fun i => match i with | 0 => S 0 | 1 => S 1 | 2 => S 2 | 3 => restore | _ => staging) R

omit [DecidableEq K] in

/-- Reading an embedded native addition stack recovers its original contents. -/
theorem addFrame_at (R : K → Bits) (restore staging : Bits) (S : Fin 3 → Bits) (i : Fin 3) :
    addFrame R restore staging S (addCode i)=S i := by
  fin_cases i <;> rfl

/-- Updating a native addition stack commutes with its embedding into the working store. -/
theorem addFrame_update (R : K → Bits) (restore staging : Bits) (S : Fin 3 → Bits) (i : Fin 3) (bits : Bits) :
    addFrame R restore staging (Function.update S i bits)=
      Function.update (addFrame R restore staging S) (addCode i) bits := by
  funext slot
  cases slot with
  | inl j => fin_cases i <;> fin_cases j <;> rfl
  | inr j => fin_cases i <;> rfl

/-- The embedded addition consumes both inputs and produces the reversed sum with the native
final local state and clock bound. -/
theorem add_call (x y dst : K) (a b : Bits) (R : K → Bits) (restore staging : Bits) (v : Local) :
    stackRun (program x y dst) (max a.length b.length+1)
      ⟨some (.add .loop),putAdd v AddVar.init,addFrame R restore staging (addStacks a b [])⟩ =
      some ⟨some (.normalize 0),putAdd v (finalAddVar a b),
        addFrame R restore staging (addStacks [] [] (bitAdd a b).reverse)⟩ ∧
    stackRunClock (program x y dst) (max a.length b.length+1)
      ⟨some (.add .loop),putAdd v AddVar.init,addFrame R restore staging (addStacks a b [])⟩ ≤ addClockBound a b := by
  obtain ⟨hr,hc⟩ := StackCall.execution addCode Label.add (.normalize 0) Prod.fst putAdd
    (addFrame R restore staging) (addFrame_at R restore staging) (addFrame_update R restore staging)
    (fun _ _ => rfl) (fun _ _ _ => rfl) addProgram (program x y dst) (fun _ => rfl)
    v _ _ _ (add_exact_end a b).1
  simp only [StackCall.cfg,addStart,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at hr hc
  exact ⟨hr,hc.trans_le (add_exact_end a b).2⟩

/-- Normalization replaces the reversed sum by the reversed canonical binary expansion of its
value, with a quadratic clock bound. -/
theorem normalize_call (x y dst : K) (S : SlotOf K → Bits) (v : Local) :
    ∃ ticks last, stackRun (program x y dst) ticks ⟨some (.normalize 0),v,S⟩ =
      some ⟨some (.save 0),putIO v last,Function.update S (.inl 2)
        (binaryValue (S (.inl 2)).reverse).bits.reverse⟩ ∧
      stackRunClock (program x y dst) ticks ⟨some (.normalize 0),v,S⟩ ≤
        20*(1+(S (.inl 2)).length)^2 := by
  let code : Fin 1 → SlotOf K := normalizeCode
  let bits := S (.inl 2)
  have hinj : Function.Injective code := fun a b _ => Subsingleton.elim a b
  have hsame : StackCall.frame code S (Normalization.singleStack bits)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    rfl
  have hfinal (out : Bits) : StackCall.frame code S (Normalization.singleStack out)=
      Function.update S (.inl 2) out := by
    have ht : Normalization.singleStack out=
        Function.update (Normalization.singleStack bits) (0 : Fin 1) out := by
      funext i
      fin_cases i
      rfl
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    rfl
  obtain ⟨ticks,last,hr,hc⟩ := BinaryNormalize.complete bits v.2
  obtain ⟨hN,hNC⟩ := StackCall.execution code Label.normalize (.save 0) Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) BinaryNormalize.program (program x y dst) (fun _ => rfl)
    v _ _ _ hr
  have hio : putIO v v.2=v := rfl
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,hio] at hN hNC
  exact ⟨ticks,last,hN,hNC.trans_le hc⟩

/-- The native addition clock bound is at most `22 * (1 + a.length + b.length)^2`. -/
theorem native_clock_bound (a b : Bits) : addClockBound a b ≤ 22*(1+a.length+b.length)^2 := by
  let N := 1+a.length+b.length
  have hN : 1≤N := by dsimp [N]; omega
  have hsteps : max a.length b.length+1≤N := by dsimp [N]; omega
  have hfactor : 4*(a.length+b.length+max a.length b.length)+14≤22*N := by dsimp [N]; omega
  have h := Nat.mul_le_mul hsteps hfactor
  change (max a.length b.length+1)*(4*(a.length+b.length+max a.length b.length)+14) ≤ 22*N^2
  nlinarith only [h]

/-- With an empty destination, the addition subroutine writes the canonical binary sum there and
halts with empty workspace within a quadratic execution bound. -/
theorem complete (x y dst : K) (R : K → Bits) (hfresh : R dst=[]) :
    Execution (program x y dst)
      ⟨some (.copy false .emit),(AddVar.init,none),store (fun _ => []) R⟩
      ⟨none,(AddVar.init,none),store (fun _ => [])
        (Function.update R dst (binaryValue (R x)+binaryValue (R y)).bits)⟩
      (300*(1+(R x).length+(R y).length)^2) := by
  let a := R x
  let b := R y
  let rawSum := bitAdd a b
  let p := (binaryValue a+binaryValue b).bits
  let v : Local := (AddVar.init,none)
  let vf : Local := (finalAddVar a b,none)
  let S0 := store (fun _ => []) R
  let S1 := Function.update S0 (.inl 4) a.reverse
  let S2 := Function.update (Function.update S1 (.inl 4) []) (.inl 0) a
  let S3 := Function.update S2 (.inl 4) b.reverse
  let S4 := Function.update (Function.update S3 (.inl 4) []) (.inl 1) b
  let S5 := addFrame R [] [] (addStacks [] [] rawSum.reverse)
  let S6 := Function.update S5 (.inl 2) p.reverse
  let S7 := Function.update (Function.update S6 (.inl 2) []) (.inr dst) p
  have hS4 : S4=addFrame R [] [] (addStacks a b []) := by
    funext slot
    cases slot with
    | inl i => fin_cases i <;> rfl
    | inr i => rfl
  have hS7 : S7=store (fun _ => []) (Function.update R dst p) := by
    funext slot
    cases slot with
    | inl i => fin_cases i <;> rfl
    | inr i =>
      simp only [S7,S6,S5,addFrame,store,Function.update_apply,Sum.elim_inr,
        Sum.inr.injEq,Sum.inr_ne_inl,↓reduceIte]
  have h00 : S0 (.inr x)=a := rfl
  have h04 : S0 (.inl 4)=[] := rfl
  have hC0 := copy_call x y dst false S0 v (by rfl)
  have e0 : Execution (program x y dst) ⟨some (.copy false .emit),v,S0⟩
      ⟨some (.reverse false 0),v,S1⟩ (25*(1+a.length)^2) := by
    refine ⟨2*a.length+3,?_,?_⟩
    · simpa only [Bool.false_eq_true,↓reduceIte,h00,h04,List.append_nil] using! hC0.1
    · simpa only [Bool.false_eq_true,↓reduceIte,h00,h04,List.length_nil,Nat.add_zero] using! hC0.2
  have h14 : S1 (.inl 4)=a.reverse := rfl
  have h10 : S1 (.inl 0)=[] := rfl
  have hT0 := transfer_call x y dst (some false) S1 v
  have e1 : Execution (program x y dst) ⟨some (.reverse false 0),v,S1⟩
      ⟨some (.copy true .emit),v,S2⟩ (10*(1+a.length)^2) := by
    refine ⟨a.length+1,?_,?_⟩
    · simpa only [transferCode,transferLabel,transferNext,reverseCode,nextReverse,Bool.false_eq_true,
        ↓reduceIte,h14,h10,List.length_reverse,List.reverse_reverse,List.append_nil] using! hT0.1
    · simpa only [transferCode,transferLabel,reverseCode,Bool.false_eq_true,↓reduceIte,h14,h10,
        List.length_reverse,List.length_nil,Nat.add_zero] using! hT0.2
  have h2y : S2 (.inr y)=b := rfl
  have h24 : S2 (.inl 4)=[] := rfl
  have hC1 := copy_call x y dst true S2 v (by rfl)
  have e2 : Execution (program x y dst) ⟨some (.copy true .emit),v,S2⟩
      ⟨some (.reverse true 0),v,S3⟩ (25*(1+b.length)^2) := by
    refine ⟨2*b.length+3,?_,?_⟩
    · simpa only [↓reduceIte,h2y,h24,List.append_nil] using! hC1.1
    · simpa only [↓reduceIte,h2y,h24,List.length_nil,Nat.add_zero] using! hC1.2
  have h34 : S3 (.inl 4)=b.reverse := rfl
  have h31 : S3 (.inl 1)=[] := rfl
  have hT1 := transfer_call x y dst (some true) S3 v
  have e3 : Execution (program x y dst) ⟨some (.reverse true 0),v,S3⟩
      ⟨some (.add .loop),v,S4⟩ (10*(1+b.length)^2) := by
    refine ⟨b.length+1,?_,?_⟩
    · simpa only [transferCode,transferLabel,transferNext,reverseCode,nextReverse,↓reduceIte,h34,h31,
        List.length_reverse,List.reverse_reverse,List.append_nil] using! hT1.1
    · simpa only [transferCode,transferLabel,reverseCode,↓reduceIte,h34,h31,
        List.length_reverse,List.length_nil,Nat.add_zero] using! hT1.2
  have hA := add_call x y dst a b R [] [] v
  have e4 : Execution (program x y dst) ⟨some (.add .loop),v,S4⟩
      ⟨some (.normalize 0),vf,S5⟩ (22*(1+a.length+b.length)^2) := by
    refine ⟨max a.length b.length+1,?_,?_⟩
    · rw [hS4]
      exact hA.1
    · rw [hS4]
      exact hA.2.trans (native_clock_bound a b)
  obtain ⟨nTicks,last,hN,hNC⟩ := normalize_call x y dst S5 vf
  have h52 : S5 (.inl 2)=rawSum.reverse := rfl
  have hsum : binaryValue rawSum=binaryValue a+binaryValue b := bitAdd_value a b
  simp only [h52,List.reverse_reverse,hsum,List.length_reverse] at hN hNC
  have e5 : Execution (program x y dst) ⟨some (.normalize 0),vf,S5⟩
      ⟨some (.save 0),putIO vf last,S6⟩ (20*(1+rawSum.length)^2) := ⟨nTicks,hN,hNC⟩
  have h62 : S6 (.inl 2)=p.reverse := rfl
  have h6d : S6 (.inr dst)=[] := hfresh
  have hSave := transfer_call x y dst none S6 (putIO vf last)
  have e6 : Execution (program x y dst) ⟨some (.save 0),putIO vf last,S6⟩
      ⟨some .done,vf,S7⟩ (10*(1+p.length)^2) := by
    refine ⟨p.length+1,?_,?_⟩
    · simpa only [transferCode,transferLabel,transferNext,saveCode,h62,h6d,List.length_reverse,
        List.reverse_reverse,List.append_nil] using! hSave.1
    · simpa only [transferCode,transferLabel,saveCode,h62,h6d,List.length_reverse,
        List.length_nil,Nat.add_zero] using! hSave.2
  have e7 : Execution (program x y dst) ⟨some .done,vf,S7⟩ ⟨none,v,S7⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  have hall := ((((((e0.trans e1).trans e2).trans e3).trans e4).trans e5).trans e6).trans e7
  rw [hS7] at hall
  apply hall.mono
  let N := 1+a.length+b.length
  have hN : 1≤N := by dsimp [N]; omega
  have ha : 1+a.length≤N := by dsimp [N]; omega
  have hb : 1+b.length≤N := by dsimp [N]; omega
  have hraw : rawSum.length ≤ max a.length b.length+1 := carryAdd_length false a b
  have hlen := BinaryNormalize.canonical_length rawSum
  rw [hsum] at hlen
  have hp : 1+p.length≤2*N := by dsimp only [p,N]; omega
  have hraw' : 1+rawSum.length≤2*N := by dsimp [N]; omega
  have ha2 := Nat.pow_le_pow_left ha 2
  have hb2 := Nat.pow_le_pow_left hb 2
  have hp2 := Nat.pow_le_pow_left hp 2
  have hr2 := Nat.pow_le_pow_left hraw' 2
  have hOne : 1≤N^2 := by have h := Nat.pow_le_pow_left hN 2; simpa using! h
  change 25*(1+a.length)^2+10*(1+a.length)^2+25*(1+b.length)^2+10*(1+b.length)^2+
    22*N^2+20*(1+rawSum.length)^2+10*(1+p.length)^2+1 ≤ 300*N^2
  nlinarith only [ha2,hb2,hp2,hr2,hOne]

end ArbitraryRegisters

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareSum
