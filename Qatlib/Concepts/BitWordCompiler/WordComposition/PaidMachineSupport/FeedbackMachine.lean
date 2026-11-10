/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.FeedbackWrite
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open scoped Classical

inductive Slot where | bank | saved | index | indexTemp deriving DecidableEq, Fintype
inductive Label where
  | counter (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.Label)
  | decide | copy | patch | restore | clear
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.counter .borrow⟩
abbrev Local :=
    Bool × Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.Local × Option Bool

def getCounter (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.Local :=
    v.2.1
def putCounter (v : Local)
    (c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.Local) : Local :=
    (v.1, c, v.2.2)
def putIO (v : Local) (b : Option Bool) : Local := (v.1, v.2.1, b)
def counterCode : Fin 2 → Slot | 0 => .index | _ => .indexTemp

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .counter l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt counterCode Label.counter .decide getCounter putCounter (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.program l)
  | .decide => .branch (fun v => (getCounter v).1)
      (.goto (fun _ => .copy)) (.goto (fun _ => .patch))
  | .copy => .pop .bank putIO (.push .saved (fun v => v.2.2.getD false)
      (.pop .bank putIO (.push .saved (fun v => v.2.2.getD false)
        (.goto (fun _ => .counter .borrow)))))
  | .patch => .pop .bank (fun v _ => v) (.pop .bank (fun v _ => v)
      (.push .bank (fun v => v.1) (.push .bank (fun _ => true) (.goto (fun _ => .restore)))))
  | .restore => .pop .saved putIO (.branch (fun v => v.2.2.isSome)
      (.push .bank (fun v => v.2.2.getD false) (.goto (fun _ => .restore)))
      (.goto (fun _ => .clear)))
  | .clear => .pop .index putIO (.branch (fun v => v.2.2.isSome)
      (.goto (fun _ => .clear)) .halt)

def store (bank saved index temporary : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .bank => bank | .saved => saved | .index => index | .indexTemp => temporary

@[simp] private theorem store_bank (b s i t x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store b s i t) Slot.bank x = store x s i t := by
  funext k
  cases k <;> rfl

@[simp] private theorem store_saved (b s i t x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store b s i t) Slot.saved x = store b x i t := by
  funext k
  cases k <;> rfl

@[simp] private theorem store_index (b s i t x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store b s i t) Slot.index x = store b s x t := by
  funext k
  cases k <;> rfl

@[simp] private theorem store_temporary (b s i t x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store b s i t) Slot.indexTemp x = store b s i x := by
  funext k
  cases k <;> rfl

def slotBits : Option Bool → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | none => [false, false] | some b => [true, b]
def bankBits (slots : List (Option Bool)) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := slots.flatMap slotBits

@[simp] theorem bankBits_length (slots : List (Option Bool)) : (bankBits slots).length = 2 * slots.length := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    rw [show bankBits (a::slots) = slotBits a ++ bankBits slots from rfl, List.length_append, ih]
    cases a <;> simp [slotBits, Nat.mul_add, Nat.add_comm]

private theorem one (l : Label) (v : Local) (S : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (last : TM2.Cfg (fun _ : Slot => Bool) Label Local)
    (h : TM2.step program ⟨some l,v,S⟩ = some last) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some l,v,S⟩ last (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock (program l) v S + 1) := by
  refine ⟨1, ?_, ?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one] using h
  · simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, h,
      Nat.add_comm]

private theorem counter_call (bank saved index temporary : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (ticks : ℕ) (c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.Local) (index' temporary' : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (h : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.program ticks ⟨some .borrow,getCounter v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair index temporary⟩ =
      some ⟨none,c,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair index' temporary'⟩) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program ticks ⟨some (.counter .borrow),v,store bank saved index temporary⟩ =
      some ⟨some .decide,putCounter v c,store bank saved index' temporary'⟩ ∧
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks ⟨some (.counter .borrow),v,store bank saved index temporary⟩ =
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.program ticks ⟨some .borrow,getCounter v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair index temporary⟩ := by
  have hinj : Function.Injective counterCode := by decide
  let S := store bank saved index temporary
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame counterCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair index temporary) = S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _ hinj
    intro k
    fin_cases k <;> rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame counterCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair index' temporary') = store bank saved index' temporary' := by
    funext k
    cases k
    · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside counterCode S _ _ (by intro i; fin_cases i <;> simp [counterCode])]
      rfl
    · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside counterCode S _ _ (by intro i; fin_cases i <;> simp [counterCode])]
      rfl
    · exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at counterCode S _ hinj 0
    · exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at counterCode S _ hinj 1
  obtain ⟨hr,hc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution counterCode Label.counter .decide getCounter putCounter
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame counterCode S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data hinj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data hinj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.program program (fun _ => rfl) v ticks _ _ h
  simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none, Option.getD_none,
    hs, hf, S, getCounter, putCounter] using And.intro hr hc

private theorem clear_execution (bank saved index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .clear,v,store bank saved index []⟩
      ⟨none,putIO v none,store bank saved [] []⟩ (3 * (1 + index.length)^2) := by
  induction index generalizing v with
  | nil =>
    have hs : TM2.step program ⟨some .clear,v,store bank saved [] []⟩ =
        some ⟨none,putIO v none,store bank saved [] []⟩ := by
      simp [program,TM2.step,TM2.stepAux,store,putIO]
    exact (one _ _ _ _ hs).mono
        (by simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO])
  | cons b index ih =>
    have hs : TM2.step program ⟨some .clear,v,store bank saved (b::index) []⟩ =
        some ⟨some .clear,putIO v (some b),store bank saved index []⟩ := by
      simp [program,TM2.step,TM2.stepAux,store,putIO]
    have he := (one _ _ _ _ hs).trans (ih (putIO v (some b)))
    apply he.mono
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO]
    nlinarith

@[simp] theorem slotBits_length (a : Option Bool) : (slotBits a).length = 2 := by cases a <;> rfl

private theorem restore_execution (bank saved index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .restore,v,store bank saved index []⟩
      ⟨none,putIO v none,store (saved.reverse ++ bank) [] [] []⟩
      (5 * (saved.length + 1) * (1 + bank.length + saved.length) + 3 * (1 + index.length)^2) := by
  induction saved generalizing bank v with
  | nil =>
    have hs : TM2.step program ⟨some .restore,v,store bank [] index []⟩ =
        some ⟨some .clear,putIO v none,store bank [] index []⟩ := by
      simp [program,TM2.step,TM2.stepAux,store,putIO]
    have he := (one _ _ _ _ hs).trans (clear_execution bank [] index (putIO v none))
    have hh : putIO (putIO v none) none = putIO v none := rfl
    rw [hh] at he
    apply he.mono
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO]
    omega
  | cons b saved ih =>
    have hs : TM2.step program ⟨some .restore,v,store bank (b::saved) index []⟩ =
        some ⟨some .restore,putIO v (some b),store (b::bank) saved index []⟩ := by
      simp [program,TM2.step,TM2.stepAux,store,putIO]
    have he := (one _ _ _ _ hs).trans (ih (b::bank) (putIO v (some b)))
    have hh : putIO (putIO v (some b)) none = putIO v none := rfl
    rw [hh] at he
    have heq : saved.reverse ++ b::bank = (b::saved).reverse ++ bank := by simp
    rw [heq] at he
    apply he.mono
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO]
    nlinarith

private theorem patch_execution (old : Option Bool) (tail saved index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .patch,v,store (slotBits old ++ tail) saved index []⟩
      ⟨some .restore,v,store (true::v.1::tail) saved index []⟩
      (10 * (1 + (slotBits old ++ tail).length + saved.length)) := by
  have hs : TM2.step program ⟨some .patch,v,store (slotBits old ++ tail) saved index []⟩ =
      some ⟨some .restore,v,store (true::v.1::tail) saved index []⟩ := by
    cases old <;> simp [slotBits,program,TM2.step,TM2.stepAux,store]
  apply (one _ _ _ _ hs).mono
  cases old <;> simp
      [slotBits,program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store]
  all_goals omega

private theorem copy_execution (a : Option Bool) (tail saved index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    ∃ w : Local, w.1 = v.1 ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .copy,v,store (slotBits a ++ tail) saved index []⟩
        ⟨some (.counter .borrow),w,store tail ((slotBits a).reverse ++ saved) index []⟩
        (10 * (1 + (slotBits a ++ tail).length + saved.length)) := by
  cases a with
  | none =>
    let w := putIO v (some false)
    refine ⟨w,rfl,?_⟩
    have hs : TM2.step program ⟨some .copy,v,store (slotBits none ++ tail) saved index []⟩ =
        some ⟨some (.counter .borrow),w,store tail ((slotBits none).reverse ++ saved) index []⟩ := by
      simp [slotBits,program,TM2.step,TM2.stepAux,store,putIO,w]
    apply (one _ _ _ _ hs).mono
    simp [slotBits,program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO]
    omega
  | some b =>
    let w := putIO v (some b)
    refine ⟨w,rfl,?_⟩
    have hs : TM2.step program ⟨some .copy,v,store (slotBits (some b) ++ tail) saved index []⟩ =
        some ⟨some (.counter .borrow),w,store tail ((slotBits (some b)).reverse ++ saved) index []⟩ := by
      simp [slotBits,program,TM2.step,TM2.stepAux,store,putIO,w]
    apply (one _ _ _ _ hs).mono
    simp [slotBits,program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,putIO]
    omega

@[simp] theorem bankBits_cons (a : Option Bool) (slots : List (Option Bool)) :
    bankBits (a::slots) = slotBits a ++ bankBits slots := rfl

def done (feedback : Bool) : Local := (feedback,(false,none),none)

theorem feedback_machine_execution (front : List (Option Bool)) (old : Option Bool)
    (suffix : List (Option Bool)) (saved index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (hi : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue index = front.length) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.counter .borrow),v,store (bankBits (front ++ old::suffix)) saved index []⟩
      ⟨none,done v.1,store (saved.reverse ++ bankBits (front ++ some v.1::suffix)) [] [] []⟩
      (100 * (front.length + 1) *
        (1 + (bankBits (front ++ old::suffix)).length + saved.length + index.length)^2) := by
  induction front generalizing saved index v with
  | nil =>
    let B := 1 + (bankBits (old::suffix)).length + saved.length + index.length
    let v1 := putCounter v (false,none)
    obtain ⟨hr,hc⟩ :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.decrement_zero index
        (getCounter v) (by simpa using hi)
    obtain ⟨hN,hNC⟩ := counter_call (bankBits (old::suffix)) saved index [] v
      (2*index.length+2) (false,none) _ [] hr
    have ec : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
        ⟨some (.counter .borrow),v,store (bankBits (old::suffix)) saved index []⟩
        ⟨some .decide,v1,store (bankBits (old::suffix)) saved (List.replicate index.length true) []⟩
        (10*(1+index.length)^2) := ⟨_,hN,hNC.trans_le hc⟩
    have hd : TM2.step program
        ⟨some .decide,v1,store (bankBits (old::suffix)) saved (List.replicate index.length true) []⟩ =
        some ⟨some .patch,v1,store (bankBits (old::suffix)) saved (List.replicate index.length true) []⟩ := rfl
    have ed := one _ _ _ _ hd
    have ep := patch_execution old (bankBits suffix) saved (List.replicate index.length true) v1
    have er :=
        restore_execution (true::v1.1::bankBits suffix) saved (List.replicate index.length true) v1
    have hb : 1 ≤ B := by dsimp [B]; omega
    have hb2 : B ≤ B^2 := Nat.le_pow (by decide)
    have hdle : 1+index.length ≤ B := by dsimp [B]; omega
    have hd2 := Nat.pow_le_pow_left hdle 2
    have ecB := ec.mono (Nat.mul_le_mul_left 10 hd2)
    have edB := ed.mono (show _ ≤ B^2 by
      simp [program,getCounter,putCounter,v1,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock]
      nlinarith)
    have epB := ep.mono (show _ ≤ 10*B^2 by
      have hl : 1+(slotBits old ++ bankBits suffix).length+saved.length ≤ B := by
        dsimp [B]
        simp only [List.length_append,slotBits_length]
        omega
      nlinarith)
    have erB := er.mono (show _ ≤ 8*B^2 by
      have h1 : saved.length+1 ≤ B := by dsimp [B]; omega
      have h2 : 1+(true::v1.1::bankBits suffix).length+saved.length ≤ B := by
        dsimp [B]
        simp only [List.length_append,slotBits_length]
        omega
      have hp := Nat.mul_le_mul h1 h2
      simp only [List.length_replicate] at *
      nlinarith)
    have he := ((ecB.trans edB).trans epB).trans erB
    have ht := he.mono (show _ ≤ 100*B^2 by omega)
    simpa only [List.nil_append,List.length_nil,Nat.zero_add,Nat.mul_one,bankBits_cons,
      slotBits,List.cons_append,putIO,putCounter,v1,done,B] using ht
  | cons a front ih =>
    let tail := bankBits (front ++ old::suffix)
    let B := 1 + (slotBits a ++ tail).length + saved.length + index.length
    obtain ⟨ticks,index',_,hlen,hvalue,hr,hc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.decrement_positive index (getCounter v)
      (by rw [hi]; simp)
    let v1 := putCounter v (true,none)
    obtain ⟨hN,hNC⟩ :=
        counter_call (slotBits a ++ tail) saved index [] v ticks (true,none) index' [] hr
    have ec : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
        ⟨some (.counter .borrow),v,store (slotBits a ++ tail) saved index []⟩
        ⟨some .decide,v1,store (slotBits a ++ tail) saved index' []⟩
        (10*(1+index.length)^2) := ⟨ticks,hN,hNC.trans_le hc⟩
    have hd : TM2.step program ⟨some .decide,v1,store (slotBits a ++ tail) saved index' []⟩ =
        some ⟨some .copy,v1,store (slotBits a ++ tail) saved index' []⟩ := rfl
    have ed := one _ _ _ _ hd
    obtain ⟨w,hw,ew⟩ := copy_execution a tail saved index' v1
    have hw' : w.1 = v.1 := hw
    have hi' : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue index' = front.length := by
      rw [hi] at hvalue
      simpa using Nat.add_right_cancel hvalue
    have ei := ih ((slotBits a).reverse ++ saved) index' w hi'
    have hB : 1 + (bankBits (front ++ old::suffix)).length +
        ((slotBits a).reverse ++ saved).length + index'.length = B := by
      dsimp [B,tail]
      simp only [List.length_append,List.length_reverse,slotBits_length,hlen]
      omega
    rw [hB,hw'] at ei
    have hbank : ((slotBits a).reverse ++ saved).reverse ++ bankBits (front ++ some v.1::suffix) =
        saved.reverse ++ bankBits ((a::front) ++ some v.1::suffix) := by
      simp [List.reverse_append,List.append_assoc]
    rw [hbank] at ei
    have hb : 1 ≤ B := by dsimp [B]; omega
    have hb2 : B ≤ B^2 := Nat.le_pow (by decide)
    have hdle : 1+index.length ≤ B := by dsimp [B]; omega
    have hd2 := Nat.pow_le_pow_left hdle 2
    have ecB := ec.mono (Nat.mul_le_mul_left 10 hd2)
    have edB := ed.mono (show _ ≤ B^2 by
      simp [program,getCounter,putCounter,v1,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock]
      nlinarith)
    have ewB := ew.mono (show _ ≤ 10*B^2 by dsimp [B]; nlinarith)
    have he := ((ecB.trans edB).trans ewB).trans ei
    have ht := he.mono (show _ ≤ 100*((a::front).length+1)*B^2 by
      simp only [List.length_cons]
      nlinarith)
    simpa only [List.cons_append,bankBits_cons,B,tail] using ht

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.FeedbackWrite
