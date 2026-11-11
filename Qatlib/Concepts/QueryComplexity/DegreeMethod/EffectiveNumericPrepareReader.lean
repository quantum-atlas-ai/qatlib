/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Reading framed words into registers

The parameterized `program` reads one length-framed word and transfers its payload into an
initially empty destination register. Its store separates the external registers from parser
workspace, preserving the unread suffix and clearing temporary stacks on termination.

The theorem `complete` supplies a cubic execution bound in the framed input length. For
background on classical subroutines and machine models, see [KitaevShenVyalyi2002].

## Main statements

* `take_call`: frame extraction produces a reversed payload and preserves the input suffix.
* `move_call`: payload transfer restores its order in the destination register.
* `complete`: the composed reader halts with the payload stored and workspace empty.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- The framed-reader stacks together with a family of destination registers. -/
abbrev Slot (K : Type) := FramedTake.Slot ⊕ K
/-- The framed-reader local state paired with an input/output symbol register. -/
abbrev Local := FramedTake.Local × Symbol

/-- Control labels for taking a frame, moving its payload, and halting. -/
inductive Label where
  | take (l : FramedTake.Label)
  | move (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.take (.read (.read .unary))⟩

/-- Replaces the framed-reader local component while preserving the symbol register. -/
def putTake (v : Local) (w : FramedTake.Local) : Local := (w,v.2)
/-- Replaces the symbol register while preserving the framed-reader local component. -/
def putIO (v : Local) (w : Symbol) : Local := (v.1,w)

variable {K : Type} [DecidableEq K]

/-- Maps payload transfer from the reader-output stack to the selected destination register. -/
def moveCode (dst : K) : Fin 2 → Slot K | 0 => .inl .output | _ => .inr dst

/-- The program that reads one framed word and transfers its payload to a destination register. -/
def program (dst : K) : Label → TM2.Stmt (fun _ : Slot K => Bool) Label Local
  | .take l => StackCall.stmt Sum.inl Label.take (.move 0) Prod.fst putTake (FramedTake.program l)
  | .move l => StackCall.stmt (moveCode dst) Label.move .done Prod.snd putIO (transferProgram l)
  | .done => .load (fun _ => default) .halt

/-- Combines a reader word and output word with the external registers and empty reader
workspace. -/
def store (R : K → Bits) (reader out : Bits) : Slot K → Bits :=
  Sum.elim (FramedTake.store reader [] [] out) R

/-- Reading a frame places its reversed payload on the output stack and preserves the unread
suffix and registers, with the stated clock bound. -/
theorem take_call (dst : K) (R : K → Bits) (bits tail : Bits) (v : Local) :
    ∃ ticks last, stackRun (program dst) ticks
      ⟨some (.take (.read (.read .unary))),v,store R (framed bits++tail) []⟩ =
      some ⟨some (.move 0),putTake v last,store R tail bits.reverse⟩ ∧
      stackRunClock (program dst) ticks
        ⟨some (.take (.read (.read .unary))),v,store R (framed bits++tail) []⟩ ≤
        5000*(bits.length+1)*(1+(framed bits++tail).length)^2 := by
  obtain ⟨ticks,last,hr,hc⟩ := FramedTake.complete bits tail [] v.1
  obtain ⟨hN,hNC⟩ := StackCall.execution Sum.inl Label.take (.move 0) Prod.fst putTake
    (fun S => Sum.elim S R) (fun _ _ => rfl)
    (fun S k w => by simpa only [StackCall.leftFrame] using StackCall.leftFrame_update R S k w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) FramedTake.program (program dst) (fun _ => rfl)
    v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    List.append_nil] at hN hNC hc
  exact ⟨ticks,last,hN,hNC.trans_le (by simpa only [List.length_nil,Nat.add_zero] using hc)⟩

omit [DecidableEq K] in

/-- The stack map for payload transfer is injective. -/
theorem moveCode_injective (dst : K) : Function.Injective (moveCode dst) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [moveCode] at h ⊢

/-- Moving a reversed payload into an empty destination register restores its original order and
clears the output stack with a quadratic clock bound. -/
theorem move_call (dst : K) (R : K → Bits) (bits reader : Bits) (v : Local) (hfresh : R dst=[]) :
    stackRun (program dst) (bits.length+1) ⟨some (.move 0),v,store R reader bits.reverse⟩ =
      some ⟨some .done,putIO v none,store (Function.update R dst bits) reader []⟩ ∧
    stackRunClock (program dst) (bits.length+1) ⟨some (.move 0),v,store R reader bits.reverse⟩ ≤
      10*(bits.length+1)^2 := by
  let code := moveCode dst
  let S := store R reader bits.reverse
  have hinj := moveCode_injective dst
  have hsame : StackCall.frame code S (stackPair bits.reverse [])=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    · rfl
    · exact hfresh
  have ht : stackPair [] bits =
      Function.update (Function.update (stackPair bits.reverse []) (0 : Fin 2) []) 1 bits := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (stackPair [] bits)=store (Function.update R dst bits) reader [] := by
    rw [ht,StackCall.frame_update _ _ _ hinj,StackCall.frame_update _ _ _ hinj,hsame]
    funext slot
    cases slot with
    | inl s => cases s <;> rfl
    | inr i =>
      simp only [moveCode,S,store,Function.update_apply,Sum.elim_inr,
        Sum.inr.injEq,Sum.inr_ne_inl,↓reduceIte]
  obtain ⟨hr,hc⟩ := StackCall.execution code Label.move .done Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram (program dst) (fun _ => rfl)
    v _ _ _ (transfer_run bits.reverse [] v.2)
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,List.append_nil,List.reverse_reverse,List.length_reverse,putIO,Prod.mk.eta] at hr hc
  rw [hfinal] at hr
  refine ⟨hr,?_⟩
  have hc0 := transfer_clock bits.reverse [] v.2
  simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hc0
  rw [hc,hc0]
  nlinarith

/-- The reader stores one framed payload in an empty destination register, preserves the
remaining input, and halts with empty reader workspace within a cubic execution bound. -/
theorem complete (dst : K) (R : K → Bits) (bits tail : Bits) (hfresh : R dst=[]) :
    Execution (program dst)
      ⟨some (.take (.read (.read .unary))),default,store R (framed bits++tail) []⟩
      ⟨none,default,store (Function.update R dst bits) tail []⟩
      (10000*(1+(framed bits++tail).length)^3) := by
  obtain ⟨ticks,last,hr,hc⟩ := take_call dst R bits tail default
  have e0 : Execution (program dst)
      ⟨some (.take (.read (.read .unary))),default,store R (framed bits++tail) []⟩
      ⟨some (.move 0),putTake default last,store R tail bits.reverse⟩
      (5000*(bits.length+1)*(1+(framed bits++tail).length)^2) := ⟨ticks,hr,hc⟩
  have hM := move_call dst R bits tail (putTake default last) hfresh
  have e1 : Execution (program dst) ⟨some (.move 0),putTake default last,store R tail bits.reverse⟩
      ⟨some .done,putIO (putTake default last) none,store (Function.update R dst bits) tail []⟩
      (10*(bits.length+1)^2) := ⟨bits.length+1,hM.1,hM.2⟩
  have e2 : Execution (program dst)
      ⟨some .done,putIO (putTake default last) none,store (Function.update R dst bits) tail []⟩
      ⟨none,default,store (Function.update R dst bits) tail []⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  apply ((e0.trans e1).trans e2).mono
  let N := 1+(framed bits++tail).length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hb : bits.length+1 ≤ N := by
    dsimp [N,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed]
    simp only [List.length_append]
    omega
  have hm := Nat.mul_le_mul_right (N^2) hb
  have hp2 := Nat.pow_le_pow_left hb 2
  have h23 : N^2 ≤ N^3 := by have h := Nat.mul_le_mul_left (N^2) hN; nlinarith
  have hOne : 1 ≤ N^3 := by have h := Nat.pow_le_pow_left hN 3; simpa using h
  change 5000*(bits.length+1)*N^2+10*(bits.length+1)^2+1 ≤ 10000*N^3
  nlinarith

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader
