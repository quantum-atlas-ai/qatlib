/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareAppendWriter
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

abbrev Slot (K : Type) :=
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot K ⊕ Fin 1

inductive Label where
  | write (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Label)
  | append (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.write (.copy .emit)⟩

variable {K : Type} [DecidableEq K]

def appendCode : Fin 2 → Slot K
  | 0 => .inl (.inl .output)
  | _ => .inr 0

def program (src : K) : Label → TM2.Stmt (fun _ : Slot K => Bool) Label Symbol
  | .write l => StackCall.stmt Sum.inl Label.write (.append 0) id (fun _ v => v)
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.program src l)
  | .append l => StackCall.stmt appendCode Label.append .done id (fun _ v => v)
      (transferProgram l)
  | .done => .halt

def store (R : K → Bits) (buffer out : Bits) : Slot K → Bits :=
  Sum.elim (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.store R [] buffer) (fun _ => out)

theorem write_call (src : K) (R : K → Bits) (out : Bits) :
    Execution (program src)
      ⟨some (.write (.copy .emit)),none,store R [] out⟩
      ⟨some (.append 0),none,store R (framed (R src)) out⟩
      (11000*(1+(R src).length)^3) := by
  obtain ⟨ticks,hr,hc⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.complete src R []
  obtain ⟨hN,hNC⟩ := StackCall.execution Sum.inl Label.write (.append 0) id
    (fun _ v : Symbol => v) (fun S => Sum.elim S (fun _ : Fin 1 => out))
    (fun _ _ => rfl)
    (fun S k w => by simpa only [StackCall.leftFrame] using
      StackCall.leftFrame_update (fun _ : Fin 1 => out) S k w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.program src)
    (program src) (fun _ => rfl) none ticks _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
    Option.getD_none,List.append_nil] at hN hNC
  refine ⟨ticks,hN,?_⟩
  exact hNC.trans_le (by simpa only [List.length_nil,Nat.add_zero] using hc)

omit [DecidableEq K] in

theorem appendCode_injective : Function.Injective (appendCode (K:=K)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [appendCode] at h ⊢

theorem append_call (src : K) (R : K → Bits) (buffer out : Bits) (v : Symbol) :
    Execution (program src) ⟨some (.append 0),v,store R buffer out⟩
      ⟨some .done,none,store R [] (buffer.reverse++out)⟩
      (10*(1+buffer.length+out.length)^2) := by
  let code := appendCode (K:=K)
  let S := store R buffer out
  have hinj := appendCode_injective (K:=K)
  have hsame : StackCall.frame code S (stackPair buffer out)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i <;> rfl
  have ht : stackPair [] (buffer.reverse++out)=
      Function.update (Function.update (stackPair buffer out) (0 : Fin 2) []) 1
        (buffer.reverse++out) := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (stackPair [] (buffer.reverse++out))=
      store R [] (buffer.reverse++out) := by
    rw [ht,StackCall.frame_update _ _ _ hinj,StackCall.frame_update _ _ _ hinj,hsame]
    funext slot
    cases slot with
    | inl w =>
      cases w with
      | inl j => cases j <;> rfl
      | inr j => rfl
    | inr j => fin_cases j; rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code Label.append .done id (fun _ v : Symbol => v)
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram (program src) (fun _ => rfl)
    v _ _ _ (transfer_run buffer out v)
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
    Option.getD_none,hsame,hfinal] at hr hc
  refine ⟨buffer.length+1,hr,?_⟩
  rw [hc,transfer_clock]
  nlinarith

theorem complete (src : K) (R : K → Bits) (out : Bits) :
    Execution (program src)
      ⟨some (.write (.copy .emit)),none,store R [] out.reverse⟩
      ⟨none,none,store R [] (out++framed (R src)).reverse⟩
      (12000*(1+(R src).length+out.length)^3) := by
  have e0 := write_call src R out.reverse
  have e1 := append_call src R (framed (R src)) out.reverse none
  have e2 : Execution (program src)
      ⟨some .done,none,store R [] ((framed (R src)).reverse++out.reverse)⟩
      ⟨none,none,store R [] ((framed (R src)).reverse++out.reverse)⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  have hall := (e0.trans e1).trans e2
  rw [← List.reverse_append] at hall
  apply hall.mono
  simp only [List.length_reverse]
  let N := 1+(R src).length+out.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hb : 1+(R src).length ≤ N := by dsimp [N]; omega
  have hf : (framed (R src)).length ≤ 3*(R src).length+3 := by
    simp only [framed,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits,List.length_append,
      List.length_replicate,List.length_cons,List.length_nil]
    have h := Counter.bits_length_le (R src).length
    omega
  have ht : 1+(framed (R src)).length+out.length ≤ 4*N := by dsimp [N]; omega
  have hb3 := Nat.pow_le_pow_left hb 3
  have ht2 := Nat.pow_le_pow_left ht 2
  have h23 : N^2 ≤ N^3 := by have h := Nat.mul_le_mul_left (N^2) hN; nlinarith only [h]
  have hOne : 1 ≤ N^3 := by have h := Nat.pow_le_pow_left hN 3; simpa using h
  change 11000*(1+(R src).length)^3+
    10*(1+(framed (R src)).length+out.length)^2+1 ≤ 12000*N^3
  nlinarith only [hb3,ht2,h23,hOne]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareAppendWriter
