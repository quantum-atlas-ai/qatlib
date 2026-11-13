/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Writing framed register words

The parameterized `program` preserves its source register while prepending its framed word to an
output buffer. It composes copying, frame encoding, and temporary-source cleanup, with `store`
describing the registers and framing workspace.

The theorem `complete` proves correctness and a cubic execution bound in the source and existing
output lengths. For the classical computational background, see [KitaevShenVyalyi2002].

## Main statements

* `copy_call`: a register is copied in reverse order into writer workspace.
* `encode_call`: the corresponding frame is prepended to the output.
* `complete`: the writer halts with the frame written and workspace cleared.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- The framed-writer stacks together with a family of source registers. -/
abbrev Slot (K : Type) := FrameCopy.Slot ⊕ K

/-- Control labels for copying a register, framing the copy, draining workspace, and halting. -/
inductive Label where
  | copy (l : NatEmit.Label)
  | encode (l : FrameCopy.Label)
  | drain (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.copy .emit⟩

variable {K : Type} [DecidableEq K]

/-- Maps register copying to the framed-writer restoration and source stacks. -/
def copyCode (src : K) : Fin 3 → Slot K
  | 0 => .inr src | 1 => .inl .restore | _ => .inl .source
/-- Selects the framed-writer source stack for cleanup. -/
def drainCode (_ : Fin 1) : Slot K := .inl .source

/-- The program that copies a source register, prepends its framed encoding to the output
buffer, and clears its temporary source stack. -/
def program (src : K) : Label → TM2.Stmt (fun _ : Slot K => Bool) Label Symbol
  | .copy l => StackCall.stmt (copyCode src) Label.copy (.encode (.copy false .emit))
      id (fun _ v => v) (NatEmit.program l)
  | .encode l => StackCall.stmt Sum.inl Label.encode (.drain 0) id (fun _ v => v) (FrameCopy.program l)
  | .drain l => StackCall.stmt drainCode Label.drain .done id (fun _ v => v) (Normalization.drainProgram l)
  | .done => .halt

/-- Combines the source registers with a writer-source word, output buffer, and empty framing
workspace. -/
def store (R : K → Bits) (source out : Bits) : Slot K → Bits :=
  Sum.elim (FrameCopy.store source [] [] [] [] out) R

omit [DecidableEq K] in

/-- The stack map for copying a source register is injective. -/
theorem copyCode_injective (src : K) : Function.Injective (copyCode src) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [copyCode] at h ⊢

/-- Copying a source register produces its reversed contents in writer workspace while
preserving the register and output buffer, with a quadratic clock bound. -/
theorem copy_call (src : K) (R : K → Bits) (out : Bits) (v : Symbol) :
    stackRun (program src) (2*(R src).length+3) ⟨some (.copy .emit),v,store R [] out⟩ =
      some ⟨some (.encode (.copy false .emit)),none,store R (R src).reverse out⟩ ∧
    stackRunClock (program src) (2*(R src).length+3) ⟨some (.copy .emit),v,store R [] out⟩ ≤
      25*(1+(R src).length)^2 := by
  let code := copyCode src
  let S := store R [] out
  have hinj := copyCode_injective src
  have hsame : StackCall.frame code S (Parsing.triple (R src) [] [])=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i <;> rfl
  have ht : Parsing.triple (R src) [] (R src).reverse =
      Function.update (Parsing.triple (R src) [] []) (2 : Fin 3) (R src).reverse := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (Parsing.triple (R src) [] (R src).reverse)=
      store R (R src).reverse out := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    funext slot
    cases slot with
    | inl s => cases s <;> rfl
    | inr i => rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code Label.copy (.encode (.copy false .emit)) id
    (fun _ v : Symbol => v) (StackCall.frame code S)
    (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) NatEmit.program (program src) (fun _ => rfl)
    v _ _ _ (NatEmit.copy_complete (R src) [] v).1
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,List.append_nil,hfinal] at hr hc
  exact ⟨hr,hc.trans_le (by simpa only [List.length_nil,Nat.add_zero] using NatEmit.copy_clock_bound (R src) [] v)⟩

/-- Encoding a reversed source prepends its frame to the output buffer while retaining the
source and registers, with a cubic clock bound. -/
theorem encode_call (src : K) (R : K → Bits) (bits out : Bits) (v : Symbol) :
    ∃ ticks, stackRun (program src) ticks
      ⟨some (.encode (.copy false .emit)),v,store R bits.reverse out⟩ =
      some ⟨some (.drain 0),none,store R bits.reverse (framed bits++out)⟩ ∧
      stackRunClock (program src) ticks
        ⟨some (.encode (.copy false .emit)),v,store R bits.reverse out⟩ ≤
        10000*(1+bits.length+out.length)^3 := by
  obtain ⟨ticks,hr,hc⟩ := FrameCopy.complete bits out v
  obtain ⟨hN,hNC⟩ := StackCall.execution Sum.inl Label.encode (.drain 0) id (fun _ v : Symbol => v)
    (fun S => Sum.elim S R) (fun _ _ => rfl)
    (fun S k w => by simpa only [StackCall.leftFrame] using StackCall.leftFrame_update R S k w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) FrameCopy.program (program src) (fun _ => rfl)
    v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

/-- Cleanup empties the writer-source stack while preserving registers and output, with a
quadratic clock bound. -/
theorem drain_call (src : K) (R : K → Bits) (bits out : Bits) (v : Symbol) :
    stackRun (program src) (bits.length+1) ⟨some (.drain 0),v,store R bits out⟩ =
      some ⟨some .done,none,store R [] out⟩ ∧
    stackRunClock (program src) (bits.length+1) ⟨some (.drain 0),v,store R bits out⟩ ≤
      10*(1+bits.length)^2 := by
  let code : Fin 1 → Slot K := drainCode
  let S := store R bits out
  have hinj : Function.Injective code := fun a b _ => Subsingleton.elim a b
  have hsame : StackCall.frame code S (Normalization.singleStack bits)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    rfl
  have ht : Normalization.singleStack [] =
      Function.update (Normalization.singleStack bits) (0 : Fin 1) [] := by
    funext i
    fin_cases i
    rfl
  have hfinal : StackCall.frame code S (Normalization.singleStack [])=store R [] out := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    funext slot
    cases slot with
    | inl s => cases s <;> rfl
    | inr i => rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code Label.drain .done id (fun _ v : Symbol => v)
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram (program src) (fun _ => rfl)
    v _ _ _ (Normalization.drain_run bits v)
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal] at hr hc
  refine ⟨hr,?_⟩
  rw [hc,Normalization.drain_clock]
  nlinarith

/-- The writer prepends the selected register's frame to the output buffer and halts with empty
workspace and unchanged registers within a cubic execution bound. -/
theorem complete (src : K) (R : K → Bits) (out : Bits) :
    Execution (program src) ⟨some (.copy .emit),none,store R [] out⟩
      ⟨none,none,store R [] (framed (R src)++out)⟩
      (11000*(1+(R src).length+out.length)^3) := by
  have hC := copy_call src R out none
  have e0 : Execution (program src) ⟨some (.copy .emit),none,store R [] out⟩
      ⟨some (.encode (.copy false .emit)),none,store R (R src).reverse out⟩
      (25*(1+(R src).length)^2) := ⟨2*(R src).length+3,hC.1,hC.2⟩
  obtain ⟨ticks,hr,hc⟩ := encode_call src R (R src) out none
  have e1 : Execution (program src)
      ⟨some (.encode (.copy false .emit)),none,store R (R src).reverse out⟩
      ⟨some (.drain 0),none,store R (R src).reverse (framed (R src)++out)⟩
      (10000*(1+(R src).length+out.length)^3) := ⟨ticks,hr,hc⟩
  have hD := drain_call src R (R src).reverse (framed (R src)++out) none
  have e2 : Execution (program src)
      ⟨some (.drain 0),none,store R (R src).reverse (framed (R src)++out)⟩
      ⟨some .done,none,store R [] (framed (R src)++out)⟩
      (10*(1+(R src).length)^2) := by
    refine ⟨(R src).length+1,?_,?_⟩
    · simpa only [List.length_reverse] using hD.1
    · simpa only [List.length_reverse] using hD.2
  have e3 : Execution (program src) ⟨some .done,none,store R [] (framed (R src)++out)⟩
      ⟨none,none,store R [] (framed (R src)++out)⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  apply (((e0.trans e1).trans e2).trans e3).mono
  let N := 1+(R src).length+out.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hb : 1+(R src).length ≤ N := by dsimp [N]; omega
  have hp2 := Nat.pow_le_pow_left hb 2
  have h23 : N^2 ≤ N^3 := by have h := Nat.mul_le_mul_left (N^2) hN; nlinarith
  have hOne : 1 ≤ N^3 := by have h := Nat.pow_le_pow_left hN 3; simpa using h
  change 25*(1+(R src).length)^2+10000*N^3+10*(1+(R src).length)^2+1 ≤ 11000*N^3
  nlinarith

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter
