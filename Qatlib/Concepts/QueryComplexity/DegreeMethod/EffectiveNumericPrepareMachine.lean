/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader
import Mathlib.Data.Nat.Size

/-!
# Encoded preparation-loop machine

The `program` parses an encoded counter and five framed data words, invokes the bounded
preparation loop, and serializes its result. Its input and output formats are specified by
`input` and `output`, while parsing and serialization clear their temporary stacks.

The theorem `uniform_raw_loop_machine` compiles this computation to one finite-state Turing
machine with quartic time and space bounds in the iteration count and encoded input length.
Classical computation provides the model background in [KitaevShenVyalyi2002].

## Main statements

* `frontend`: parsing reconstructs the counter and data with a cubic execution bound.
* `serializer`: the result is framed and all other stacks are cleared.
* `complete`: the complete stack program has a quartic execution bound.
* `uniform_raw_loop_machine`: one Turing machine handles every encoded loop instance.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator
open Qatlib.Foundations.IntervalArith.IntervalOps

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue natBits framed Runs)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- Additional stacks for reading input, storing output, and carrying out parsing and
serialization. -/
inductive Extra where
  | input | buffer | work0 | work1 | work2 | work3 | work4 | work5 | work6 | work7 | output | spare
  deriving DecidableEq,Fintype
/-- The preparation-loop stacks together with the additional input, output, and workspace
stacks. -/
abbrev Slot := Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot ⊕ Extra
/-- The loop-local state, framed-reader state, and input/output symbol register. -/
abbrev Local :=
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Local × FramedTake.Local × Symbol

/-- Control labels for parsing, loop execution, serialization, cleanup, and termination. -/
inductive Label where
  | init (l : Fin 1)
  | nat (l : Fin 3)
  | field (index : Fin 5) (l : FramedTake.Label)
  | transfer (index : Option (Fin 5)) (l : Fin 1)
  | launch
  | loop (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Label)
  | reverseA (l : Fin 1)
  | encode (l : FrameCopy.Label)
  | drain (index : Fin 5) (l : Fin 1)
  | reverseOutput (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.init 0⟩

/-- Extracts the preparation-loop component of the local state. -/
def getLoop (v : Local) := v.1
/-- Replaces the preparation-loop component of the local state. -/
def putLoop (v : Local)
    (w : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Local) : Local :=
    (w,v.2)
/-- Extracts the framed-reader component of the local state. -/
def getTake (v : Local) := v.2.1
/-- Replaces the framed-reader component of the local state. -/
def putTake (v : Local) (w : FramedTake.Local) : Local := (v.1,w,v.2.2)
/-- Extracts the input/output symbol register. -/
def getIO (v : Local) := v.2.2
/-- Replaces the input/output symbol register. -/
def putIO (v : Local) (w : Symbol) : Local := (v.1,v.2.1,w)

/-- Maps the transfer subroutine stacks to the spare input stack and the reader stack. -/
def initCode : Fin 2 → Slot | 0 => .inr .spare | _ => .inr .input

/-- Maps the natural-number parser stacks to the input and designated workspace stacks. -/
def natCode : Fin 3 → Slot | 0 => .inr .input | 1 => .inr .work0 | _ => .inr .work5

/-- Maps the framed-field reader stacks to the input and designated workspace stacks. -/
def fieldCode : FramedTake.Slot → Slot
  | .reader => .inr .input | .markers => .inr .work0 | .payload => .inr .work1
  | .count => .inr .work2 | .temporary => .inr .work3 | .header => .inr .work4
  | .output => .inr .work5

/-- Maps a transfer subroutine to the workspace source and either the counter or a selected
data-field destination. -/
def transferCode (index : Option (Fin 5)) : Fin 2 → Slot
  | 0 => .inr .work5
  | _ => match index with
      | none => .inl (.inr 0)
      | some i => .inl (.inl (Fin.castLE (by decide) i))

/-- Selects the next field-reader entry label, or launches the loop after the fifth field. -/
def nextField (i : Fin 5) : Label :=
  if h : i.val+1<5 then .field ⟨i.val+1,h⟩ (.read (.read .unary)) else .launch

/-- Maps the result-word reversal subroutine to the result stack and its workspace destination. -/
def reverseACode : Fin 2 → Slot | 0 => .inl (.inl 4) | _ => .inr .work5

/-- Maps the framed-copy subroutine stacks to the serialization workspace and output buffer. -/
def encodeCode : FrameCopy.Slot → Slot
  | .source => .inr .work5 | .restore => .inr .work0 | .copy => .inr .work1
  | .count => .inr .work2 | .temporary => .inr .work3 | .markers => .inr .work4
  | .header => .inr .work6 | .output => .inr .buffer

/-- Selects one of the four arithmetic input stacks or the result workspace stack for cleanup. -/
def drainCode (i : Fin 5) (_ : Fin 1) : Slot :=
  if i.val<4 then .inl (.inl (Fin.castLE (by decide) i)) else .inr .work5

/-- Selects the next cleanup label, or the output-reversal label after the last cleanup. -/
def nextDrain (i : Fin 5) : Label :=
  if h : i.val+1<5 then .drain ⟨i.val+1,h⟩ 0 else .reverseOutput 0

/-- Maps the final transfer subroutine to the output buffer and output stack. -/
def outputCode : Fin 2 → Slot | 0 => .inr .buffer | _ => .inr .output

/-- The stack-machine program that parses a counter and five data fields, executes the
preparation loop, and serializes the result. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .init l => StackCall.stmt initCode Label.init (.nat 0) getIO putIO (transferProgram l)
  | .nat l => StackCall.stmt natCode Label.nat (.transfer none 0) getIO putIO (Parsing.natProgram l)
  | .field i l => StackCall.stmt fieldCode (Label.field i) (.transfer (some i) 0)
      getTake putTake (FramedTake.program l)
  | .transfer i l => StackCall.stmt (transferCode i) (Label.transfer i)
      (match i with | none => .field 0 (.read (.read .unary)) | some j => nextField j)
      getIO putIO (transferProgram l)
  | .launch => .load (fun v => putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)))
      (.goto (fun _ => .loop (.counter .borrow)))
  | .loop l => StackCall.stmt Sum.inl Label.loop (.reverseA 0) getLoop putLoop (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.program l)
  | .reverseA l => StackCall.stmt reverseACode Label.reverseA (.encode (.copy false .emit))
      getIO putIO (transferProgram l)
  | .encode l => StackCall.stmt encodeCode Label.encode (.drain 0 0) getIO putIO (FrameCopy.program l)
  | .drain i l => StackCall.stmt (drainCode i) (Label.drain i) (nextDrain i)
      getIO putIO (Normalization.drainProgram l)
  | .reverseOutput l => StackCall.stmt outputCode Label.reverseOutput .done getIO putIO (transferProgram l)
  | .done => .load (fun _ => default) .halt

/-- Concatenates the framed encodings of the five preparation data words. -/
def fields (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : Bits :=
  framed d.sq4 ++ (framed d.lin2 ++ (framed d.q ++ (framed d.rhs ++ framed d.a)))

/-- Encodes the iteration counter followed by the five framed preparation data words. -/
def input (k : ℕ)
    (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : Bits :=
    natBits k ++ fields d

/-- The framed result word after `k` preparation-loop updates. -/
def output (k : ℕ)
    (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : Bits :=
    framed (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d).a)

/-- Combines parsed loop data with an unread input suffix and empty auxiliary stacks. -/
def parsedStore (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (reader : Bits) : Slot → Bits :=
  Sum.elim (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store counter [] d) (fun e => if e=Extra.input then reader else [])

/-- The stack map for the natural-number parser is injective. -/
theorem natCode_injective : Function.Injective natCode := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [natCode] at h ⊢

/-- The stack map for the framed-field reader is injective. -/
theorem fieldCode_injective : Function.Injective fieldCode := by
  intro a b h
  cases a <;> cases b <;> simp [fieldCode] at h ⊢

/-- Returning from the natural-number parser updates the input suffix and parser-output
workspace in the parsed store. -/
theorem nat_frame_final (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (before after out : Bits) :
    StackCall.frame natCode (parsedStore counter d before) (Parsing.triple after [] out) =
      Function.update (parsedStore counter d after) (.inr .work5) out := by
  funext slot
  cases slot with
  | inl k =>
    rw [WordValidator.frame_outside natCode _ _ _ (by intro j; fin_cases j <;> simp [natCode])]
    rfl
  | inr e =>
    cases e
    all_goals first
    | exact StackCall.frame_at natCode _ _ natCode_injective 0
    | exact StackCall.frame_at natCode _ _ natCode_injective 1
    | exact StackCall.frame_at natCode _ _ natCode_injective 2
    | (rw [WordValidator.frame_outside natCode _ _ _ (by intro j; fin_cases j <;> simp [natCode])]; rfl)

/-- The embedded natural-number parser reads the counter encoding into reversed binary form with
the stated step count and quadratic clock bound. -/
theorem nat_call (k : ℕ) (tail counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    stackRun program (2*k.bits.length+3)
        ⟨some (.nat 0),v,parsedStore counter d (natBits k++tail)⟩ =
      some ⟨some (.transfer none 0),putIO v none,
        Function.update (parsedStore counter d tail) (.inr .work5) k.bits.reverse⟩ ∧
    stackRunClock program (2*k.bits.length+3)
        ⟨some (.nat 0),v,parsedStore counter d (natBits k++tail)⟩ ≤
      40*(1+(natBits k++tail).length)^2 := by
  let S := parsedStore counter d (natBits k++tail)
  have hsame : StackCall.frame natCode S (Parsing.triple (natBits k++tail) [] [])=S := by
    apply StackCall.frame_same _ _ _ natCode_injective
    intro j
    fin_cases j <;> rfl
  have hfinal := nat_frame_final counter d (natBits k++tail) tail k.bits.reverse
  have hr := (Parsing.nat_execution k tail [] (getIO v)).1
  have hc := Parsing.nat_clock_bound k tail [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution natCode Label.nat (.transfer none 0) getIO putIO
    (StackCall.frame natCode S) (fun data j => StackCall.frame_at _ _ data natCode_injective j)
    (fun data j bits => StackCall.frame_update _ _ data natCode_injective j bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Parsing.natProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil] at hN hNC
  dsimp only [S] at hN hNC
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  exact hNC.trans_le (by simpa only [List.length_nil,Nat.add_zero] using! hc)

/-- Returning from the framed-field reader updates the input suffix and field-output workspace
in the parsed store. -/
theorem field_frame_final (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (before after out : Bits) :
    StackCall.frame fieldCode (parsedStore counter d before) (FramedTake.store after [] [] out) =
      Function.update (parsedStore counter d after) (.inr .work5) out := by
  funext slot
  cases slot with
  | inl k =>
    rw [WordValidator.frame_outside fieldCode _ _ _ (by intro j; cases j <;> simp [fieldCode])]
    rfl
  | inr e =>
    cases e
    all_goals first
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.reader
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.markers
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.payload
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.count
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.temporary
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.header
    | exact StackCall.frame_at fieldCode _ _ fieldCode_injective FramedTake.Slot.output
    | (rw [WordValidator.frame_outside fieldCode _ _ _ (by intro j; cases j <;> simp [fieldCode])]; rfl)

/-- The embedded field reader extracts a framed word in reverse order and preserves the unread
suffix, with the stated clock bound. -/
theorem field_call (i : Fin 5) (bits tail counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    ∃ ticks last, stackRun program ticks
        ⟨some (.field i (.read (.read .unary))),v,parsedStore counter d (framed bits++tail)⟩ =
      some ⟨some (.transfer (some i) 0),putTake v last,
        Function.update (parsedStore counter d tail) (.inr .work5) bits.reverse⟩ ∧
    stackRunClock program ticks
        ⟨some (.field i (.read (.read .unary))),v,parsedStore counter d (framed bits++tail)⟩ ≤
      5000*(bits.length+1)*(1+(framed bits++tail).length)^2 := by
  let S := parsedStore counter d (framed bits++tail)
  have hsame : StackCall.frame fieldCode S (FramedTake.store (framed bits++tail) [] [] [])=S := by
    apply StackCall.frame_same _ _ _ fieldCode_injective
    intro j
    cases j <;> rfl
  have hfinal := field_frame_final counter d (framed bits++tail) tail bits.reverse
  obtain ⟨ticks,last,hr,hc⟩ := FramedTake.complete bits tail [] (getTake v)
  obtain ⟨hN,hNC⟩ := StackCall.execution fieldCode (Label.field i) (.transfer (some i) 0) getTake putTake
    (StackCall.frame fieldCode S) (fun data j => StackCall.frame_at _ _ data fieldCode_injective j)
    (fun data j bs => StackCall.frame_update _ _ data fieldCode_injective j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) FramedTake.program program (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getTake,putTake,hsame,List.append_nil] at hN hNC
  dsimp only [S] at hN hNC
  rw [hfinal] at hN
  refine ⟨ticks,last,hN,?_⟩
  exact hNC.trans_le (by simpa only [List.length_nil,Nat.add_zero] using! hc)

/-- Framing a two-stack store through an injective stack map equals updating the two selected
caller stacks. -/
theorem pair_frame {J : Type} [DecidableEq J] (code : Fin 2 → J)
    (hinj : Function.Injective code) (S : J → Bits) (a b : Bits) :
    StackCall.frame code S (stackPair a b) =
      Function.update (Function.update S (code 0) a) (code 1) b := by
  have h01 : code 0≠code 1 := by
    intro h
    have h' := hinj h
    norm_num at h'
  funext j
  by_cases h0 : j=code 0
  · subst j
    simpa only [stackPair_zero,Function.update_of_ne h01,Function.update_self] using!
      StackCall.frame_at code S (stackPair a b) hinj 0
  by_cases h1 : j=code 1
  · subst j
    simpa only [stackPair_one,Function.update_self] using!
      StackCall.frame_at code S (stackPair a b) hinj 1
  rw [WordValidator.frame_outside code S _ j (by
    intro i
    fin_cases i
    · exact Ne.symm h0
    · exact Ne.symm h1)]
  rw [Function.update_of_ne h1,Function.update_of_ne h0]

/-- The stack map for each counter or field transfer is injective. -/
theorem transferCode_injective (index : Option (Fin 5)) : Function.Injective (transferCode index) := by
  intro a b h
  cases index <;> fin_cases a <;> fin_cases b <;> simp [transferCode] at h ⊢

/-- Clearing the parser-output workspace restores the parsed store. -/
theorem scratch_clear (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (reader bits : Bits) :
    Function.update (Function.update (parsedStore counter d reader) (.inr .work5) bits)
      (.inr .work5) [] = parsedStore counter d reader := by
  funext slot
  by_cases h : slot=(.inr .work5 : Slot)
  · subst slot
    rfl
  · simp only [Function.update_of_ne h]

/-- Updating the counter stack replaces the counter word in the parsed store. -/
theorem parsedStore_update_counter (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (reader bits : Bits) :
    Function.update (parsedStore counter d reader) (.inl (.inr 0)) bits = parsedStore bits d reader := by
  change Function.update (StackCall.leftFrame (fun e : Extra => if e=Extra.input then reader else [])
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store counter [] d)) (.inl (.inr 0)) bits = _
  rw [← StackCall.leftFrame_update,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store_update_counter]
  rfl

/-- The counter-transfer phase restores the parsed binary counter and enters the first field
reader with a quadratic clock bound. -/
theorem nat_transfer_call (k : ℕ) (reader : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    stackRun program (k.bits.length+1)
        ⟨some (.transfer none 0),v,
          Function.update (parsedStore [] d reader) (.inr .work5) k.bits.reverse⟩ =
      some ⟨some (.field 0 (.read (.read .unary))),putIO v none,parsedStore k.bits d reader⟩ ∧
    stackRunClock program (k.bits.length+1)
        ⟨some (.transfer none 0),v,
          Function.update (parsedStore [] d reader) (.inr .work5) k.bits.reverse⟩ ≤
      10*(k.bits.length+1)^2 := by
  let S := Function.update (parsedStore [] d reader) (.inr .work5) k.bits.reverse
  have hsame : StackCall.frame (transferCode none) S (stackPair k.bits.reverse [])=S := by
    apply StackCall.frame_same _ _ _ (transferCode_injective none)
    intro j
    fin_cases j <;> rfl
  have hfinal : StackCall.frame (transferCode none) S (stackPair [] k.bits)=parsedStore k.bits d reader := by
    rw [pair_frame _ (transferCode_injective none)]
    change Function.update (Function.update
      (Function.update (parsedStore [] d reader) (.inr .work5) k.bits.reverse)
        (.inr .work5) []) (.inl (.inr 0)) k.bits = _
    rw [scratch_clear,parsedStore_update_counter]
  have hr := transfer_run k.bits.reverse [] (getIO v)
  have hc := transfer_clock k.bits.reverse [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution (transferCode none) (Label.transfer none)
    (.field 0 (.read (.read .unary))) getIO putIO (StackCall.frame (transferCode none) S)
    (fun data j => StackCall.frame_at _ _ data (transferCode_injective none) j)
    (fun data j bs => StackCall.frame_update _ _ data (transferCode_injective none) j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil,List.reverse_reverse,List.length_reverse] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  rw [hNC,hc]
  simp only [List.length_nil,Nat.add_zero]
  nlinarith

/-- Selects one of the five preparation data words by its field index. -/
def getField (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : Fin 5 → Bits
  | 0 => d.sq4 | 1 => d.lin2 | 2 => d.q | 3 => d.rhs | _ => d.a

/-- Replaces the selected preparation data word. -/
def setField (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (i : Fin 5) (bits : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
  match i with
  | 0 => { d with sq4 := bits } | 1 => { d with lin2 := bits }
  | 2 => { d with q := bits } | 3 => { d with rhs := bits } | _ => { d with a := bits }

/-- Updating a selected arithmetic data stack agrees with replacing the corresponding data
field. -/
theorem dataStore_setField (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (i : Fin 5) (bits : Bits) :
    Function.update (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.dataStore d) (Fin.castLE (by decide) i) bits =
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.dataStore (setField d i bits) := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

/-- Reading a selected field stack from the parsed store returns the corresponding data word. -/
theorem parsedStore_field (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (reader : Bits) (i : Fin 5) :
    parsedStore counter d reader (.inl (.inl (Fin.castLE (by decide) i))) = getField d i := by
  fin_cases i <;> rfl

/-- Updating a selected field stack agrees with replacing that field in the parsed store. -/
theorem parsedStore_setField (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (reader : Bits)
    (i : Fin 5) (bits : Bits) :
    Function.update (parsedStore counter d reader) (.inl (.inl (Fin.castLE (by decide) i))) bits =
      parsedStore counter (setField d i bits) reader := by
  funext slot
  cases slot with
  | inl k =>
    cases k with
    | inl j => fin_cases i <;> fin_cases j <;> rfl
    | inr j => rfl
  | inr e => rfl

/-- Transferring a reversed field into an empty destination restores its original order and
advances to the next phase with a quadratic clock bound. -/
theorem field_transfer_call (i : Fin 5) (bits reader counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data)
    (v : Local) (hfresh : getField d i=[]) :
    stackRun program (bits.length+1)
        ⟨some (.transfer (some i) 0),v,
          Function.update (parsedStore counter d reader) (.inr .work5) bits.reverse⟩ =
      some ⟨some (nextField i),putIO v none,parsedStore counter (setField d i bits) reader⟩ ∧
    stackRunClock program (bits.length+1)
        ⟨some (.transfer (some i) 0),v,
          Function.update (parsedStore counter d reader) (.inr .work5) bits.reverse⟩ ≤
      10*(bits.length+1)^2 := by
  let S := Function.update (parsedStore counter d reader) (.inr .work5) bits.reverse
  have hsame : StackCall.frame (transferCode (some i)) S (stackPair bits.reverse [])=S := by
    apply StackCall.frame_same _ _ _ (transferCode_injective (some i))
    intro j
    fin_cases j
    · rfl
    · change parsedStore counter d reader (.inl (.inl (Fin.castLE (by decide) i))) = []
      rw [parsedStore_field,hfresh]
  have hfinal : StackCall.frame (transferCode (some i)) S (stackPair [] bits)=
      parsedStore counter (setField d i bits) reader := by
    rw [pair_frame _ (transferCode_injective (some i))]
    change Function.update (Function.update
      (Function.update (parsedStore counter d reader) (.inr .work5) bits.reverse)
        (.inr .work5) []) (.inl (.inl (Fin.castLE (by decide) i))) bits = _
    rw [scratch_clear,parsedStore_setField]
  have hr := transfer_run bits.reverse [] (getIO v)
  have hc := transfer_clock bits.reverse [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution (transferCode (some i)) (Label.transfer (some i))
    (nextField i) getIO putIO (StackCall.frame (transferCode (some i)) S)
    (fun data j => StackCall.frame_at _ _ data (transferCode_injective (some i)) j)
    (fun data j bs => StackCall.frame_update _ _ data (transferCode_injective (some i)) j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil,List.reverse_reverse,List.length_reverse] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  rw [hNC,hc]
  simp only [List.length_nil,Nat.add_zero]
  nlinarith

/-- Reading and transferring a framed word into an empty data field has the stated cubic
execution bound. -/
theorem read_field (i : Fin 5) (bits tail counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local)
    (hfresh : getField d i=[]) :
    ∃ w, Execution program
      ⟨some (.field i (.read (.read .unary))),v,parsedStore counter d (framed bits++tail)⟩
      ⟨some (nextField i),w,parsedStore counter (setField d i bits) tail⟩
      (6000*(1+(framed bits++tail).length)^3) := by
  obtain ⟨ticks,last,hF,hFC⟩ := field_call i bits tail counter d v
  have hT := field_transfer_call i bits tail counter d (putTake v last) hfresh
  refine ⟨putIO (putTake v last) none,ticks+(bits.length+1),?_,?_⟩
  · rw [run_add,hF,Option.bind_some,hT.1]
  · rw [clock_add _ _ _ _ _ hF]
    let N := 1+(framed bits++tail).length
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hm : bits.length+1 ≤ N := by
      dsimp [N,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed]
      simp only [List.length_append]
      omega
    have hp3 : N^2 ≤ N^3 := by
      have ht := Nat.mul_le_mul_left (N^2) hN
      nlinarith
    have hp2 := (Nat.pow_le_pow_left hm 2).trans hp3
    have hfc : 5000*(bits.length+1)*N^2 ≤ 5000*N^3 := by
      have ht := Nat.mul_le_mul_right (N^2) (Nat.mul_le_mul_left 5000 hm)
      nlinarith
    have h1 := hFC.trans hfc
    have h2 := hT.2.trans (Nat.mul_le_mul_left 10 hp2)
    change _ ≤ 6000*N^3
    nlinarith

/-- Preparation data with all five words empty. -/
def emptyData : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
    ⟨[],[],[],[],[]⟩

/-- Reading all five framed fields reconstructs the data and enters the launch phase with a
cubic execution bound. -/
theorem fields_call (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    ∃ w, Execution program
      ⟨some (.field 0 (.read (.read .unary))),v,parsedStore counter emptyData (fields d)⟩
      ⟨some .launch,w,parsedStore counter d []⟩
      (30000*(1+(fields d).length)^3) := by
  let d1 : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
      ⟨d.sq4,[],[],[],[]⟩
  let d2 : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
      ⟨d.sq4,d.lin2,[],[],[]⟩
  let d3 : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
      ⟨d.sq4,d.lin2,d.q,[],[]⟩
  let d4 : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
      ⟨d.sq4,d.lin2,d.q,d.rhs,[]⟩
  let t1 := framed d.lin2 ++ (framed d.q ++ (framed d.rhs ++ framed d.a))
  let t2 := framed d.q ++ (framed d.rhs ++ framed d.a)
  let t3 := framed d.rhs ++ framed d.a
  let t4 := framed d.a
  obtain ⟨v1,h1⟩ := read_field 0 d.sq4 t1 counter emptyData v rfl
  obtain ⟨v2,h2⟩ := read_field 1 d.lin2 t2 counter d1 v1 rfl
  obtain ⟨v3,h3⟩ := read_field 2 d.q t3 counter d2 v2 rfl
  obtain ⟨v4,h4⟩ := read_field 3 d.rhs t4 counter d3 v3 rfl
  obtain ⟨v5,h5⟩ := read_field 4 d.a [] counter d4 v4 rfl
  let B := 6000*(1+(fields d).length)^3
  have hb1 : 6000*(1+(framed d.sq4++t1).length)^3 ≤ B := by rfl
  have hb2 : 6000*(1+(framed d.lin2++t2).length)^3 ≤ B := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [fields,t2]
    simp only [List.length_append]
    omega
  have hb3 : 6000*(1+(framed d.q++t3).length)^3 ≤ B := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [fields,t3]
    simp only [List.length_append]
    omega
  have hb4 : 6000*(1+(framed d.rhs++t4).length)^3 ≤ B := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [fields,t4]
    simp only [List.length_append]
    omega
  have hb5 : 6000*(1+(framed d.a++[]).length)^3 ≤ B := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [fields]
    simp only [List.length_append,List.length_nil]
    omega
  simp only [List.append_nil] at h5 hb5
  have hall :=
      ((((h1.mono hb1).trans (h2.mono hb2)).trans (h3.mono hb3)).trans (h4.mono hb4)).trans
      (h5.mono hb5)
  refine ⟨v5,?_⟩
  exact hall.mono (by dsimp [B]; omega)

/-- The stack map for initial input transfer is injective. -/
theorem initCode_injective : Function.Injective initCode := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [initCode] at h ⊢

/-- Initial transfer reverses the spare-stack input into the reader stack and enters counter
parsing with a quadratic clock bound. -/
theorem init_call (raw : Bits) (v : Local) :
    stackRun program (raw.length+1)
        ⟨some (.init 0),v,Function.update (fun _ : Slot => []) (.inr .spare) raw.reverse⟩ =
      some ⟨some (.nat 0),putIO v none,parsedStore [] emptyData raw⟩ ∧
    stackRunClock program (raw.length+1)
        ⟨some (.init 0),v,Function.update (fun _ : Slot => []) (.inr .spare) raw.reverse⟩ ≤
      10*(raw.length+1)^2 := by
  let S := Function.update (fun _ : Slot => []) (.inr .spare) raw.reverse
  have hsame : StackCall.frame initCode S (stackPair raw.reverse [])=S := by
    apply StackCall.frame_same _ _ _ initCode_injective
    intro j
    fin_cases j <;> rfl
  have hfinal : StackCall.frame initCode S (stackPair [] raw)=parsedStore [] emptyData raw := by
    rw [pair_frame _ initCode_injective]
    change Function.update (Function.update S (.inr .spare) []) (.inr .input) raw = _
    funext slot
    cases slot with
    | inl k =>
      cases k with
      | inl j => fin_cases j <;> rfl
      | inr j => fin_cases j <;> rfl
    | inr e => cases e <;> rfl
  have hr := transfer_run raw.reverse [] (getIO v)
  have hc := transfer_clock raw.reverse [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution initCode Label.init (.nat 0) getIO putIO
    (StackCall.frame initCode S) (fun data j => StackCall.frame_at _ _ data initCode_injective j)
    (fun data j bs => StackCall.frame_update _ _ data initCode_injective j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil,List.reverse_reverse,List.length_reverse] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  rw [hNC,hc]
  simp only [List.length_nil,Nat.add_zero]
  nlinarith

/-- The input parser reconstructs the binary counter and all five data fields with a cubic
execution bound. -/
theorem frontend (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) :
    ∃ w, Execution program (TM2.init (.inr .spare) (input k d).reverse)
      ⟨some .launch,w,parsedStore k.bits d []⟩
      (40000*(1+(input k d).length)^3) := by
  let raw := input k d
  let v0 : Local := default
  let v1 := putIO v0 none
  let v2 := putIO v1 none
  let v3 := putIO v2 none
  have h0 := init_call raw v0
  have h1 := nat_call k (fields d) [] emptyData v1
  have h2 := nat_transfer_call k (fields d) emptyData v2
  obtain ⟨w,hF⟩ := fields_call k.bits d v3
  have e0 : Execution program (TM2.init (.inr .spare) raw.reverse)
      ⟨some (.nat 0),v1,parsedStore [] emptyData raw⟩ (10*(raw.length+1)^2) :=
    ⟨raw.length+1,h0.1,h0.2⟩
  have e1 : Execution program
      ⟨some (.nat 0),v1,parsedStore [] emptyData raw⟩
      ⟨some (.transfer none 0),v2,
        Function.update (parsedStore [] emptyData (fields d)) (.inr .work5) k.bits.reverse⟩
      (40*(1+raw.length)^2) := ⟨2*k.bits.length+3,h1.1,h1.2⟩
  have e2 : Execution program
      ⟨some (.transfer none 0),v2,
        Function.update (parsedStore [] emptyData (fields d)) (.inr .work5) k.bits.reverse⟩
      ⟨some (.field 0 (.read (.read .unary))),v3,parsedStore k.bits emptyData (fields d)⟩
      (10*(k.bits.length+1)^2) := ⟨k.bits.length+1,h2.1,h2.2⟩
  have hall := ((e0.trans e1).trans e2).trans hF
  refine ⟨w,hall.mono ?_⟩
  let N := 1+raw.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hm : k.bits.length+1 ≤ N := by
    dsimp [N,raw,input,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits]
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    omega
  have hf : 1+(fields d).length ≤ N := by dsimp [N,raw,input]; simp only [List.length_append]; omega
  have hp : N^2 ≤ N^3 := by have ht := Nat.mul_le_mul_left (N^2) hN; nlinarith
  have hpm := Nat.pow_le_pow_left hm 2
  have hpf := Nat.pow_le_pow_left hf 3
  change (10*(raw.length+1)^2+40*(1+raw.length)^2+10*(k.bits.length+1)^2)+
    30000*(1+(fields d).length)^3 ≤ 40000*(1+(input k d).length)^3
  dsimp [N,raw] at hp hpm hpf
  nlinarith

/-- Launching the loop resets its local state and enters counter decrement in one step of clock
cost one. -/
theorem launch_run (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    stackRun program 1 ⟨some .launch,v,parsedStore counter d []⟩ =
      some ⟨some (.loop (.counter .borrow)),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        parsedStore counter d []⟩ ∧
    stackRunClock program 1 ⟨some .launch,v,parsedStore counter d []⟩ = 1 := by
  constructor
  · simp [stackRun,TM2.step,program,TM2.stepAux]
  · simp [stackRunClock,TM2.step,program,TM2.stepAux,stackClock]

/-- The embedded loop performs `k` updates, clears its counter, and enters result reversal with
the stated execution bound. -/
theorem loop_call (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    Execution program ⟨some .launch,v,parsedStore k.bits d []⟩
      ⟨some (.reverseA 0),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        parsedStore [] ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d) []⟩
      (1+4000000*(k+1)^2*(k.bits.length+d.width+10*k+10)^2) := by
  obtain ⟨ticks,hr,hc,_,_⟩ := Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.complete_bounds k k.bits d
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits k)
  let extra : Extra → Bits := fun e => if e=Extra.input then [] else []
  obtain ⟨hN,hNC⟩ := StackCall.execution Sum.inl Label.loop (.reverseA 0) getLoop putLoop
    (StackCall.leftFrame extra) (StackCall.leftFrame_at extra) (StackCall.leftFrame_update extra)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.program program (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.loopCfg,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.haltedCfg,putLoop] at hN hNC
  have e0 : Execution program ⟨some .launch,v,parsedStore k.bits d []⟩
      ⟨some (.loop (.counter .borrow)),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        parsedStore k.bits d []⟩ 1 :=
    ⟨1,(launch_run k.bits d v).1,(launch_run k.bits d v).2.le⟩
  have e1 : Execution program
      ⟨some (.loop (.counter .borrow)),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        parsedStore k.bits d []⟩
      ⟨some (.reverseA 0),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        parsedStore [] ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d) []⟩
      (4000000*(k+1)^2*(k.bits.length+d.width+10*k+10)^2) :=
    ⟨ticks,hN,hNC.trans_le hc⟩
  exact e0.trans e1

/-- The parsed store with the result field moved in reverse order to the serialization
workspace. -/
def reversedStore (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : Slot → Bits :=
  Function.update (parsedStore [] (setField d 4 []) []) (.inr .work5) d.a.reverse

/-- The stack map for result-word reversal is injective. -/
theorem reverseACode_injective : Function.Injective reverseACode := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [reverseACode] at h ⊢

/-- Reversing the result word enters framed encoding with a quadratic clock bound. -/
theorem reverseA_call (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    stackRun program (d.a.length+1) ⟨some (.reverseA 0),v,parsedStore [] d []⟩ =
      some ⟨some (.encode (.copy false .emit)),putIO v none,reversedStore d⟩ ∧
    stackRunClock program (d.a.length+1) ⟨some (.reverseA 0),v,parsedStore [] d []⟩ ≤
      10*(d.a.length+1)^2 := by
  let S := parsedStore [] d []
  have hsame : StackCall.frame reverseACode S (stackPair d.a [])=S := by
    apply StackCall.frame_same _ _ _ reverseACode_injective
    intro j
    fin_cases j <;> rfl
  have hfinal : StackCall.frame reverseACode S (stackPair [] d.a.reverse)=reversedStore d := by
    rw [pair_frame _ reverseACode_injective]
    change Function.update (Function.update (parsedStore [] d []) (.inl (.inl 4)) [])
      (.inr .work5) d.a.reverse = _
    have hi : (Fin.castLE (show 5≤12 by decide) (4:Fin 5) : Fin 12)=4 := by decide
    rw [← hi,parsedStore_setField [] d [] (4:Fin 5) []]
    rfl
  have hr := transfer_run d.a [] (getIO v)
  have hc := transfer_clock d.a [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution reverseACode Label.reverseA (.encode (.copy false .emit))
    getIO putIO (StackCall.frame reverseACode S)
    (fun data j => StackCall.frame_at _ _ data reverseACode_injective j)
    (fun data j bs => StackCall.frame_update _ _ data reverseACode_injective j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  rw [hNC,hc]
  simp only [List.length_nil,Nat.add_zero]
  nlinarith

/-- The stack map for framed encoding is injective. -/
theorem encodeCode_injective : Function.Injective encodeCode := by
  intro a b h
  cases a <;> cases b <;> simp [encodeCode] at h ⊢

/-- Framed encoding writes the result frame to the output buffer and enters cleanup with a cubic
clock bound. -/
theorem encode_call (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    ∃ ticks, stackRun program ticks ⟨some (.encode (.copy false .emit)),v,reversedStore d⟩ =
      some ⟨some (.drain 0 0),putIO v none,
        Function.update (reversedStore d) (.inr .buffer) (framed d.a)⟩ ∧
    stackRunClock program ticks ⟨some (.encode (.copy false .emit)),v,reversedStore d⟩ ≤
      10000*(1+d.a.length)^3 := by
  let S := reversedStore d
  have hsame : StackCall.frame encodeCode S (FrameCopy.store d.a.reverse [] [] [] [] [])=S := by
    apply StackCall.frame_same _ _ _ encodeCode_injective
    intro j
    cases j <;> rfl
  have hfinal : StackCall.frame encodeCode S (FrameCopy.store d.a.reverse [] [] [] [] (framed d.a))=
      Function.update S (.inr .buffer) (framed d.a) := by
    funext slot
    cases slot with
    | inl j =>
      rw [WordValidator.frame_outside encodeCode S _ _ (by intro j; cases j <;> simp [encodeCode])]
      rfl
    | inr e =>
      cases e
      all_goals first
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.source
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.restore
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.copy
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.count
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.temporary
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.markers
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.header
      | exact StackCall.frame_at encodeCode S _ encodeCode_injective FrameCopy.Slot.output
      | (rw [WordValidator.frame_outside encodeCode S _ _ (by intro j; cases j <;> simp [encodeCode])]; rfl)
  obtain ⟨ticks,hr,hc⟩ := FrameCopy.complete d.a [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution encodeCode Label.encode (.drain 0 0) getIO putIO
    (StackCall.frame encodeCode S) (fun data j => StackCall.frame_at _ _ data encodeCode_injective j)
    (fun data j bs => StackCall.frame_update _ _ data encodeCode_injective j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) FrameCopy.program program (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil] at hN hNC
  rw [hfinal] at hN
  refine ⟨ticks,hN,hNC.trans_le ?_⟩
  simpa only [List.length_nil,Nat.add_zero] using! hc

/-- Framing a single-stack store equals updating the selected caller stack. -/
theorem one_frame {J : Type} [DecidableEq J] (code : Fin 1 → J) (S : J → Bits) (bits : Bits) :
    StackCall.frame code S (Normalization.singleStack bits) = Function.update S (code 0) bits := by
  have hinj : Function.Injective code := fun _ _ _ => Subsingleton.elim _ _
  funext j
  by_cases h : j=code 0
  · subst j
    simpa only [Normalization.singleStack_zero,Function.update_self] using!
      StackCall.frame_at code S (Normalization.singleStack bits) hinj 0
  · rw [WordValidator.frame_outside code S _ j (by
      intro i
      have hi : i=0 := Subsingleton.elim _ _
      rw [hi]
      exact Ne.symm h)]
    rw [Function.update_of_ne h]

/-- Draining a selected cleanup stack empties it and advances to the next phase with a quadratic
execution bound. -/
theorem drain_call (i : Fin 5) (S : Slot → Bits) (v : Local) :
    Execution program ⟨some (.drain i 0),v,S⟩
      ⟨some (nextDrain i),putIO v none,Function.update S (drainCode i 0) []⟩
      (10*(1+(S (drainCode i 0)).length)^2) := by
  have hinj : Function.Injective (drainCode i) := fun _ _ _ => Subsingleton.elim _ _
  have hsame : StackCall.frame (drainCode i) S
      (Normalization.singleStack (S (drainCode i 0)))=S := by
    rw [one_frame,Function.update_eq_self]
  have hfinal := one_frame (drainCode i) S []
  have hr := Normalization.drain_run (S (drainCode i 0)) (getIO v)
  have hc := Normalization.drain_clock (S (drainCode i 0)) (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution (drainCode i) (Label.drain i) (nextDrain i) getIO putIO
    (StackCall.frame (drainCode i) S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j bs => StackCall.frame_update _ _ data hinj j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨(S (drainCode i 0)).length+1,hN,?_⟩
  rw [hNC,hc]
  nlinarith

/-- The binary expansion of a natural number has length at most the number plus one. -/
theorem bits_length_le (n : ℕ) : n.bits.length ≤ n+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

/-- A framed word has length at most three times its payload length plus three. -/
theorem framed_length_le (bits : Bits) : (framed bits).length ≤ 3*bits.length+3 := by
  have h := bits_length_le bits.length
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

/-- Each preparation update adds exactly one bit to the result word. -/
theorem iterate_a_length (n : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) :
    (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[n]) d).a).length=d.a.length+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[n]) d).a).length+1=d.a.length+(n+1)
    omega

/-- Cleanup clears all remaining arithmetic workspace while preserving the framed output buffer,
with a quadratic execution bound. -/
theorem clear_call (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    Execution program
      ⟨some (.drain 0 0),v,Function.update (reversedStore d) (.inr .buffer) (framed d.a)⟩
      ⟨some (.reverseOutput 0),putIO v none,
        Function.update (fun _ : Slot => []) (.inr .buffer) (framed d.a)⟩
      (50*(1+d.width)^2) := by
  let S0 := Function.update (reversedStore d) (.inr .buffer) (framed d.a)
  let S1 := Function.update S0 (drainCode 0 0) []
  let S2 := Function.update S1 (drainCode 1 0) []
  let S3 := Function.update S2 (drainCode 2 0) []
  let S4 := Function.update S3 (drainCode 3 0) []
  let S5 := Function.update S4 (drainCode 4 0) []
  let w := putIO v none
  have h0 := drain_call 0 S0 v
  have h1 := drain_call 1 S1 w
  have h2 := drain_call 2 S2 w
  have h3 := drain_call 3 S3 w
  have h4 := drain_call 4 S4 w
  obtain ⟨ha,hb,hq,hr,haa⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.width_fields d
  have hl0 : (S0 (drainCode 0 0)).length ≤ d.width := by change d.sq4.length ≤ _; exact ha
  have hl1 : (S1 (drainCode 1 0)).length ≤ d.width := by change d.lin2.length ≤ _; exact hb
  have hl2 : (S2 (drainCode 2 0)).length ≤ d.width := by change d.q.length ≤ _; exact hq
  have hl3 : (S3 (drainCode 3 0)).length ≤ d.width := by change d.rhs.length ≤ _; exact hr
  have hl4 : (S4 (drainCode 4 0)).length ≤ d.width := by
    change d.a.reverse.length ≤ _
    simpa only [List.length_reverse] using! haa
  have b0 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_left hl0 1) 2)
  have b1 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_left hl1 1) 2)
  have b2 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_left hl2 1) 2)
  have b3 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_left hl3 1) 2)
  have b4 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_left hl4 1) 2)
  have hall :=
      ((((h0.mono b0).trans (h1.mono b1)).trans (h2.mono b2)).trans (h3.mono b3)).trans (h4.mono b4)
  have hfinal : S5=Function.update (fun _ : Slot => []) (.inr .buffer) (framed d.a) := by
    funext slot
    cases slot with
    | inl k =>
      cases k with
      | inl j => fin_cases j <;> rfl
      | inr j => fin_cases j <;> rfl
    | inr e => cases e <;> rfl
  change Execution program _ ⟨some (.reverseOutput 0),w,S5⟩ _ at hall
  rw [hfinal] at hall
  exact hall.mono (by omega)

/-- The stack map for final output transfer is injective. -/
theorem outputCode_injective : Function.Injective outputCode := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [outputCode] at h ⊢

/-- Final transfer reverses the output buffer into the output stack with a quadratic clock
bound. -/
theorem output_call (out : Bits) (v : Local) :
    stackRun program (out.length+1)
        ⟨some (.reverseOutput 0),v,Function.update (fun _ : Slot => []) (.inr .buffer) out⟩ =
      some ⟨some .done,putIO v none,
        Function.update (fun _ : Slot => []) (.inr .output) out.reverse⟩ ∧
    stackRunClock program (out.length+1)
        ⟨some (.reverseOutput 0),v,Function.update (fun _ : Slot => []) (.inr .buffer) out⟩ ≤
      10*(out.length+1)^2 := by
  let S := Function.update (fun _ : Slot => []) (.inr .buffer) out
  have hsame : StackCall.frame outputCode S (stackPair out [])=S := by
    apply StackCall.frame_same _ _ _ outputCode_injective
    intro j
    fin_cases j <;> rfl
  have hfinal : StackCall.frame outputCode S (stackPair [] out.reverse)=
      Function.update (fun _ : Slot => []) (.inr .output) out.reverse := by
    rw [pair_frame _ outputCode_injective]
    funext slot
    cases slot with
    | inl k => rfl
    | inr e => cases e <;> rfl
  have hr := transfer_run out [] (getIO v)
  have hc := transfer_clock out [] (getIO v)
  obtain ⟨hN,hNC⟩ := StackCall.execution outputCode Label.reverseOutput .done getIO putIO
    (StackCall.frame outputCode S) (fun data j => StackCall.frame_at _ _ data outputCode_injective j)
    (fun data j bs => StackCall.frame_update _ _ data outputCode_injective j bs)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram program (fun _ => rfl) v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    getIO,putIO,hsame,List.append_nil] at hN hNC hc
  rw [hfinal] at hN
  refine ⟨hN,?_⟩
  rw [hNC,hc]
  simp only [List.length_nil,Nat.add_zero]
  nlinarith

/-- The final control label halts in one step of clock cost one without changing the stack
store. -/
theorem done_run (S : Slot → Bits) (v : Local) :
    stackRun program 1 ⟨some .done,v,S⟩=some ⟨none,default,S⟩ ∧
    stackRunClock program 1 ⟨some .done,v,S⟩=1 := by
  constructor
  · simp [stackRun,TM2.step,program,TM2.stepAux]
  · simp [stackRunClock,TM2.step,program,TM2.stepAux,stackClock]

/-- Result serialization halts with only the reversed result frame on the output stack and has a
cubic execution bound. -/
theorem serializer (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Local) :
    Execution program ⟨some (.reverseA 0),v,parsedStore [] d []⟩
      ⟨none,default,Function.update (fun _ : Slot => []) (.inr .output) (framed d.a).reverse⟩
      (100000*(1+d.width)^3) := by
  let w := putIO v none
  have hR := reverseA_call d v
  obtain ⟨ticks,hE,hEC⟩ := encode_call d w
  have e0 : Execution program ⟨some (.reverseA 0),v,parsedStore [] d []⟩
      ⟨some (.encode (.copy false .emit)),w,reversedStore d⟩ (10*(d.a.length+1)^2) :=
    ⟨d.a.length+1,hR.1,hR.2⟩
  have e1 : Execution program ⟨some (.encode (.copy false .emit)),w,reversedStore d⟩
      ⟨some (.drain 0 0),w,Function.update (reversedStore d) (.inr .buffer) (framed d.a)⟩
      (10000*(1+d.a.length)^3) := ⟨ticks,hE,hEC⟩
  have e2 := clear_call d w
  have hO := output_call (framed d.a) w
  have e3 : Execution program
      ⟨some (.reverseOutput 0),w,Function.update (fun _ : Slot => []) (.inr .buffer) (framed d.a)⟩
      ⟨some .done,w,Function.update (fun _ : Slot => []) (.inr .output) (framed d.a).reverse⟩
      (10*((framed d.a).length+1)^2) := ⟨(framed d.a).length+1,hO.1,hO.2⟩
  have hD := done_run (Function.update (fun _ : Slot => []) (.inr .output) (framed d.a).reverse) w
  have e4 : Execution program
      ⟨some .done,w,Function.update (fun _ : Slot => []) (.inr .output) (framed d.a).reverse⟩
      ⟨none,default,Function.update (fun _ : Slot => []) (.inr .output) (framed d.a).reverse⟩ 1 :=
    ⟨1,hD.1,hD.2.le⟩
  have hall := (((e0.trans e1).trans e2).trans e3).trans e4
  apply hall.mono
  let N := 1+d.width
  have hN : 1 ≤ N := by dsimp [N]; omega
  have ha :=
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.width_fields d).2.2.2.2
  have hp2 := Nat.pow_le_pow_left (show d.a.length+1 ≤ N by dsimp [N]; omega) 2
  have hp3 := Nat.pow_le_pow_left (show 1+d.a.length ≤ N by dsimp [N]; omega) 3
  have hout : (framed d.a).length+1 ≤ 4*N := by
    have h := framed_length_le d.a
    dsimp [N]
    omega
  have hpo := Nat.pow_le_pow_left hout 2
  have hpN : N^2 ≤ N^3 := by have h := Nat.mul_le_mul_left (N^2) hN; nlinarith
  have hOne : 1 ≤ N^2 := by have h := Nat.pow_le_pow_left hN 2; simpa using! h
  dsimp [N] at hp2 hp3 hpo hpN hOne
  nlinarith

/-- The data width is at most the encoded input length. -/
theorem width_le_input (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : d.width ≤ (input k d).length := by
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.width
  dsimp [input,fields,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed]
  simp only [List.length_append]
  omega

/-- The binary counter length is at most the encoded input length. -/
theorem counter_length_le_input (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) : k.bits.length ≤ (input k d).length := by
  dsimp [input,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits]
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

/-- The full stack-machine program computes the framed iterated result and halts within the
stated quartic execution bound. -/
theorem complete (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) :
    Execution program (TM2.init (.inr .spare) (input k d).reverse)
      ⟨none,default,Function.update (fun _ : Slot => []) (.inr .output) (output k d).reverse⟩
      (2000000000*(1+k+(input k d).length)^4) := by
  obtain ⟨v,hF⟩ := frontend k d
  have hL := loop_call k d v
  have hS := serializer ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d)
    (putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)))
  have hall := (hF.trans hL).trans hS
  apply hall.mono
  let N := 1+k+(input k d).length
  let L := k.bits.length+d.width+10*k+10
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hw := width_le_input k d
  have hc := counter_length_le_input k d
  have hi : 1+(input k d).length ≤ N := by dsimp [N]; omega
  have hk : k+1 ≤ N := by dsimp [N]; omega
  have hLN : L ≤ 12*N := by dsimp [L,N]; omega
  have hpL := Nat.mul_le_mul (Nat.pow_le_pow_left hk 2) (Nat.pow_le_pow_left hLN 2)
  have hpL' : (k+1)^2*L^2 ≤ 144*N^4 := by nlinarith [hpL]
  have hwn :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.iterate_width k d
  have hnext :
      1+((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d).width ≤ 11*N := by dsimp [N]; omega
  have hpnext := Nat.pow_le_pow_left hnext 3
  have hpi := Nat.pow_le_pow_left hi 3
  have hpN : N^3 ≤ N^4 := by have h := Nat.mul_le_mul_left (N^3) hN; nlinarith
  have hOne : 1 ≤ N^4 := by have h := Nat.pow_le_pow_left hN 4; simpa using! h
  change 40000*(1+(input k d).length)^3+
    (1+4000000*(k+1)^2*L^2)+100000*(1+((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d).width)^3 ≤ 2000000000*N^4
  nlinarith [hpL',hpnext,hpi,hpN,hOne]

/-- A single finite-state Turing machine computes every encoded loop instance with time and
space bounded by a common constant times the stated fourth power. -/
theorem uniform_raw_loop_machine :
    ∃ (q : ℕ) (M : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0<C ∧
      ∀ (k : ℕ) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data),
        Runs M (input k d) (output k d)
          (C*(1+k+(input k d).length)^4) (C*(1+k+(input k d).length)^4) := by
  obtain ⟨q,M,C,hC,hM⟩ := raw_compiler_separate program (.inr .spare) (.inr .output)
  refine ⟨q,M,3000000000*C,Nat.mul_pos (by decide) hC,?_⟩
  intro k d
  obtain ⟨ticks,hr,hclock⟩ := complete k d
  have hraw := hM (input k d) (output k d) ticks default hr
  have hmax := maxClock_le_clock program ticks (TM2.init (.inr .spare) (input k d).reverse)
  have hw :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.iterate_width k d
  have hi := width_le_input k d
  have ha :=
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.width_fields ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d)).2.2.2.2
  have hout :=
      framed_length_le
      (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d).a)
  let N := 1+k+(input k d).length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hin : 1+(input k d).length ≤ N := by dsimp [N]; omega
  have hout' : 1+(output k d).length ≤ 34*N := by dsimp [N,output]; omega
  have hclockN : stackRunClock program ticks (TM2.init (.inr .spare) (input k d).reverse) ≤
      2000000000*N^4 := hclock
  have hin2 := Nat.pow_le_pow_left hin 2
  have hout2 := Nat.pow_le_pow_left hout' 2
  have hp : N^2 ≤ N^4 := by
    have h := Nat.pow_le_pow_left hN 2
    nlinarith [sq_nonneg (N^2:ℤ)]
  apply runs_mono hraw
  · have hb : (1+(input k d).length)^2+
        stackRunClock program ticks (TM2.init (.inr .spare) (input k d).reverse)+
        (1+(output k d).length)^2 ≤ 3000000000*N^4 := by nlinarith [hclockN]
    calc
      _ ≤ C*(3000000000*N^4) := Nat.mul_le_mul_left C hb
      _ = _ := by dsimp [N]; ring
  · have hb : (1+(input k d).length)^2+
        stackRunMaxClock program ticks (TM2.init (.inr .spare) (input k d).reverse)+
        (1+(output k d).length)^2 ≤ 3000000000*N^4 := by nlinarith [hclockN]
    calc
      _ ≤ C*(3000000000*N^4) := Nat.mul_le_mul_left C hb
      _ = _ := by dsimp [N]; ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine
