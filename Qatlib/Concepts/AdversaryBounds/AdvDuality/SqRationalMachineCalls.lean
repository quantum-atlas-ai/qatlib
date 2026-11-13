/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalArithmetic
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs
import Mathlib.Analysis.Real.Cardinality

/-!
# Subroutine calls for the rational word machine

This module embeds framed-word input, copying, transfer, draining, table lookup, addition, and
multiplication routines into the rational word machine. `Machine.Storage` describes the stack
contents, the call lemmas such as `Machine.take_call` establish execution and clock bounds in a
saved heap, and the corresponding payload lemmas such as `Machine.mul_data` express the
resulting updates through `Machine.dataHeap`.

The theorem `no_total_real_decoder` records the cardinality obstruction to decoding every real
number from finite bit words. For general background on finite representations and computation,
see [KitaevShenVyalyi2002].

## Main statements

* `no_total_real_decoder`: finite bit words cannot encode every real number.
* `Machine.take_call`: execution of the embedded frame-reading routine.
* `Machine.mul_data`: multiplication updates on payload heaps.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002] *Classical and Quantum Computation*.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

set_option autoImplicit false
set_option maxHeartbeats 2500000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Machine
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- No function from finite Boolean words to the real numbers is surjective. -/
theorem no_total_real_decoder : ∀ decode : List Bool → ℝ, ¬Function.Surjective decode :=
  fun decode => not_surjective_countable_uncountable decode

namespace Machine
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- The bit-word contents of the machine's program, values, lookup storage, arithmetic buffers,
frame, and output stacks. -/
structure Storage where
  code : Bits
  values : Bits
  table : Bits
  buffers : Fin 6 → Bits
  index : Bits
  found : Bits
  frame : Bits
  output : Bits

namespace Storage

/-- Interpret a storage record as a machine heap, placing its fields in their payload slots and
leaving auxiliary slots empty. -/
def heap (s : Storage) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits
  | .inl .program => s.code
  | .inl .values => s.values
  | .inl .frame => s.frame
  | .inl .output => s.output
  | .inl (.arithmetic i) => s.buffers i
  | .inl (.lookup k) => ReadonlyTableGet.store s.table [] s.index s.found k
  | .inr _ => []

/-- The storage representation of a word state and program code, with an encoded value stack, a
reversed parameter stream, and empty working stacks. -/
def canonical (code : Bits) (s : WordState) : Storage :=
  ⟨code,valueStack s.values,(TableGet.stream s.parameters).reverse,
    (fun _ => []),[],[],[],[]⟩

/-- Updating the program slot of a storage heap agrees with updating the `code` field of the
storage record. -/
theorem update_program (s : Storage) (bits : Bits) :
    Function.update s.heap (.inl .program) bits = ({s with code:=bits} : Storage).heap := by
  funext k
  cases k with
  | inl p => cases p <;> simp [heap]
  | inr h => simp [heap]
end Storage

/-- The embedded take routine removes a leading frame and prepends its reversed payload to the
destination, returning to the mode's return phase. Its stack-run clock is bounded by the
stated cubic expression in the source and destination lengths. -/
theorem take_call (mode : TakeMode) (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (bits tail out : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ ticks last,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.take mode takeEntry),v,
          StackCall.frame (takeCode mode) outside (FramedTake.store (framed bits++tail) [] [] out)⟩ =
        some ⟨some (.phase (takeReturn mode)),putTake v last,
          StackCall.frame (takeCode mode) outside (FramedTake.store tail [] [] (bits.reverse++out))⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.take mode takeEntry),v,
          StackCall.frame (takeCode mode) outside (FramedTake.store (framed bits++tail) [] [] out)⟩ ≤
        5000*(bits.length+1)*(1+(framed bits++tail).length+out.length)^2 := by
  obtain ⟨ticks,last,hr,hc,_⟩ :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.read_frame_actual bits tail out (getTake v)
  let frame := StackCall.frame (takeCode mode) outside
  have hi := takeCode_injective mode
  obtain ⟨hR,hC⟩ := StackCall.execution (takeCode mode) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.take mode) (.phase (takeReturn mode))
    getTake putTake frame (fun S k => StackCall.frame_at _ outside S hi k)
    (fun S k xs => StackCall.frame_update _ outside S hi k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    FramedTake.program Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) v ticks _ _ hr
  refine ⟨ticks,last,?_,?_⟩
  · exact hR
  · exact hC.trans_le hc
end Machine
end Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- The embedded copy routine preserves its reversed source word and prepends the framed word to
the destination, returning to the mode's return phase. Its stack-run clock is at most `10000
* (1 + bits.length + out.length)^3`. -/
theorem copy_call (mode : CopyMode) (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (bits out : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.copy mode copyEntry),v,
          StackCall.frame (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) outside (FrameCopy.store bits.reverse [] [] [] [] out)⟩ =
        some ⟨some (.phase (copyReturn mode)),putCopy v none,
          StackCall.frame (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) outside (FrameCopy.store bits.reverse [] [] [] [] (framed bits++out))⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.copy mode copyEntry),v,
          StackCall.frame (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) outside (FrameCopy.store bits.reverse [] [] [] [] out)⟩ ≤
        10000*(1+bits.length+out.length)^3 := by
  obtain ⟨ticks,hr,hc,_⟩ :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.write_frame_actual bits out (getCopy v)
  let frame :=
      StackCall.frame
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) outside
  have hi := copyCode_injective mode
  obtain ⟨hR,hC⟩ := StackCall.execution (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.copy mode) (.phase (copyReturn mode))
    getCopy putCopy frame (fun S k => StackCall.frame_at _ outside S hi k)
    (fun S k xs => StackCall.frame_update _ outside S hi k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    FrameCopy.program Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) v ticks _ _ hr
  exact ⟨ticks,hR,hC.trans_le hc⟩

/-- In `bits.length + 1` stack steps, the embedded transfer routine empties its source and
prepends its reversal to the destination. Its stack-run clock is at most `bits.length * (2 *
(bits.length + out.length) + 5) + 3`. -/
theorem transfer_call (mode : TransferMode) (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (bits out : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    let ticks := bits.length+1
    stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.transfer mode 0),v,
        StackCall.frame (transferCode mode) outside (stackPair bits out)⟩ =
      some ⟨some (.phase (transferReturn mode)),Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v none,
        StackCall.frame (transferCode mode) outside (stackPair [] (bits.reverse++out))⟩ ∧
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.transfer mode 0),v,
        StackCall.frame (transferCode mode) outside (stackPair bits out)⟩ ≤
      bits.length*(2*(bits.length+out.length)+5)+3 := by
  have hr :=
      transfer_run bits out
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO v)
  let frame := StackCall.frame (transferCode mode) outside
  have hi := transferCode_injective mode
  obtain ⟨hR,hC⟩ := StackCall.execution (transferCode mode) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.transfer mode) (.phase (transferReturn mode))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO frame (fun S k => StackCall.frame_at _ outside S hi k)
    (fun S k xs => StackCall.frame_update _ outside S hi k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    transferProgram Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) v (bits.length+1) _ _ hr
  exact ⟨hR,(hC.trans (transfer_clock bits out (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO v))).le⟩

/-- In `bits.length + 1` stack steps, the embedded drain routine empties its stack and reaches
the mode's return phase. Its stack-run clock is at most `bits.length^2 + 3 * bits.length +
3`. -/
theorem drain_call (mode : DrainMode) (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (bits : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    let ticks := bits.length+1
    stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.drain mode 0),v,
        StackCall.frame (drainCode mode) outside (Normalization.singleStack bits)⟩ =
      some ⟨some (.phase (drainReturn mode)),Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v none,
        StackCall.frame (drainCode mode) outside (Normalization.singleStack [])⟩ ∧
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.drain mode 0),v,
        StackCall.frame (drainCode mode) outside (Normalization.singleStack bits)⟩ ≤
      bits.length^2+3*bits.length+3 := by
  have hr :=
      Normalization.drain_run bits
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO v)
  let frame := StackCall.frame (drainCode mode) outside
  have hi := drainCode_injective mode
  obtain ⟨hR,hC⟩ := StackCall.execution (drainCode mode) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.drain mode) (.phase (drainReturn mode))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO frame (fun S k => StackCall.frame_at _ outside S hi k)
    (fun S k xs => StackCall.frame_update _ outside S hi k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    Normalization.drainProgram Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) v (bits.length+1) _ _ hr
  exact ⟨hR,(hC.trans (Normalization.drain_clock bits (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.getIO v))).le⟩

/-- The embedded lookup routine preserves the table, clears the index, and prepends the reversed
selected word to the output, using the empty word for an out-of-range index. It reaches the
lookup-copy entry with the stated polynomial stack-run clock bound. -/
theorem lookup_call (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (values : List Bits) (index out : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ ticks last,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.lookup (.copy .emit)),v,
          StackCall.frame lookupCode outside (ReadonlyTableGet.store (TableGet.stream values).reverse [] index out)⟩ =
        some ⟨some (.copy .lookup copyEntry),putLookup v last,
          StackCall.frame lookupCode outside (ReadonlyTableGet.store (TableGet.stream values).reverse [] []
            ((values.getD (binaryValue index) []).reverse++out))⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
        ⟨some (.lookup (.copy .emit)),v,
          StackCall.frame lookupCode outside (ReadonlyTableGet.store (TableGet.stream values).reverse [] index out)⟩ ≤
        30000*(1+(TableGet.stream values).length)*(1+(TableGet.stream values).length+index.length+out.length)^2 := by
  obtain ⟨ticks,last,hr,hc⟩ := ReadonlyTableGet.complete values index out (getLookup v)
  let frame := StackCall.frame lookupCode outside
  obtain ⟨hR,hC⟩ := StackCall.execution lookupCode Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.lookup (.copy .lookup copyEntry)
    getLookup putLookup frame (fun S k => StackCall.frame_at _ outside S lookupCode_injective k)
    (fun S k xs => StackCall.frame_update _ outside S lookupCode_injective k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    ReadonlyTableGet.program Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) v ticks _ _ hr
  exact ⟨ticks,last,hR,hC.trans_le hc⟩

/-- The embedded addition routine consumes the two operand stacks and writes the reversed
`bitAdd` result in `max x.length y.length + 1` stack steps. It reaches the result-copy entry
with stack-run clock at most `addClockBound x y`. -/
theorem add_call (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (x y : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    let ticks := max x.length y.length+1
    stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.add .loop),putAdd v AddVar.init,
        StackCall.frame addCode outside (addStacks x y [])⟩ =
      some ⟨some (.copy .result copyEntry),putAdd v (Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum.finalAddVar x y),
        StackCall.frame addCode outside (addStacks [] [] (bitAdd x y).reverse)⟩ ∧
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.add .loop),putAdd v AddVar.init,
        StackCall.frame addCode outside (addStacks x y [])⟩ ≤ addClockBound x y := by
  obtain ⟨hr,hc,_⟩ := Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum.add_exact_end x y
  let frame := StackCall.frame addCode outside
  obtain ⟨hR,hC⟩ := StackCall.execution addCode Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.add (.copy .result copyEntry)
    getAdd putAdd frame (fun S k => StackCall.frame_at _ outside S addCode_injective k)
    (fun S k xs => StackCall.frame_update _ outside S addCode_injective k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    addProgram Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) (putAdd v AddVar.init) _ _ _ hr
  exact ⟨hR,hC.trans_le hc⟩

/-- The embedded multiplication routine reaches the master-clearing phase after `mulTotalTicks x
y y.length + 2` stack steps with the `mulAcc` result and the preserved reversed first
operand. Its stack-run clock is at most `31720 * (1 + x.length + y.length)^4`. -/
theorem mul_call (outside : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (x y : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    let ticks := mulTotalTicks x y y.length+2
    stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.multiply .outer),putMul v MulVar.init,
        StackCall.frame mulCode outside (mulStacks [] [] [] x.reverse y.reverse [])⟩ =
      some ⟨some (.phase .clearMaster),putMul v MulVar.init,
        StackCall.frame mulCode outside (mulStacks (mulAcc x y y.length) [] [] x.reverse [] [])⟩ ∧
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks
      ⟨some (.multiply .outer),putMul v MulVar.init,
        StackCall.frame mulCode outside (mulStacks [] [] [] x.reverse y.reverse [])⟩ ≤
      31720*(1+x.length+y.length)^4 := by
  obtain ⟨hr,hc,_,_⟩ := Qatlib.Concepts.AdversaryBounds.AdvDuality.Product.mul_core_complete x y
  let frame := StackCall.frame mulCode outside
  obtain ⟨hR,hC⟩ := StackCall.execution mulCode Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label.multiply (.phase .clearMaster)
    getMul putMul frame (fun S k => StackCall.frame_at _ outside S mulCode_injective k)
    (fun S k xs => StackCall.frame_update _ outside S mulCode_injective k xs)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    mulProgram Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (fun _ => rfl) (putMul v MulVar.init) _ _ _ hr
  exact ⟨hR,hC.trans_le hc⟩
end Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- Extend a payload-stack assignment to a machine heap by making every auxiliary stack empty. -/
def dataHeap (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits
  | .inl p => S p
  | .inr _ => []

/-- A framed heap equals a target heap when they agree on every injectively assigned call slot
and the target agrees with the saved heap outside those slots. -/
theorem frame_target {K : Type} [DecidableEq K] (code : K → Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot)
    (saved target : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot → Bits) (data : K → Bits) (hinj : Function.Injective code)
    (hm : ∀ k,target (code k)=data k)
    (ho : ∀ bank,(∀ k,code k≠bank) → target bank=saved bank) :
    StackCall.frame code saved data=target := by
  classical
  funext bank
  by_cases he : ∃ k,code k=bank
  · obtain ⟨k,rfl⟩ := he
    exact (StackCall.frame_at code saved data hinj k).trans (hm k).symm
  · rw [WordValidator.frame_outside code saved data bank (fun k hk => he ⟨k,hk⟩)]
    exact (ho bank (fun k hk => he ⟨k,hk⟩)).symm

/-- The payload assignment after taking a frame: replace the source by its tail and prepend the
reversed payload to the target. -/
def takeResult (mode : TakeMode) (bits tail : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update (Function.update S (takeSource mode) tail) (takeTarget mode)
    (bits.reverse++S (takeTarget mode))

/-- If the selected source begins with `framed bits`, the embedded take routine produces
`takeResult` on the payload heap. It reaches the mode's return phase with the stated
stack-run clock bound. -/
theorem take_data (mode : TakeMode) (bits tail : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hr : S (takeSource mode)=framed bits++tail) :
    ∃ ticks last,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.take mode takeEntry),v,dataHeap S⟩ =
        some ⟨some (.phase (takeReturn mode)),putTake v last,dataHeap (takeResult mode bits tail S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.take mode takeEntry),v,dataHeap S⟩ ≤
        5000*(bits.length+1)*(1+(framed bits++tail).length+(S (takeTarget mode)).length)^2 := by
  have hi := takeCode_injective mode
  have hsame : StackCall.frame (takeCode mode) (dataHeap S)
      (FramedTake.store (framed bits++tail) [] [] (S (takeTarget mode)))=dataHeap S := by
    apply StackCall.frame_same _ _ _ hi
    intro key
    cases key <;> simp [dataHeap,takeCode,FramedTake.store,hr]
  have hfinal : StackCall.frame (takeCode mode) (dataHeap S)
      (FramedTake.store tail [] [] (bits.reverse++S (takeTarget mode))) =
      dataHeap (takeResult mode bits tail S) := by
    apply frame_target _ _ _ _ hi
    · intro key
      cases mode <;> cases key <;>
        simp [dataHeap,takeCode,takeResult,takeSource,takeTarget,table,FramedTake.store]
    · intro bank hno
      cases bank with
      | inl p =>
        have hs : p≠takeSource mode := fun h => hno .reader (congrArg Sum.inl h.symm)
        have ht : p≠takeTarget mode := fun h => hno .output (congrArg Sum.inl h.symm)
        simp [dataHeap,takeResult,hs,ht]
      | inr a => rfl
  obtain ⟨ticks,last,hR,hC⟩ := take_call mode (dataHeap S) bits tail (S (takeTarget mode)) v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨ticks,last,hR,hC⟩

/-- The payload assignment obtained by prepending `framed bits` to the selected copy target. -/
def copyResult (mode : CopyMode) (bits : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update S (copyTarget mode) (framed bits++S (copyTarget mode))

/-- If the selected source contains `bits.reverse`, the embedded copy routine produces
`copyResult` on the payload heap. Its stack-run clock is at most `10000 * (1 + bits.length +
(S (copyTarget mode)).length)^3`. -/
theorem copy_data (mode : CopyMode) (bits : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hr : S (copySource mode)=bits.reverse) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.copy mode copyEntry),v,dataHeap S⟩ =
        some ⟨some (.phase (copyReturn mode)),putCopy v none,dataHeap (copyResult mode bits S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.copy mode copyEntry),v,dataHeap S⟩ ≤
        10000*(1+bits.length+(S (copyTarget mode)).length)^3 := by
  have hi := copyCode_injective mode
  have hsame : StackCall.frame (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) (dataHeap S)
      (FrameCopy.store bits.reverse [] [] [] [] (S (copyTarget mode)))=dataHeap S := by
    apply StackCall.frame_same _ _ _ hi
    intro key
    cases key <;> simp
        [dataHeap,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode,FrameCopy.store,hr]
  have hfinal : StackCall.frame (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode mode) (dataHeap S)
      (FrameCopy.store bits.reverse [] [] [] [] (framed bits++S (copyTarget mode))) =
      dataHeap (copyResult mode bits S) := by
    apply frame_target _ _ _ _ hi
    · intro key
      cases mode <;> cases key <;>
        simp [dataHeap,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.copyCode,copyResult,copySource,copyTarget,lookupOutput,FrameCopy.store]
      all_goals simpa only [copySource,lookupOutput] using! hr
    · intro bank hno
      cases bank with
      | inl p =>
        have ht : p≠copyTarget mode := fun h => hno .output (congrArg Sum.inl h.symm)
        simp [dataHeap,copyResult,ht]
      | inr a => rfl
  obtain ⟨ticks,hR,hC⟩ := copy_call mode (dataHeap S) bits (S (copyTarget mode)) v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨ticks,hR,hC⟩

/-- The payload assignment obtained by emptying the selected transfer source and prepending its
reversal to the selected target. -/
def transferResult (mode : TransferMode) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update (Function.update S (transferSource mode) []) (transferTarget mode)
    ((S (transferSource mode)).reverse++S (transferTarget mode))

/-- The embedded transfer routine produces `transferResult` on an arbitrary payload heap and
returns to the mode's return phase. Its stack-run clock satisfies the stated quadratic bound
in the source and target lengths. -/
theorem transfer_data (mode : TransferMode) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.transfer mode 0),v,dataHeap S⟩ =
        some ⟨some (.phase (transferReturn mode)),Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v none,dataHeap (transferResult mode S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.transfer mode 0),v,dataHeap S⟩ ≤
        (S (transferSource mode)).length *
          (2*((S (transferSource mode)).length+(S (transferTarget mode)).length)+5)+3 := by
  have hi := transferCode_injective mode
  have hsame : StackCall.frame (transferCode mode) (dataHeap S)
      (stackPair (S (transferSource mode)) (S (transferTarget mode)))=dataHeap S := by
    apply StackCall.frame_same _ _ _ hi
    intro key
    fin_cases key <;> rfl
  have hfinal : StackCall.frame (transferCode mode) (dataHeap S)
      (stackPair [] ((S (transferSource mode)).reverse++S (transferTarget mode))) =
      dataHeap (transferResult mode S) := by
    apply frame_target _ _ _ _ hi
    · intro key
      fin_cases key <;> cases mode <;>
        simp [dataHeap,transferCode,transferResult,transferSource,transferTarget,table,lookupIndex,stackPair]
    · intro bank hno
      cases bank with
      | inl p =>
        have hs : p≠transferSource mode := fun h => hno 0 (congrArg Sum.inl h.symm)
        have ht : p≠transferTarget mode := fun h => hno 1 (congrArg Sum.inl h.symm)
        simp [dataHeap,transferResult,hs,ht]
      | inr a => rfl
  obtain ⟨hR,hC⟩ :=
      transfer_call mode (dataHeap S) (S (transferSource mode)) (S (transferTarget mode)) v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨_,hR,hC⟩

/-- The payload assignment obtained by emptying the stack selected by the drain mode. -/
def drainResult (mode : DrainMode) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update S (drainTarget mode) []

/-- The embedded drain routine produces `drainResult` on an arbitrary payload heap and returns
to the mode's return phase. Its stack-run clock is at most `L^2 + 3 * L + 3`, where `L` is
the initial target length. -/
theorem drain_data (mode : DrainMode) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.drain mode 0),v,dataHeap S⟩ =
        some ⟨some (.phase (drainReturn mode)),Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v none,dataHeap (drainResult mode S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.drain mode 0),v,dataHeap S⟩ ≤
        (S (drainTarget mode)).length^2+3*(S (drainTarget mode)).length+3 := by
  have hi := drainCode_injective mode
  have hsame : StackCall.frame (drainCode mode) (dataHeap S)
      (Normalization.singleStack (S (drainTarget mode)))=dataHeap S := by
    apply StackCall.frame_same _ _ _ hi
    intro key
    fin_cases key
    rfl
  have hfinal : StackCall.frame (drainCode mode) (dataHeap S)
      (Normalization.singleStack []) = dataHeap (drainResult mode S) := by
    apply frame_target _ _ _ _ hi
    · intro key
      fin_cases key
      simp [dataHeap,drainCode,drainResult,Normalization.singleStack]
    · intro bank hno
      cases bank with
      | inl p =>
        have ht : p≠drainTarget mode := fun h => hno 0 (congrArg Sum.inl h.symm)
        simp [dataHeap,drainResult,ht]
      | inr a => rfl
  obtain ⟨hR,hC⟩ := drain_call mode (dataHeap S) (S (drainTarget mode)) v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨_,hR,hC⟩
end Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- Replace the lookup stacks by the completed lookup state, preserving the table, clearing the
index, and prepending the reversed selected word to the output. -/
def lookupResult (values : List Bits) (index out : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits
  | .lookup k => ReadonlyTableGet.store (TableGet.stream values).reverse [] []
      ((values.getD (binaryValue index) []).reverse++out) k
  | p => S p

/-- From the specified lookup-stack encoding, the embedded lookup routine produces
`lookupResult` and reaches the lookup-copy entry. Its stack-run clock satisfies the stated
polynomial bound in the table, index, and output lengths. -/
theorem lookup_data (values : List Bits) (index out : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hp : ∀ k,S (.lookup k)=ReadonlyTableGet.store (TableGet.stream values).reverse [] index out k) :
    ∃ ticks last,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.lookup (.copy .emit)),v,dataHeap S⟩ =
        some ⟨some (.copy .lookup copyEntry),putLookup v last,dataHeap (lookupResult values index out S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.lookup (.copy .emit)),v,dataHeap S⟩ ≤
        30000*(1+(TableGet.stream values).length)*(1+(TableGet.stream values).length+index.length+out.length)^2 := by
  have hsame : StackCall.frame lookupCode (dataHeap S)
      (ReadonlyTableGet.store (TableGet.stream values).reverse [] index out)=dataHeap S := by
    apply StackCall.frame_same _ _ _ lookupCode_injective
    exact hp
  have hfinal : StackCall.frame lookupCode (dataHeap S)
      (ReadonlyTableGet.store (TableGet.stream values).reverse [] []
        ((values.getD (binaryValue index) []).reverse++out)) =
      dataHeap (lookupResult values index out S) := by
    apply frame_target _ _ _ _ lookupCode_injective
    · intro k
      rfl
    · intro bank hno
      cases bank with
      | inl p =>
        cases p with
        | lookup k => exact False.elim (hno k rfl)
        | _ => rfl
      | inr k => rfl
  obtain ⟨ticks,last,hR,hC⟩ := lookup_call (dataHeap S) values index out v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨ticks,last,hR,hC⟩

/-- The payload assignment obtained by clearing arithmetic stacks zero and one and placing the
reversed `bitAdd` result in stack two. -/
def addResult (x y : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update (Function.update (Function.update S (.arithmetic 0) []) (.arithmetic 1) [])
    (.arithmetic 2) (bitAdd x y).reverse

/-- With the two operands in arithmetic stacks zero and one and stack two empty, the embedded
addition routine produces `addResult`. It reaches the result-copy entry with stack-run clock
at most `addClockBound x y`. -/
theorem add_data (x y : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (h0 : S (.arithmetic 0)=x) (h1 : S (.arithmetic 1)=y) (h2 : S (.arithmetic 2)=[]) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.add .loop),putAdd v AddVar.init,dataHeap S⟩ =
        some ⟨some (.copy .result copyEntry),putAdd v (Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum.finalAddVar x y),dataHeap (addResult x y S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.add .loop),putAdd v AddVar.init,dataHeap S⟩ ≤ addClockBound x y := by
  have hsame : StackCall.frame addCode (dataHeap S) (addStacks x y [])=dataHeap S := by
    apply StackCall.frame_same _ _ _ addCode_injective
    intro i
    fin_cases i <;> simp [dataHeap,addCode,addStacks,h0,h1,h2]
  have hfinal : StackCall.frame addCode (dataHeap S) (addStacks [] [] (bitAdd x y).reverse) =
      dataHeap (addResult x y S) := by
    apply frame_target _ _ _ _ addCode_injective
    · intro i
      fin_cases i <;> simp [dataHeap,addResult,addCode,addStacks]
    · intro bank hno
      cases bank with
      | inl p =>
        have h0 : p≠.arithmetic 0 := fun h => hno 0 (congrArg Sum.inl h.symm)
        have h1 : p≠.arithmetic 1 := fun h => hno 1 (congrArg Sum.inl h.symm)
        have h2 : p≠.arithmetic 2 := fun h => hno 2 (congrArg Sum.inl h.symm)
        simp [dataHeap,addResult,h0,h1,h2]
      | inr a => rfl
  obtain ⟨hR,hC⟩ := add_call (dataHeap S) x y v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨_,hR,hC⟩

/-- Replace the arithmetic stacks by the completed multiplication layout containing `mulAcc x y
y.length` and the preserved reversed first operand. -/
def mulResult (x y : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits
  | .arithmetic i => mulStacks (mulAcc x y y.length) [] [] x.reverse [] [] i
  | p => S p

/-- From the specified initial multiplication layout, the embedded multiplication routine
produces `mulResult` and reaches the master-clearing phase. Its stack-run clock is at most
`31720 * (1 + x.length + y.length)^4`. -/
theorem mul_data (x y : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hp : ∀ i,S (.arithmetic i)=mulStacks [] [] [] x.reverse y.reverse [] i) :
    ∃ ticks,
      stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.multiply .outer),putMul v MulVar.init,dataHeap S⟩ =
        some ⟨some (.phase .clearMaster),putMul v MulVar.init,dataHeap (mulResult x y S)⟩ ∧
      stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks ⟨some (.multiply .outer),putMul v MulVar.init,dataHeap S⟩ ≤
        31720*(1+x.length+y.length)^4 := by
  have hsame : StackCall.frame mulCode (dataHeap S)
      (mulStacks [] [] [] x.reverse y.reverse [])=dataHeap S := by
    apply StackCall.frame_same _ _ _ mulCode_injective
    exact hp
  have hfinal : StackCall.frame mulCode (dataHeap S)
      (mulStacks (mulAcc x y y.length) [] [] x.reverse [] []) = dataHeap (mulResult x y S) := by
    apply frame_target _ _ _ _ mulCode_injective
    · intro i
      rfl
    · intro bank hno
      cases bank with
      | inl p =>
        cases p with
        | arithmetic i => exact False.elim (hno i rfl)
        | _ => rfl
      | inr k => rfl
  obtain ⟨hR,hC⟩ := mul_call (dataHeap S) x y v
  rw [hsame,hfinal] at hR
  rw [hsame] at hC
  exact ⟨_,hR,hC⟩
end Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine
