/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineKernel

/-!
# Rational stack-machine control and storage

The finite types `Payload`, `Label`, and `Local` specify the storage layout and control state of
the rational-arithmetic stack machine. The slot maps connect framed input, copying, table
lookup, addition, multiplication, transfer, and clearing routines to a common machine.

`phaseProgram` decodes instruction tags and schedules these routines, while `program` assembles
the complete transition program. This construction supplies an explicit classical computation
model for the arithmetic used in quantum algorithms; see [NielsenChuang2010].

## Main statements

* `program`: assembles the stack-machine transition program.
* `takeCode_injective`: ensures distinct framed-reader slots remain distinct in the machine.
* `mulCode_injective`: ensures distinct multiplication slots remain distinct in the machine.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

deriving instance Fintype for AddVar
deriving instance Fintype for MulVar

/-- Payload stack identifiers for program bits, values, output, framing, arithmetic registers,
and table lookup. -/
inductive Payload where
  | program | values | output | frame
  | arithmetic (index : Fin 6)
  | lookup (slot : ReadonlyTableGet.Slot)
  deriving DecidableEq, Fintype

/-- The machine's stack slots, combining payload stacks with the auxiliary slots of framed
reading and copying. -/
abbrev Slot := Payload ⊕ (FramedTake.Slot ⊕ FrameCopy.Slot)

/-- The payload slot holding the table stream used by the lookup routine. -/
def table : Payload := .lookup (.inl 0)
/-- The payload slot holding the index for table lookup. -/
def lookupIndex : Payload := .lookup (.inr .index)
/-- The payload slot holding the result of table lookup. -/
def lookupOutput : Payload := .lookup (.inr .output)

/-- Control phases for instruction decoding, arithmetic, storage, cleanup, and termination. -/
inductive Phase where
  | boot | firstBit | secondBit | thirdBit | dispatch
  | takeRight | afterOperands | afterLeft | reverseIndex | addStart | mulStart
  | copyResult | copyLookup | copyStore
  | clearResult | clearLookup | clearStore | clearMaster
  | reverseProduct | storeTransfer | finishTable | finishValues | halt
  deriving DecidableEq, Fintype
/-- The framed-read modes for the table, literals, indices, operands, and stored values. -/
inductive TakeMode where | table | literal | index | left | right | store deriving DecidableEq, Fintype
/-- The copying modes for arithmetic results, lookup results, and stored values. -/
inductive CopyMode where | result | lookup | store deriving DecidableEq, Fintype
/-- The transfer modes for addition operands, lookup indices, products, stored frames, and final
output. -/
inductive TransferMode where | addLeft | addRight | index | product | store | finish deriving DecidableEq, Fintype
/-- The clearing modes for result, lookup, store, multiplication-master, and table stacks. -/
inductive DrainMode where | result | lookup | store | master | table deriving DecidableEq, Fintype

/-- Control labels combining machine phases with labels of the called stack routines. -/
inductive Label where
  | phase (p : Phase)
  | take (mode : TakeMode) (l : FramedTake.Label)
  | copy (mode : CopyMode) (l : FrameCopy.Label)
  | lookup (l : ReadonlyTableGet.Label)
  | add (l : AddLabel)
  | multiply (l : MulLabel)
  | transfer (mode : TransferMode) (l : Fin 1)
  | drain (mode : DrainMode) (l : Fin 1)
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.phase .boot⟩

/-- The finite local state recording instruction bits, the arithmetic selector, and the states
of the called routines. -/
structure Local where
  io : Symbol
  first : Bool
  second : Bool
  third : Bool
  multiply : Bool
  takeState : FramedTake.Local
  copyState : Symbol
  lookupState : ReadonlyTableGet.Local
  addState : AddVar
  mulState : MulVar

/-- A product representation of the fields of `Local`, used to construct its finite enumeration. -/
private abbrev LocalProduct := Symbol × Bool × Bool × Bool × Bool × FramedTake.Local ×
  Symbol × ReadonlyTableGet.Local × AddVar × MulVar

/-- The equivalence between `Local` and the product of its component state types. -/
private def localEquiv : Local ≃ LocalProduct where
  toFun v := (v.io,v.first,v.second,v.third,v.multiply,v.takeState,v.copyState,v.lookupState,v.addState,v.mulState)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Local := Fintype.ofEquiv LocalProduct localEquiv.symm

/-- The initial local state, with empty symbol registers, false instruction bits, and
initialized arithmetic states. -/
def Local.init : Local :=
    ⟨none,false,false,false,false,default,none,default,AddVar.init,MulVar.init⟩
instance : Inhabited Local := ⟨Local.init⟩

/-- Read the machine's input/output symbol register. -/
def getIO (v : Local) : Symbol := v.io
/-- Replace the machine's input/output symbol register with `s`. -/
def putIO (v : Local) (s : Symbol) : Local := {v with io:=s}
/-- Read the local state of the framed-reader routine. -/
def getTake (v : Local) : FramedTake.Local := v.takeState
/-- Replace the local state of the framed-reader routine with `s`. -/
def putTake (v : Local) (s : FramedTake.Local) : Local := {v with takeState:=s}
/-- Read the symbol register of the frame-copy routine. -/
def getCopy (v : Local) : Symbol := v.copyState
/-- Replace the symbol register of the frame-copy routine with `s`. -/
def putCopy (v : Local) (s : Symbol) : Local := {v with copyState:=s}
/-- Read the local state of the table-lookup routine. -/
def getLookup (v : Local) : ReadonlyTableGet.Local := v.lookupState
/-- Replace the local state of the table-lookup routine with `s`. -/
def putLookup (v : Local) (s : ReadonlyTableGet.Local) : Local := {v with lookupState:=s}
/-- Read the local state of the addition routine. -/
def getAdd (v : Local) : AddVar := v.addState
/-- Replace the local state of the addition routine with `s`. -/
def putAdd (v : Local) (s : AddVar) : Local := {v with addState:=s}
/-- Read the local state of the multiplication routine. -/
def getMul (v : Local) : MulVar := v.mulState
/-- Replace the local state of the multiplication routine with `s`. -/
def putMul (v : Local) (s : MulVar) : Local := {v with mulState:=s}

/-- Select the source payload stack for a framed-read mode. -/
def takeSource : TakeMode → Payload | .left | .right | .store => .values | _ => .program
/-- Select the destination payload stack for a framed-read mode. -/
def takeTarget : TakeMode → Payload
  | .table => table | .literal | .store => .arithmetic 2
  | .index => .arithmetic 5 | .left => .arithmetic 4 | .right => .arithmetic 3

/-- Select the machine phase to resume after a framed read. -/
def takeReturn : TakeMode → Phase
  | .table => .firstBit | .literal => .copyResult | .index => .reverseIndex
  | .left => .takeRight | .right => .afterOperands | .store => .copyStore

/-- Map framed-reader slots into the machine's slots using the source and destination selected
by `mode`. -/
def takeCode (mode : TakeMode) : FramedTake.Slot → Slot
  | .reader => .inl (takeSource mode) | .output => .inl (takeTarget mode)
  | s => .inr (.inl s)

/-- Select the source payload stack for a copy mode. -/
def copySource : CopyMode → Payload | .lookup => lookupOutput | _ => .arithmetic 2
/-- Select the destination payload stack for a copy mode. -/
def copyTarget : CopyMode → Payload | .store => .frame | _ => .values
/-- Select the cleanup phase to resume after copying. -/
def copyReturn : CopyMode →
    Phase | .result => .clearResult | .lookup => .clearLookup | .store => .clearStore

/-- Map frame-copy slots into the machine's slots for the selected copy mode. -/
def copyCode (mode : CopyMode) : FrameCopy.Slot → Slot
  | .source => .inl (copySource mode) | .output => .inl (copyTarget mode)
  | s => .inr (.inr s)

/-- Select the source payload stack for a transfer mode. -/
def transferSource : TransferMode → Payload
  | .addLeft => .arithmetic 3 | .addRight => .arithmetic 4 | .product => .arithmetic 0
  | .index => .arithmetic 5 | .store => .frame | .finish => .values
/-- Select the destination payload stack for a transfer mode. -/
def transferTarget : TransferMode → Payload
  | .addLeft => .arithmetic 0 | .addRight => .arithmetic 1 | .product => .arithmetic 2
  | .index => lookupIndex | .store => table | .finish => .output
/-- Select the phase to resume after a transfer. -/
def transferReturn : TransferMode → Phase
  | .addLeft => .afterLeft | .addRight => .addStart | .product => .copyResult
  | .index => .copyLookup
  | .store => .firstBit | .finish => .halt

/-- Map the two transfer slots to the source and destination stacks selected by `mode`. -/
def transferCode (mode : TransferMode) : Fin 2 → Slot := fun i =>
  .inl (if i=0 then transferSource mode else transferTarget mode)

/-- Select the payload stack to clear in a drain mode. -/
def drainTarget : DrainMode → Payload
  | .lookup => lookupOutput | .master => .arithmetic 3 | .table => table | _ => .arithmetic 2
/-- Select the machine phase to resume after clearing a stack. -/
def drainReturn : DrainMode → Phase
  | .result | .lookup => .firstBit | .store => .storeTransfer
  | .master => .reverseProduct | .table => .finishValues

/-- Map the drain routine's single slot to the payload stack selected by `mode`. -/
def drainCode (mode : DrainMode) (_ : Fin 1) : Slot := .inl (drainTarget mode)
/-- Embed the three addition slots into the machine's arithmetic payload slots. -/
def addCode (i : Fin 3) : Slot := .inl (.arithmetic (Fin.castLE (by decide) i))
/-- Embed the six multiplication slots into the machine's arithmetic payload slots. -/
def mulCode (i : Fin 6) : Slot := .inl (.arithmetic i)
/-- Embed the lookup routine's slots into the machine's lookup payload slots. -/
def lookupCode (s : ReadonlyTableGet.Slot) : Slot := .inl (.lookup s)

/-- The entry label for reading a unary-framed bit word. -/
def takeEntry : FramedTake.Label := .read (.read .unary)
/-- The entry label for emitting a framed copy of a bit word. -/
def copyEntry : FrameCopy.Label := .copy false .emit

/-- The control statement for each machine phase, including tag decoding, routine dispatch,
cleanup, and halting. -/
def phaseProgram : Phase → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .boot => .goto (fun _ => .take .table takeEntry)
  | .firstBit => .pop (.inl .program) putIO
      (.branch (fun v => v.io.isSome)
        (.load (fun v => {v with first:=v.io.getD false}) (.goto (fun _ => .phase .secondBit)))
        (.goto (fun _ => .phase .finishTable)))
  | .secondBit => .pop (.inl .program) putIO
      (.branch (fun v => v.io.isSome)
        (.load (fun v => {v with second:=v.io.getD false}) (.goto (fun _ => .phase .thirdBit))) .halt)
  | .thirdBit => .pop (.inl .program) putIO
      (.branch (fun v => v.io.isSome)
        (.load (fun v => {v with third:=v.io.getD false}) (.goto (fun _ => .phase .dispatch))) .halt)
  | .dispatch =>
      .branch (fun v => v.first)
        (.branch (fun v => v.second || v.third) .halt (.goto (fun _ => .take .store takeEntry)))
        (.branch (fun v => v.second)
          (.load (fun v => {v with multiply:=v.third}) (.goto (fun _ => .take .left takeEntry)))
          (.branch (fun v => v.third) (.goto (fun _ => .take .index takeEntry))
            (.goto (fun _ => .take .literal takeEntry))))
  | .takeRight => .goto (fun _ => .take .right takeEntry)
  | .afterOperands => .branch (fun v => v.multiply)
      (.goto (fun _ => .phase .mulStart)) (.goto (fun _ => .transfer .addLeft 0))
  | .afterLeft => .goto (fun _ => .transfer .addRight 0)
  | .reverseIndex => .goto (fun _ => .transfer .index 0)
  | .addStart => .load (fun v => putAdd v AddVar.init) (.goto (fun _ => .add .loop))
  | .mulStart => .load (fun v => putMul v MulVar.init) (.goto (fun _ => .multiply .outer))
  | .copyResult => .goto (fun _ => .copy .result copyEntry)
  | .copyLookup => .goto (fun _ => .lookup (.copy .emit))
  | .copyStore => .goto (fun _ => .copy .store copyEntry)
  | .clearResult => .goto (fun _ => .drain .result 0)
  | .clearLookup => .goto (fun _ => .drain .lookup 0)
  | .clearStore => .goto (fun _ => .drain .store 0)
  | .clearMaster => .goto (fun _ => .drain .master 0)
  | .reverseProduct => .goto (fun _ => .transfer .product 0)
  | .storeTransfer => .goto (fun _ => .transfer .store 0)
  | .finishTable => .goto (fun _ => .drain .table 0)
  | .finishValues => .goto (fun _ => .transfer .finish 0)
  | .halt => .halt

/-- The stack-machine program obtained by combining phase control with the embedded arithmetic
and data-handling routines. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .phase p => phaseProgram p
  | .take mode l => StackCall.stmt (takeCode mode) (Label.take mode) (.phase (takeReturn mode)) getTake putTake (FramedTake.program l)
  | .copy mode l => StackCall.stmt (copyCode mode) (Label.copy mode) (.phase (copyReturn mode)) getCopy putCopy (FrameCopy.program l)
  | .lookup l => StackCall.stmt lookupCode Label.lookup (.copy .lookup copyEntry) getLookup putLookup (ReadonlyTableGet.program l)
  | .add l => StackCall.stmt addCode Label.add (.copy .result copyEntry) getAdd putAdd (addProgram l)
  | .multiply l => StackCall.stmt mulCode Label.multiply (.phase .clearMaster) getMul putMul (mulProgram l)
  | .transfer mode l => StackCall.stmt (transferCode mode) (Label.transfer mode) (.phase (transferReturn mode)) getIO putIO (transferProgram l)
  | .drain mode l => StackCall.stmt (drainCode mode) (Label.drain mode) (.phase (drainReturn mode)) getIO putIO (Normalization.drainProgram l)

end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Machine
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- The framed-reader slot map is injective for every read mode. -/
theorem takeCode_injective (mode : TakeMode) : Function.Injective (takeCode mode) := by
  intro a b h
  cases mode <;> cases a <;> cases b <;>
    simp [takeCode,takeSource,takeTarget,table] at h ⊢

/-- The frame-copy slot map is injective for every copy mode. -/
theorem copyCode_injective (mode : CopyMode) : Function.Injective (copyCode mode) := by
  intro a b h
  cases mode <;> cases a <;> cases b <;>
    simp [copyCode,copySource,copyTarget,lookupOutput] at h ⊢

/-- The transfer slot map is injective for every transfer mode. -/
theorem transferCode_injective (mode : TransferMode) : Function.Injective (transferCode mode) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> cases mode <;>
    simp [transferCode,transferSource,transferTarget,table,lookupIndex] at h ⊢

/-- The drain slot map is injective for every drain mode. -/
theorem drainCode_injective (mode : DrainMode) : Function.Injective (drainCode mode) := by
  intro a b _
  exact Subsingleton.elim a b

/-- The addition slot map is injective. -/
theorem addCode_injective : Function.Injective addCode := by
  intro a b h
  have hv := congrArg (fun z : Slot => match z with | .inl (.arithmetic i) => i.val | _ => 0) h
  exact Fin.ext hv

/-- The multiplication slot map is injective. -/
theorem mulCode_injective : Function.Injective mulCode := by
  intro a b h
  exact Payload.arithmetic.inj (Sum.inl.inj h)

/-- The lookup slot map is injective. -/
theorem lookupCode_injective : Function.Injective lookupCode := by
  intro a b h
  exact Payload.lookup.inj (Sum.inl.inj h)
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Machine
