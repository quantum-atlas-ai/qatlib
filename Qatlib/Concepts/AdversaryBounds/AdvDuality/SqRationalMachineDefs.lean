/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineKernel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

inductive Payload where
  | program | values | output | frame
  | arithmetic (index : Fin 6)
  | lookup (slot : ReadonlyTableGet.Slot)
  deriving DecidableEq, Fintype

abbrev Slot := Payload ⊕ (FramedTake.Slot ⊕ FrameCopy.Slot)

def table : Payload := .lookup (.inl 0)
def lookupIndex : Payload := .lookup (.inr .index)
def lookupOutput : Payload := .lookup (.inr .output)

inductive Phase where
  | boot | firstBit | secondBit | thirdBit | dispatch
  | takeRight | afterOperands | afterLeft | reverseIndex | addStart | mulStart
  | copyResult | copyLookup | copyStore
  | clearResult | clearLookup | clearStore | clearMaster
  | reverseProduct | storeTransfer | finishTable | finishValues | halt
  deriving DecidableEq, Fintype
inductive TakeMode where | table | literal | index | left | right | store deriving DecidableEq, Fintype
inductive CopyMode where | result | lookup | store deriving DecidableEq, Fintype
inductive TransferMode where | addLeft | addRight | index | product | store | finish deriving DecidableEq, Fintype
inductive DrainMode where | result | lookup | store | master | table deriving DecidableEq, Fintype

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

private abbrev LocalProduct := Symbol × Bool × Bool × Bool × Bool × FramedTake.Local ×
  Symbol × ReadonlyTableGet.Local × AddVar × MulVar

private def localEquiv : Local ≃ LocalProduct where
  toFun v := (v.io,v.first,v.second,v.third,v.multiply,v.takeState,v.copyState,v.lookupState,v.addState,v.mulState)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Local := Fintype.ofEquiv LocalProduct localEquiv.symm

def Local.init : Local :=
    ⟨none,false,false,false,false,default,none,default,AddVar.init,MulVar.init⟩
instance : Inhabited Local := ⟨Local.init⟩

def getIO (v : Local) : Symbol := v.io
def putIO (v : Local) (s : Symbol) : Local := {v with io:=s}
def getTake (v : Local) : FramedTake.Local := v.takeState
def putTake (v : Local) (s : FramedTake.Local) : Local := {v with takeState:=s}
def getCopy (v : Local) : Symbol := v.copyState
def putCopy (v : Local) (s : Symbol) : Local := {v with copyState:=s}
def getLookup (v : Local) : ReadonlyTableGet.Local := v.lookupState
def putLookup (v : Local) (s : ReadonlyTableGet.Local) : Local := {v with lookupState:=s}
def getAdd (v : Local) : AddVar := v.addState
def putAdd (v : Local) (s : AddVar) : Local := {v with addState:=s}
def getMul (v : Local) : MulVar := v.mulState
def putMul (v : Local) (s : MulVar) : Local := {v with mulState:=s}

def takeSource : TakeMode → Payload | .left | .right | .store => .values | _ => .program
def takeTarget : TakeMode → Payload
  | .table => table | .literal | .store => .arithmetic 2
  | .index => .arithmetic 5 | .left => .arithmetic 4 | .right => .arithmetic 3

def takeReturn : TakeMode → Phase
  | .table => .firstBit | .literal => .copyResult | .index => .reverseIndex
  | .left => .takeRight | .right => .afterOperands | .store => .copyStore

def takeCode (mode : TakeMode) : FramedTake.Slot → Slot
  | .reader => .inl (takeSource mode) | .output => .inl (takeTarget mode)
  | s => .inr (.inl s)

def copySource : CopyMode → Payload | .lookup => lookupOutput | _ => .arithmetic 2
def copyTarget : CopyMode → Payload | .store => .frame | _ => .values
def copyReturn : CopyMode →
    Phase | .result => .clearResult | .lookup => .clearLookup | .store => .clearStore

def copyCode (mode : CopyMode) : FrameCopy.Slot → Slot
  | .source => .inl (copySource mode) | .output => .inl (copyTarget mode)
  | s => .inr (.inr s)

def transferSource : TransferMode → Payload
  | .addLeft => .arithmetic 3 | .addRight => .arithmetic 4 | .product => .arithmetic 0
  | .index => .arithmetic 5 | .store => .frame | .finish => .values
def transferTarget : TransferMode → Payload
  | .addLeft => .arithmetic 0 | .addRight => .arithmetic 1 | .product => .arithmetic 2
  | .index => lookupIndex | .store => table | .finish => .output
def transferReturn : TransferMode → Phase
  | .addLeft => .afterLeft | .addRight => .addStart | .product => .copyResult
  | .index => .copyLookup
  | .store => .firstBit | .finish => .halt

def transferCode (mode : TransferMode) : Fin 2 → Slot := fun i =>
  .inl (if i=0 then transferSource mode else transferTarget mode)

def drainTarget : DrainMode → Payload
  | .lookup => lookupOutput | .master => .arithmetic 3 | .table => table | _ => .arithmetic 2
def drainReturn : DrainMode → Phase
  | .result | .lookup => .firstBit | .store => .storeTransfer
  | .master => .reverseProduct | .table => .finishValues

def drainCode (mode : DrainMode) (_ : Fin 1) : Slot := .inl (drainTarget mode)
def addCode (i : Fin 3) : Slot := .inl (.arithmetic (Fin.castLE (by decide) i))
def mulCode (i : Fin 6) : Slot := .inl (.arithmetic i)
def lookupCode (s : ReadonlyTableGet.Slot) : Slot := .inl (.lookup s)

def takeEntry : FramedTake.Label := .read (.read .unary)
def copyEntry : FrameCopy.Label := .copy false .emit

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

theorem takeCode_injective (mode : TakeMode) : Function.Injective (takeCode mode) := by
  intro a b h
  cases mode <;> cases a <;> cases b <;>
    simp [takeCode,takeSource,takeTarget,table] at h ⊢

theorem copyCode_injective (mode : CopyMode) : Function.Injective (copyCode mode) := by
  intro a b h
  cases mode <;> cases a <;> cases b <;>
    simp [copyCode,copySource,copyTarget,lookupOutput] at h ⊢

theorem transferCode_injective (mode : TransferMode) : Function.Injective (transferCode mode) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> cases mode <;>
    simp [transferCode,transferSource,transferTarget,table,lookupIndex] at h ⊢

theorem drainCode_injective (mode : DrainMode) : Function.Injective (drainCode mode) := by
  intro a b _
  exact Subsingleton.elim a b

theorem addCode_injective : Function.Injective addCode := by
  intro a b h
  have hv := congrArg (fun z : Slot => match z with | .inl (.arithmetic i) => i.val | _ => 0) h
  exact Fin.ext hv

theorem mulCode_injective : Function.Injective mulCode := by
  intro a b h
  exact Payload.arithmetic.inj (Sum.inl.inj h)

theorem lookupCode_injective : Function.Injective lookupCode := by
  intro a b h
  exact Payload.lookup.inj (Sum.inl.inj h)
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Machine
