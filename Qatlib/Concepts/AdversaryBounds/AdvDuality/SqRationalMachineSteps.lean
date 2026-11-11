/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCalls

/-!
# Execution of rational stack-machine instructions

This module proves execution rules for decoding and running the arithmetic machine's
instructions on encoded word states. The rules cover literals, parameter lookup, addition,
multiplication, storage, initialization, and final output, each with an explicit budget.

`PathExecution` tracks total clock and maximum clock separately, allowing `program_execution` to
compose successful instruction semantics into a machine execution. These constructions implement
elementary classical arithmetic in the computation setting of [NielsenChuang2010].

## Main statements

* `instruction_execution`: realizes each successful word-level instruction execution.
* `PathExecution.trans`: adds total-clock bounds and takes the maximum of peak bounds.
* `program_execution`: realizes a successful list of instructions with compositional cost
  bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

set_option autoImplicit false
set_option maxHeartbeats 2500000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.AdversaryBounds.AdvDuality.Machine
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open scoped Classical

/-- Configurations of the rational-arithmetic machine with Boolean stack symbols. -/
abbrev Config :=
    TM2.Cfg (fun _ : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot => Bool) Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local

/-- Construct an active machine configuration from a control label, local state, and payload
data, with auxiliary stacks initialized by `dataHeap`. -/
def cfg (l : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) : Config :=
  ⟨some l,v,dataHeap S⟩

/-- Update the local state with three parsed instruction bits, storing the third bit in the
input/output register. -/
def parsed (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) (a b c : Bool) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local :=
  {v with io:=some c,first:=a,second:=b,third:=c}

/-- Updating a payload slot in `dataHeap S` agrees with applying `dataHeap` after the
corresponding update to `S`. -/
@[simp] theorem dataHeap_update (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (p : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload) (bits : Bits) :
    Function.update (dataHeap S) (.inl p) bits = dataHeap (Function.update S p bits) := by
  funext k
  by_cases h : k=(.inl p : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot)
  · subst k
    simp only [Function.update_self,dataHeap]
  · rw [Function.update_of_ne h]
    cases k with
    | inl q =>
      have hn : q≠p := fun hq => h (congrArg Sum.inl hq)
      simp only [dataHeap,Function.update_of_ne hn]
    | inr k => rfl

/-- Three machine ticks consume the three instruction-tag bits and reach the dispatch phase with
the corresponding parsed local state. -/
theorem parse_run (a b c : Bool) (tail : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program 3 (cfg (.phase .firstBit) v (Function.update S .program (a::b::c::tail))) =
      some (cfg (.phase .dispatch) (parsed v a b c) (Function.update S .program tail)) := by
  simp [stackRun,cfg,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,TM2.step,TM2.stepAux,dataHeap,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO,parsed]

/-- The three-tick instruction-tag parser has total clock `6 * tail.length + 18`. -/
theorem parse_clock (a b c : Bool) (tail : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program 3 (cfg (.phase .firstBit) v (Function.update S .program (a::b::c::tail))) =
      6*tail.length+18 := by
  simp [stackRunClock,cfg,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,TM2.step,TM2.stepAux,dataHeap,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO,stackClock]
  omega

/-- A phase transition with zero stack clock gives an `Execution` with budget one. -/
theorem control (p : Phase) (l : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Label) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v w : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hr : TM2.step Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase p) v S)=some (cfg l w S))
    (hc : stackClock (phaseProgram p) v (dataHeap S)=0) :
    Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase p) v S) (cfg l w S) 1 := by
  refine ⟨1,?_,?_⟩
  · simpa only [run_one] using! hr
  · simp [stackRunClock,cfg,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,hc]

/-- Encode the remaining program, value stack, and reversed parameter-table stream as payload
stacks, leaving other payload stacks empty. -/
def wordData (code : Bits) (ps values : List Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits
  | .program => code
  | .values => valueStack values
  | .lookup k => ReadonlyTableGet.store (TableGet.stream ps).reverse [] [] [] k
  | _ => []

/-- The clock budget for copying an arithmetic result onto the value stack and clearing its
temporary stack. -/
def resultBudget (bits values : Bits) : ℕ :=
  1+10000*(1+bits.length+values.length)^3+1+(bits.length^2+3*bits.length+3)

/-- An arithmetic result stored in reverse order can be copied and cleared, returning to
instruction parsing within `resultBudget`. -/
theorem finish_result (bits : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hr : S (.arithmetic 2)=bits.reverse) :
    ∃ last, Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .copyResult) v S)
      (cfg (.phase .firstBit) last (drainResult .result (copyResult .result bits S)))
      (resultBudget bits (S .values)) := by
  have h0 := control .copyResult (.copy .result copyEntry) S v v rfl rfl
  obtain ⟨n,hR,hC⟩ := copy_data .result bits S v hr
  have h1 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.copy .result copyEntry) v S)
      (cfg (.phase .clearResult) (putCopy v none) (copyResult .result bits S))
      (10000*(1+bits.length+(S .values).length)^3) := ⟨n,hR,hC⟩
  have h2 := control .clearResult (.drain .result 0)
    (copyResult .result bits S) (putCopy v none) (putCopy v none) rfl rfl
  obtain ⟨m,hD,hB⟩ := drain_data .result (copyResult .result bits S) (putCopy v none)
  have h3 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.drain .result 0) (putCopy v none) (copyResult .result bits S))
      (cfg (.phase .firstBit) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (putCopy v none) none) (drainResult .result (copyResult .result bits S)))
      (bits.length^2+3*bits.length+3) := by
    refine ⟨m,hD,?_⟩
    simpa [drainTarget,copyResult,copyTarget,hr] using! hB
  refine ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (putCopy v none) none,?_⟩
  exact ((h0.trans h1).trans h2).trans h3

/-- The clock budget for parsing, reading, and pushing a literal bit word. -/
def literalBudget (bits tail : Bits) (stack : List Bits) : ℕ :=
  6*(framed bits++tail).length+18+1+
    5000*(bits.length+1)*(1+(framed bits++tail).length)^2+
    resultBudget bits (valueStack stack)

/-- A literal instruction consumes its code and pushes `bits` onto the value stack within
`literalBudget`, preserving the parameter table. -/
theorem literal_execution (bits tail : Bits) (ps stack : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .firstBit) v
      (wordData (Instruction.code (.literal bits)++tail) ps stack))
      (cfg (.phase .firstBit) last (wordData tail ps (bits::stack)))
      (literalBudget bits tail stack) := by
  let S := wordData (Instruction.code (.literal bits)++tail) ps stack
  let P := Function.update S .program (framed bits++tail)
  let T := takeResult .literal bits tail P
  let v0 := parsed v false false false
  have hS : Function.update S .program (false::false::false::(framed bits++tail))=S := by
    funext p
    cases p <;> rfl
  have h0 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .firstBit) v S)
      (cfg (.phase .dispatch) v0 P) (6*(framed bits++tail).length+18) := by
    refine ⟨3,?_,?_⟩
    · simpa only [hS] using! parse_run false false false (framed bits++tail) S v
    · simpa only [hS] using! (parse_clock false false false (framed bits++tail) S v).le
  have h1 := control .dispatch (.take .literal takeEntry) P v0 v0 rfl rfl
  obtain ⟨n,last,hR,hC⟩ := take_data .literal bits tail P v0 (by simp [P,takeSource])
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .literal takeEntry) v0 P)
      (cfg (.phase .copyResult) (putTake v0 last) T)
      (5000*(bits.length+1)*(1+(framed bits++tail).length)^2) := by
    refine ⟨n,hR,?_⟩
    simpa [P,S,wordData,takeTarget] using! hC
  obtain ⟨last',h3⟩ := finish_result bits T (putTake v0 last)
    (by simp [T,takeResult,takeTarget,P,S,wordData])
  have hf : drainResult .result (copyResult .result bits T)=wordData tail ps (bits::stack) := by
    funext p
    cases p <;> (try rename_i i; fin_cases i) <;>
      simp [drainResult,drainTarget,copyResult,copyTarget,T,takeResult,takeSource,takeTarget,P,S,
        wordData,valueStack]
  rw [hf] at h3
  refine ⟨last',?_⟩
  have hh := ((h0.trans h1).trans h2).trans h3
  simpa [literalBudget,resultBudget,T,takeResult,takeSource,takeTarget,P,S,wordData] using! hh

/-- The clock budget for clearing the parameter table and transferring the value stack to final
output. -/
def finishBudget (ps values : List Bits) : ℕ :=
  3+1+((TableGet.stream ps).length^2+3*(TableGet.stream ps).length+3)+1+
    ((valueStack values).length*(2*(valueStack values).length+5)+3)+1

/-- An empty remaining program halts with all stacks empty except the reversed encoded value
stack in the output slot, within `finishBudget`. -/
theorem finish_execution (ps stack : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .firstBit) v (wordData [] ps stack))
      ⟨none,last,Function.update (fun _ => []) (.inl .output) (valueStack stack).reverse⟩
      (finishBudget ps stack) := by
  let S := wordData [] ps stack
  let T := drainResult .table S
  let U := transferResult .finish T
  let v0 := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v none
  have hs : Function.update S .program []=S := by
    funext p
    cases p <;> rfl
  have h0 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .firstBit) v S)
      (cfg (.phase .finishTable) v0 S) 3 := by
    refine ⟨1,?_,?_⟩
    · simp [run_one,cfg,TM2.step,TM2.stepAux,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,dataHeap_update,
        show dataHeap S
            (.inl .program)=[] from rfl,hs,v0,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO]
    · simp [stackRunClock,cfg,TM2.step,TM2.stepAux,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,dataHeap,
        S,wordData,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO,stackClock]
  have h1 := control .finishTable (.drain .table 0) S v0 v0 rfl rfl
  obtain ⟨n,hR,hC⟩ := drain_data .table S v0
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.drain .table 0) v0 S)
      (cfg (.phase .finishValues) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none) T)
      ((TableGet.stream ps).length^2+3*(TableGet.stream ps).length+3) := by
    refine ⟨n,hR,?_⟩
    simpa [S,wordData,drainTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,ReadonlyTableGet.store] using! hC
  have h3 :=
      control .finishValues (.transfer .finish 0) T
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none)
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none) rfl rfl
  obtain ⟨m,hD,hB⟩ :=
      transfer_data .finish T
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none)
  have h4 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .finish 0) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none) T)
      (cfg (.phase .halt) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none) none) U)
      ((valueStack stack).length*(2*(valueStack stack).length+5)+3) := by
    refine ⟨m,hD,?_⟩
    simpa [T,drainResult,drainTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,S,wordData,transferSource,transferTarget] using! hB
  let vf :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none) none
  have h5 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .halt) vf U) ⟨none,vf,dataHeap U⟩ 1 := by
    refine ⟨1,?_,?_⟩
    · rfl
    · rfl
  have hf : dataHeap U=Function.update (fun _ => []) (.inl .output) (valueStack stack).reverse := by
    funext k
    cases k with
    | inl p =>
      cases p with
      | lookup k =>
        cases k with
        | inl k => fin_cases k <;>
            simp [dataHeap,U,transferResult,transferSource,transferTarget,T,drainResult,drainTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,
              S,wordData,ReadonlyTableGet.store]
        | inr k => cases k <;>
            simp [dataHeap,U,transferResult,transferSource,transferTarget,T,drainResult,drainTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,
              S,wordData,ReadonlyTableGet.store,TableGet.store]
      | _ => simp [dataHeap,U,transferResult,transferSource,transferTarget,T,drainResult,drainTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,
          S,wordData]
    | inr k => simp [dataHeap]
  have hh := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  rw [hf] at hh
  exact ⟨vf,hh⟩

/-- The reversed input encoding of the framed parameter-table stream followed by the program
code. -/
def inputCode (ps : List Bits) (code : Bits) : Bits :=
  (framed (TableGet.stream ps)++code).reverse

/-- The clock budget for reading the initial parameter table and reaching the first instruction. -/
def bootBudget (ps : List Bits) (code : Bits) : ℕ :=
  1+5000*((TableGet.stream ps).length+1)*(1+(framed (TableGet.stream ps)++code).length)^2

/-- The machine initialized with reversed `inputCode ps code` reaches the first parsing phase
with program `code`, parameters `ps`, and an empty value stack within `bootBudget`. -/
theorem boot_execution (ps : List Bits) (code : Bits) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (TM2.init (.inl .program) (inputCode ps code).reverse)
      (cfg (.phase .firstBit) last (wordData code ps [])) (bootBudget ps code) := by
  let S := wordData (framed (TableGet.stream ps)++code) [] []
  let T := takeResult .table (TableGet.stream ps) code S
  have hi : (TM2.init (.inl .program) (inputCode ps code).reverse : Config)=
      cfg (.phase .boot) Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init S := by
    simp only [TM2.init,inputCode,List.reverse_reverse,cfg]
    congr 1
    funext k
    cases k with
    | inl p =>
      cases p with
      | lookup k =>
        cases k with
        | inl k => fin_cases k <;> simp [dataHeap,S,wordData,ReadonlyTableGet.store,TableGet.stream]
        | inr k => cases k <;> simp [dataHeap,S,wordData,ReadonlyTableGet.store,TableGet.store]
      | _ => simp [dataHeap,S,wordData,valueStack]
    | inr k => simp [dataHeap]
  have h0 :=
      control .boot
      (.take .table takeEntry) S Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init rfl rfl
  obtain ⟨n,last,hR,hC⟩ :=
      take_data .table
      (TableGet.stream ps) code S Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init rfl
  have h1 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .table takeEntry) Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init S)
      (cfg (.phase .firstBit) (putTake Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init last) T)
      (5000*((TableGet.stream ps).length+1)*(1+(framed (TableGet.stream ps)++code).length)^2) := by
    refine ⟨n,hR,?_⟩
    simpa [S,wordData,takeTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,ReadonlyTableGet.store] using! hC
  have hf : T=wordData code ps [] := by
    funext p
    cases p with
    | lookup k =>
      cases k with
      | inl k => fin_cases k <;>
          simp [T,takeResult,takeSource,takeTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,S,wordData,ReadonlyTableGet.store,TableGet.stream]
      | inr k => cases k <;>
          simp [T,takeResult,takeSource,takeTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,S,wordData,ReadonlyTableGet.store,TableGet.store]
    | _ => simp [T,takeResult,takeSource,takeTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,S,wordData]
  rw [hf] at h1
  rw [hi]
  exact ⟨putTake Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local.init last,h0.trans h1⟩

/-- Associate each copy mode with the drain mode that clears its temporary source. -/
def copyDrain : CopyMode → DrainMode | .result => .result | .lookup => .lookup | .store => .store

/-- The combined clock budget for copying a bit word and clearing its temporary source stack. -/
def copyDrainBudget (bits out : Bits) : ℕ :=
  10000*(1+bits.length+out.length)^3+1+(bits.length^2+3*bits.length+3)

/-- A copy followed by its associated drain reaches the corresponding return phase with the
specified payload update within `copyDrainBudget`. -/
theorem finish_copy (mode : CopyMode) (bits : Bits) (S : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (hr : S (copySource mode)=bits.reverse) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.copy mode copyEntry) v S)
      (cfg (.phase (drainReturn (copyDrain mode))) last
        (drainResult (copyDrain mode) (copyResult mode bits S)))
      (copyDrainBudget bits (S (copyTarget mode))) := by
  obtain ⟨n,hR,hC⟩ := copy_data mode bits S v hr
  have h0 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.copy mode copyEntry) v S)
      (cfg (.phase (copyReturn mode)) (putCopy v none) (copyResult mode bits S))
      (10000*(1+bits.length+(S (copyTarget mode)).length)^3) := ⟨n,hR,hC⟩
  have h1 := control (copyReturn mode) (.drain (copyDrain mode) 0)
    (copyResult mode bits S) (putCopy v none) (putCopy v none)
    (by cases mode <;> rfl) (by cases mode <;> rfl)
  obtain ⟨m,hD,hB⟩ := drain_data (copyDrain mode) (copyResult mode bits S) (putCopy v none)
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.drain (copyDrain mode) 0) (putCopy v none) (copyResult mode bits S))
      (cfg (.phase (drainReturn (copyDrain mode))) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (putCopy v none) none)
        (drainResult (copyDrain mode) (copyResult mode bits S)))
      (bits.length^2+3*bits.length+3) := by
    refine ⟨m,hD,?_⟩
    cases mode <;>
      simp [copyDrain,drainTarget,copyResult,copyTarget,copySource,lookupOutput] at hr hB ⊢
    all_goals simpa [hr] using! hB
  exact ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (putCopy v none) none,(h0.trans h1).trans h2⟩

/-- Existence of a machine run between two configurations with separate bounds on total clock
and maximum clock. -/
def PathExecution (first last : Config) (time peak : ℕ) : Prop :=
  ∃ ticks,stackRun Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks first=some last ∧
    stackRunClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks first≤time ∧ stackRunMaxClock Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program ticks first≤peak

/-- An `Execution` with budget `budget` yields a `PathExecution` with both clock bounds equal to
`budget`. -/
theorem path_of_execution {first last : Config} {budget : ℕ}
    (h : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program first last budget) : PathExecution first last budget budget := by
  obtain ⟨n,hr,hc⟩ := h
  exact ⟨n,hr,hc,(maxClock_le_clock _ _ _).trans hc⟩

/-- Compose two path executions by adding their total-clock bounds and taking the maximum of
their maximum-clock bounds. -/
theorem PathExecution.trans {first mid last : Config} {a b p q : ℕ}
    (h : PathExecution first mid a p) (g : PathExecution mid last b q) :
    PathExecution first last (a+b) (max p q) := by
  obtain ⟨n,hr,hc,hp⟩ := h
  obtain ⟨m,gr,gc,gp⟩ := g
  refine ⟨n+m,?_,?_,?_⟩
  · rw [run_add,hr,Option.bind_some,gr]
  · rw [clock_add _ _ _ _ _ hr]
    exact Nat.add_le_add hc gc
  · rw [maxClock_add _ _ _ _ _ hr]
    exact max_le_max hp gp

/-- Updating the program component of `wordData` replaces its code while preserving the
parameter and value encodings. -/
@[simp] theorem wordData_update (code code' : Bits) (ps values : List Bits) :
    Function.update (wordData code ps values) .program code'=wordData code' ps values := by
  funext p
  cases p <;> rfl

/-- The three instruction-tag bits are parsed into the dispatch state within budget `6 *
tail.length + 18`. -/
theorem parse_execution (a b c : Bool) (tail : Bits) (ps values : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.phase .firstBit) v (wordData (a::b::c::tail) ps values))
      (cfg (.phase .dispatch) (parsed v a b c) (wordData tail ps values))
      (6*tail.length+18) := by
  refine ⟨3,?_,?_⟩
  · simpa only [wordData_update] using! parse_run a b c tail (wordData tail ps values) v
  · simpa only [wordData_update] using! (parse_clock a b c tail (wordData tail ps values) v).le

/-- The clock budget for reading, framing, clearing, and appending a stored value to the
parameter table. -/
def storeBudget (bits tail : Bits) (ps rest : List Bits) : ℕ :=
  6*tail.length+18+1+
    5000*(bits.length+1)*(1+(framed bits++valueStack rest).length)^2+1+
    copyDrainBudget bits []+1+
    ((framed bits).length*(2*((framed bits).length+(TableGet.stream ps).length)+5)+3)

/-- A store instruction removes the top value and appends it to the parameter list, returning to
parsing within `storeBudget`. -/
theorem store_execution (bits tail : Bits) (ps rest : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (Instruction.code .store++tail) ps (bits::rest)))
      (cfg (.phase .firstBit) last (wordData tail (ps++[bits]) rest))
      (storeBudget bits tail ps rest) := by
  let P := wordData tail ps (bits::rest)
  let T := takeResult .store bits (valueStack rest) P
  let U := drainResult .store (copyResult .store bits T)
  let V := transferResult .store U
  let v0 := parsed v true false false
  have h0 := parse_execution true false false tail ps (bits::rest) v
  have h1 := control .dispatch (.take .store takeEntry) P v0 v0 rfl rfl
  obtain ⟨n,last,hR,hC⟩ := take_data .store bits (valueStack rest) P v0
    (by simp [P,wordData,takeSource,valueStack])
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .store takeEntry) v0 P)
      (cfg (.phase .copyStore) (putTake v0 last) T)
      (5000*(bits.length+1)*(1+(framed bits++valueStack rest).length)^2) := by
    refine ⟨n,hR,?_⟩
    simpa [P,wordData,takeTarget] using! hC
  have h3 :=
      control .copyStore (.copy .store copyEntry) T (putTake v0 last) (putTake v0 last) rfl rfl
  obtain ⟨last',h4⟩ := finish_copy .store bits T (putTake v0 last)
    (by simp [copySource,T,takeResult,takeTarget,P,wordData])
  have h5 := control .storeTransfer (.transfer .store 0) U last' last' rfl rfl
  obtain ⟨m,hD,hB⟩ := transfer_data .store U last'
  have h6 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .store 0) last' U)
      (cfg (.phase .firstBit) (Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO last' none) V)
      ((framed bits).length*(2*((framed bits).length+(TableGet.stream ps).length)+5)+3) := by
    refine ⟨m,hD,?_⟩
    simpa [U,drainResult,drainTarget,copyResult,copyTarget,T,takeResult,takeSource,takeTarget,
      P,wordData,transferSource,transferTarget,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,ReadonlyTableGet.store] using! hB
  have hf : V=wordData tail (ps++[bits]) rest := by
    funext p
    cases p with
    | arithmetic i => fin_cases i <;>
        simp [V,transferResult,transferSource,transferTarget,U,drainResult,drainTarget,
          copyResult,copyTarget,T,takeResult,takeSource,takeTarget,P,wordData,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table]
    | lookup k =>
      cases k with
      | inl k => fin_cases k <;>
          simp [V,transferResult,transferSource,transferTarget,U,drainResult,drainTarget,
            copyResult,copyTarget,T,takeResult,takeSource,takeTarget,P,wordData,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,
            ReadonlyTableGet.store,TableGet.stream,List.reverse_append]
      | inr k => cases k <;>
          simp [V,transferResult,transferSource,transferTarget,U,drainResult,drainTarget,
            copyResult,copyTarget,T,takeResult,takeSource,takeTarget,P,wordData,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,
            ReadonlyTableGet.store,TableGet.store]
    | _ => simp [V,transferResult,transferSource,transferTarget,U,drainResult,drainTarget,
        copyResult,copyTarget,T,takeResult,takeSource,takeTarget,P,wordData,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.table,valueStack]
  have hh := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
  rw [hf] at hh
  refine ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO last' none,?_⟩
  simpa [storeBudget,Instruction.code,copyDrain,copyDrainBudget,T,takeResult,takeSource,takeTarget,
    P,wordData,copyTarget] using! hh

/-- The clock budget for decoding a parameter index, looking up its bit word, and pushing the
result. -/
def parameterBudget (i : ℕ) (tail : Bits) (ps stack : List Bits) : ℕ :=
  6*(framed i.bits++tail).length+18+1+
    5000*(i.bits.length+1)*(1+(framed i.bits++tail).length)^2+1+
    (i.bits.length*(2*i.bits.length+5)+3)+1+
    30000*(1+(TableGet.stream ps).length)*(1+(TableGet.stream ps).length+i.bits.length)^2+
    copyDrainBudget (ps.getD i []) (valueStack stack)

/-- A parameter instruction pushes `ps.getD i []` onto the value stack within `parameterBudget`,
preserving the parameter table. -/
theorem parameter_execution (i : ℕ) (tail : Bits) (ps stack : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (Instruction.code (.parameter i)++tail) ps stack))
      (cfg (.phase .firstBit) last (wordData tail ps ((ps.getD i [])::stack)))
      (parameterBudget i tail ps stack) := by
  let P := wordData (framed i.bits++tail) ps stack
  let T := takeResult .index i.bits tail P
  let U := transferResult .index T
  let V := lookupResult ps i.bits [] U
  let W := drainResult .lookup (copyResult .lookup (ps.getD i []) V)
  let v0 := parsed v false false true
  have h0 := parse_execution false false true (framed i.bits++tail) ps stack v
  have h1 := control .dispatch (.take .index takeEntry) P v0 v0 rfl rfl
  obtain ⟨n,last,hR,hC⟩ := take_data .index i.bits tail P v0 rfl
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .index takeEntry) v0 P)
      (cfg (.phase .reverseIndex) (putTake v0 last) T)
      (5000*(i.bits.length+1)*(1+(framed i.bits++tail).length)^2) := by
    refine ⟨n,hR,?_⟩
    simpa [P,wordData,takeTarget] using! hC
  have h3 :=
      control .reverseIndex (.transfer .index 0) T (putTake v0 last) (putTake v0 last) rfl rfl
  obtain ⟨m,hD,hB⟩ := transfer_data .index T (putTake v0 last)
  let v1 :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO (putTake v0 last) none
  have h4 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .index 0) (putTake v0 last) T)
      (cfg (.phase .copyLookup) v1 U) (i.bits.length*(2*i.bits.length+5)+3) := by
    refine ⟨m,hD,?_⟩
    simpa [T,takeResult,takeSource,takeTarget,P,wordData,transferSource,transferTarget,lookupIndex,
      ReadonlyTableGet.store,TableGet.store] using! hB
  have h5 := control .copyLookup (.lookup (.copy .emit)) U v1 v1 rfl rfl
  have hp : ∀ k,U (.lookup k)=ReadonlyTableGet.store (TableGet.stream ps).reverse [] i.bits [] k := by
    intro k
    cases k with
    | inl k => fin_cases k <;>
        simp [U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
          takeTarget,P,wordData,ReadonlyTableGet.store]
    | inr k => cases k <;>
        simp [U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
          takeTarget,P,wordData,ReadonlyTableGet.store,TableGet.store]
  obtain ⟨l,last',hL,hLB⟩ := lookup_data ps i.bits [] U v1 hp
  have h6 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.lookup (.copy .emit)) v1 U)
      (cfg (.copy .lookup copyEntry) (putLookup v1 last') V)
      (30000*(1+(TableGet.stream ps).length)*(1+(TableGet.stream ps).length+i.bits.length)^2) := by
    refine ⟨l,hL,?_⟩
    simpa using! hLB
  obtain ⟨vf,h7⟩ := finish_copy .lookup (ps.getD i []) V (putLookup v1 last')
    (by simp [V,lookupResult,copySource,lookupOutput,ReadonlyTableGet.store,TableGet.store,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits])
  have hf : W=wordData tail ps ((ps.getD i [])::stack) := by
    funext p
    cases p with
    | arithmetic i => fin_cases i <;>
        simp [W,drainResult,drainTarget,copyResult,copyTarget,lookupOutput,V,lookupResult,
          U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
          takeTarget,P,wordData]
    | lookup k =>
      cases k with
      | inl k => fin_cases k <;>
          simp [W,drainResult,drainTarget,copyResult,copyTarget,lookupOutput,V,lookupResult,
            U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
            takeTarget,P,wordData,ReadonlyTableGet.store]
      | inr k => cases k <;>
          simp [W,drainResult,drainTarget,copyResult,copyTarget,lookupOutput,V,lookupResult,
            U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
            takeTarget,P,wordData,ReadonlyTableGet.store,TableGet.store]
    | _ => simp [W,drainResult,drainTarget,copyResult,copyTarget,lookupOutput,V,lookupResult,
        U,transferResult,transferSource,transferTarget,lookupIndex,T,takeResult,takeSource,
        takeTarget,P,wordData,valueStack]
  have hh := ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7
  change Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program _
      (cfg (.phase .firstBit) vf W) _ at hh
  rw [hf] at hh
  refine ⟨vf,?_⟩
  simpa [parameterBudget,Instruction.code,copyDrain,V,lookupResult,U,transferResult,transferSource,
    transferTarget,lookupIndex,T,takeResult,takeSource,takeTarget,P,wordData,copyTarget] using! hh

/-- The payload layout after extracting the two operands of a binary arithmetic instruction. -/
def binaryData (tail : Bits) (ps rest : List Bits) (a b : Bits) : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Payload → Bits :=
  Function.update (Function.update (wordData tail ps rest) (.arithmetic 3) a.reverse)
    (.arithmetic 4) b.reverse

/-- The clock budget for parsing a binary instruction and extracting its two operands. -/
def operandBudget (a b tail : Bits) (rest : List Bits) : ℕ :=
  6*tail.length+18+1+
    5000*(b.length+1)*(1+(framed b++framed a++valueStack rest).length)^2+1+
    5000*(a.length+1)*(1+(framed a++valueStack rest).length)^2

/-- A binary instruction reaches the operand-ready phase with payload `binaryData` and the
prescribed multiplication selector within `operandBudget`. -/
theorem operands_execution (multiply : Bool) (a b tail : Bits) (ps rest : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,last.multiply=multiply ∧ Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (false::true::multiply::tail) ps (b::a::rest)))
      (cfg (.phase .afterOperands) last (binaryData tail ps rest a b))
      (operandBudget a b tail rest) := by
  let P := wordData tail ps (b::a::rest)
  let T := takeResult .left b (framed a++valueStack rest) P
  let U := takeResult .right a (valueStack rest) T
  let v0 := parsed v false true multiply
  let v1 := {v0 with multiply:=multiply}
  have h0 := parse_execution false true multiply tail ps (b::a::rest) v
  have h1 := control .dispatch (.take .left takeEntry) P v0 v1 rfl rfl
  obtain ⟨n,l0,hR,hC⟩ := take_data .left b (framed a++valueStack rest) P v1
    (by simp [P,wordData,takeSource,valueStack])
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .left takeEntry) v1 P)
      (cfg (.phase .takeRight) (putTake v1 l0) T)
      (5000*(b.length+1)*(1+(framed b++framed a++valueStack rest).length)^2) := by
    refine ⟨n,hR,?_⟩
    simpa [P,wordData,takeTarget,List.append_assoc] using! hC
  have h3 := control .takeRight (.take .right takeEntry) T (putTake v1 l0) (putTake v1 l0) rfl rfl
  obtain ⟨m,l1,hD,hB⟩ := take_data .right a (valueStack rest) T (putTake v1 l0)
    (by simp [T,takeResult,takeSource,takeTarget])
  have h4 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.take .right takeEntry) (putTake v1 l0) T)
      (cfg (.phase .afterOperands) (putTake (putTake v1 l0) l1) U)
      (5000*(a.length+1)*(1+(framed a++valueStack rest).length)^2) := by
    refine ⟨m,hD,?_⟩
    simpa [T,takeResult,takeTarget,P,wordData] using! hB
  have hf : U=binaryData tail ps rest a b := by
    funext p
    cases p <;> (try rename_i i; fin_cases i) <;>
      simp [U,T,takeResult,takeSource,takeTarget,P,wordData,binaryData,valueStack]
  have hh := (((h0.trans h1).trans h2).trans h3).trans h4
  rw [hf] at hh
  exact ⟨putTake (putTake v1 l0) l1,rfl,hh⟩

/-- The clock budget for parsing, extracting, adding, copying, and clearing two operands. -/
def addBudget (a b tail : Bits) (rest : List Bits) : ℕ :=
  operandBudget a b tail rest+1+(a.length*(2*a.length+5)+3)+1+
    (b.length*(2*b.length+5)+3)+1+addClockBound a b+
    copyDrainBudget (bitAdd a b) (valueStack rest)

/-- An addition instruction replaces the top two values `b` and `a` with `bitAdd a b` within
`addBudget`. -/
theorem add_execution (a b tail : Bits) (ps rest : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (Instruction.code .add++tail) ps (b::a::rest)))
      (cfg (.phase .firstBit) last (wordData tail ps (bitAdd a b::rest)))
      (addBudget a b tail rest) := by
  let S := binaryData tail ps rest a b
  let T := transferResult .addLeft S
  let U := transferResult .addRight T
  let V := addResult a b U
  let W := drainResult .result (copyResult .result (bitAdd a b) V)
  obtain ⟨v0,hflag,h0⟩ := operands_execution false a b tail ps rest v
  have h1 := control .afterOperands (.transfer .addLeft 0) S v0 v0
    (by simp [cfg,TM2.step,TM2.stepAux,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,hflag])
    (by simp [phaseProgram,stackClock,hflag])
  obtain ⟨n,hR,hC⟩ := transfer_data .addLeft S v0
  let v1 := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v0 none
  have h2 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .addLeft 0) v0 S)
      (cfg (.phase .afterLeft) v1 T) (a.length*(2*a.length+5)+3) := by
    refine ⟨n,hR,?_⟩
    simpa [S,binaryData,wordData,transferSource,transferTarget] using! hC
  have h3 := control .afterLeft (.transfer .addRight 0) T v1 v1 rfl rfl
  obtain ⟨m,hD,hB⟩ := transfer_data .addRight T v1
  let v2 := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v1 none
  have h4 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .addRight 0) v1 T)
      (cfg (.phase .addStart) v2 U) (b.length*(2*b.length+5)+3) := by
    refine ⟨m,hD,?_⟩
    simpa [T,transferResult,transferSource,transferTarget,S,binaryData,wordData] using! hB
  have h5 := control .addStart (.add .loop) U v2 (putAdd v2 AddVar.init) rfl rfl
  obtain ⟨l,hA,hAC⟩ := add_data a b U v2
    (by simp [U,T,transferResult,transferSource,transferTarget,S,binaryData,wordData])
    (by simp [U,T,transferResult,transferSource,transferTarget,S,binaryData,wordData])
    (by simp [U,T,transferResult,transferSource,transferTarget,S,binaryData,wordData])
  have h6 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.add .loop) (putAdd v2 AddVar.init) U)
      (cfg (.copy .result copyEntry) (putAdd v2 (Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum.finalAddVar a b)) V)
      (addClockBound a b) := ⟨l,hA,hAC⟩
  obtain ⟨vf,h7⟩ := finish_copy .result (bitAdd a b) V (putAdd v2 (Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum.finalAddVar a b))
    (by simp [V,addResult,copySource])
  have hf : W=wordData tail ps (bitAdd a b::rest) := by
    funext p
    cases p <;> (try rename_i i; fin_cases i) <;>
      simp [W,drainResult,drainTarget,copyResult,copyTarget,V,addResult,U,T,
        transferResult,transferSource,transferTarget,S,binaryData,wordData,valueStack]
  have hh := ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7
  change Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program _
      (cfg (.phase .firstBit) vf W) _ at hh
  rw [hf] at hh
  refine ⟨vf,?_⟩
  simpa [Instruction.code,addBudget,copyDrain,copyTarget,V,addResult,U,T,transferResult,
    transferSource,transferTarget,S,binaryData,wordData] using! hh

/-- The clock budget for parsing, extracting, multiplying, copying, and clearing two operands. -/
def mulBudget (a b tail : Bits) (rest : List Bits) : ℕ :=
  operandBudget a b tail rest+1+1+31720*(1+a.length+b.length)^4+1+
    (a.length^2+3*a.length+3)+1+
    ((mulAcc a b b.length).length*(2*(mulAcc a b b.length).length+5)+3)+
    resultBudget (mulAcc a b b.length) (valueStack rest)

/-- A multiplication instruction replaces the top two values `b` and `a` with `mulAcc a b
b.length` within `mulBudget`. -/
theorem mul_execution (a b tail : Bits) (ps rest : List Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (Instruction.code .multiply++tail) ps (b::a::rest)))
      (cfg (.phase .firstBit) last (wordData tail ps (mulAcc a b b.length::rest)))
      (mulBudget a b tail rest) := by
  let S := binaryData tail ps rest a b
  let V := mulResult a b S
  let T := drainResult .master V
  let U := transferResult .product T
  let W := drainResult .result (copyResult .result (mulAcc a b b.length) U)
  obtain ⟨v0,hflag,h0⟩ := operands_execution true a b tail ps rest v
  have h1 := control .afterOperands (.phase .mulStart) S v0 v0
    (by simp [cfg,TM2.step,TM2.stepAux,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program,phaseProgram,hflag])
    (by simp [phaseProgram,stackClock,hflag])
  have h2 := control .mulStart (.multiply .outer) S v0 (putMul v0 MulVar.init) rfl rfl
  obtain ⟨n,hR,hC⟩ := mul_data a b S v0
    (by intro i; fin_cases i <;> simp [S,binaryData,wordData,mulStacks])
  let v1 := putMul v0 MulVar.init
  have h3 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.multiply .outer) v1 S)
      (cfg (.phase .clearMaster) v1 V) (31720*(1+a.length+b.length)^4) := ⟨n,hR,hC⟩
  have h4 := control .clearMaster (.drain .master 0) V v1 v1 rfl rfl
  obtain ⟨m,hD,hB⟩ := drain_data .master V v1
  let v2 := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v1 none
  have h5 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.drain .master 0) v1 V)
      (cfg (.phase .reverseProduct) v2 T) (a.length^2+3*a.length+3) := by
    refine ⟨m,hD,?_⟩
    simpa [V,mulResult,drainTarget,mulStacks] using! hB
  have h6 := control .reverseProduct (.transfer .product 0) T v2 v2 rfl rfl
  obtain ⟨l,hA,hAC⟩ := transfer_data .product T v2
  let v3 := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.putIO v2 none
  have h7 : Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program (cfg (.transfer .product 0) v2 T)
      (cfg (.phase .copyResult) v3 U)
      ((mulAcc a b b.length).length*(2*(mulAcc a b b.length).length+5)+3) := by
    refine ⟨l,hA,?_⟩
    simpa [T,drainResult,drainTarget,V,mulResult,mulStacks,transferSource,transferTarget] using! hAC
  obtain ⟨vf,h8⟩ := finish_result (mulAcc a b b.length) U v3
    (by simp [U,transferResult,transferSource,transferTarget,T,drainResult,drainTarget,V,mulResult,mulStacks])
  have hf : W=wordData tail ps (mulAcc a b b.length::rest) := by
    funext p
    cases p <;> (try rename_i i; fin_cases i) <;>
      simp [W,drainResult,drainTarget,copyResult,copyTarget,U,transferResult,transferSource,
        transferTarget,T,V,mulResult,mulStacks,S,binaryData,wordData,valueStack]
  have hh :=
      (((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8
  change Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program _
      (cfg (.phase .firstBit) vf W) _ at hh
  rw [hf] at hh
  refine ⟨vf,?_⟩
  simpa [Instruction.code,mulBudget,U,transferResult,transferSource,transferTarget,T,
    drainResult,drainTarget,V,mulResult,S,binaryData,wordData] using! hh

/-- Select the execution budget for an instruction and word state, returning zero for
unsupported stack shapes. -/
def instructionBudget : Instruction → Bits → WordState → ℕ
  | .literal bits,tail,s => literalBudget bits tail s.values
  | .parameter i,tail,s => parameterBudget i tail s.parameters s.values
  | .add,tail,⟨_,b::a::rest⟩ => addBudget a b tail rest
  | .multiply,tail,⟨_,b::a::rest⟩ => mulBudget a b tail rest
  | .store,tail,⟨ps,a::rest⟩ => storeBudget a tail ps rest
  | _,_,_ => 0

/-- Every successful word-level instruction execution is realized by the stack machine within
`instructionBudget`, consuming the instruction code and preserving the program tail. -/
theorem instruction_execution (op : Instruction) (tail : Bits) (s s' : WordState) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s=some s') :
    ∃ last,Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      (cfg (.phase .firstBit) v (wordData (op.code++tail) s.parameters s.values))
      (cfg (.phase .firstBit) last (wordData tail s'.parameters s'.values))
      (instructionBudget op tail s) := by
  rcases s with ⟨ps,values⟩
  cases op with
  | literal bits =>
    simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at h
    subst s'
    exact literal_execution bits tail ps values v
  | parameter i =>
    simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at h
    subst s'
    exact parameter_execution i tail ps values v
  | add =>
    cases values with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at h
    | cons b rest =>
      cases rest with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at h
      | cons a rest =>
        simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at h
        subst s'
        exact add_execution a b tail ps rest v
  | multiply =>
    cases values with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at h
    | cons b rest =>
      cases rest with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at h
      | cons a rest =>
        simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at h
        subst s'
        exact mul_execution a b tail ps rest v
  | store =>
    cases values with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at h
    | cons a rest =>
      simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at h
      subst s'
      exact store_execution a tail ps rest v

/-- The sum of instruction budgets along the word-level execution, stopping the recursive
contribution when an instruction fails. -/
def programBudget : List Instruction → Bits → WordState → ℕ
  | [],_,_ => 0
  | op::rest,tail,s => instructionBudget op (programCode rest++tail) s+
      match Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with | some next => programBudget rest tail next | none => 0

/-- The maximum instruction budget along the word-level execution, stopping the recursive
contribution when an instruction fails. -/
def programPeak : List Instruction → Bits → WordState → ℕ
  | [],_,_ => 0
  | op::rest,tail,s => max (instructionBudget op (programCode rest++tail) s)
      (match Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with | some next => programPeak rest tail next | none => 0)

/-- Every successful word-level program run is realized by a `PathExecution` that consumes its
encoded program and respects `programBudget` and `programPeak`. -/
theorem program_execution (p : List Instruction) (tail : Bits) (s s' : WordState) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p s=some s') :
    ∃ last,PathExecution
      (cfg (.phase .firstBit) v (wordData (programCode p++tail) s.parameters s.values))
      (cfg (.phase .firstBit) last (wordData tail s'.parameters s'.values))
      (programBudget p tail s) (programPeak p tail s) := by
  induction p generalizing s v with
  | nil =>
    simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,Option.some.injEq] at h
    subst s'
    exact ⟨v,0,rfl,Nat.le_refl 0,Nat.le_refl 0⟩
  | cons op rest ih =>
    cases he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
    | none => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,he] at h
    | some next =>
      have hr :
          Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run rest next=some s' :=
          by simpa only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,he,Option.bind_some] using! h
      obtain ⟨mid,h0⟩ := instruction_execution op (programCode rest++tail) s next v he
      obtain ⟨last,h1⟩ := ih next mid hr
      have hh := (path_of_execution h0).trans h1
      refine ⟨last,?_⟩
      simpa [programCode,List.append_assoc,programBudget,programPeak,he] using! hh

end Qatlib.Concepts.AdversaryBounds.AdvDuality
