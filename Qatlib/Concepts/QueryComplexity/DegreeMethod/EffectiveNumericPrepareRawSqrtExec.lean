/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtExec
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def memory (A : FramedTake.Slot → Bits) (R : Fin 9 → Bits) (W : Fin 6 → Bits)
    (F : FrameCopy.Slot → Bits) (raw : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits
  | 0 => A .reader | 1 => A .markers | 2 => A .payload | 3 => A .count
  | 4 => A .temporary | 5 => A .header | 6 => A .output
  | 7 => R 0 | 8 => R 1 | 9 => R 2 | 10 => R 3 | 11 => R 4
  | 12 => R 5 | 13 => R 6 | 14 => R 7 | 15 => R 8
  | 16 => W 0 | 17 => W 1 | 18 => W 2 | 19 => W 3 | 20 => W 4 | 21 => W 5
  | 22 => F .source | 23 => F .restore | 24 => F .copy | 25 => F .count
  | 26 => F .temporary | 27 => F .markers | 28 => F .header | 29 => F .output
  | _ => raw

def readerFrame (W : Fin 6 → Bits) (F : FrameCopy.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9) → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory (fun s => S (.inl s)) (fun i => S (.inr i)) W F raw

theorem readerFrame_at (W : Fin 6 → Bits) (F : FrameCopy.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9) → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9)) :
    readerFrame W F raw S (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.readCode i)=S i := by
  cases i with
  | inl s => cases s <;> rfl
  | inr i => fin_cases i <;> rfl

theorem readerFrame_update (W : Fin 6 → Bits) (F : FrameCopy.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9) → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9)) (bits : Bits) :
    readerFrame W F raw (Function.update S i bits)=
      Function.update (readerFrame W F raw S) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.readCode i) bits := by
  cases i with
  | inl s => cases s <;> funext j <;> fin_cases j <;> rfl
  | inr i => fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem read_call (index : Fin 5) (R : Fin 9 → Bits) (W : Fin 6 → Bits)
    (F : FrameCopy.Slot → Bits) (raw bits tail : Bits) (hfresh : R (readDst index)=[]) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.read index (.take (.read (.read .unary)))),default,
        memory (FramedTake.store (framed bits++tail) [] [] []) R W F raw⟩
      ⟨some (nextRead index),default,
        memory (FramedTake.store tail [] [] []) (Function.update R (readDst index) bits) W F raw⟩
      (10000*(1+(framed bits++tail).length)^3) := by
  obtain ⟨ticks,hr,hc⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.complete
      (readDst index) R bits tail hfresh
  obtain ⟨hN,hNC⟩ := StackCall.execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.readCode (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.read index) (nextRead index) getReader putReader
    (readerFrame W F raw) (readerFrame_at W F raw) (readerFrame_update W F raw)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.program (readDst index)) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    default _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

def inputRegisters (k : ℕ) (qN qD sN sD : Bits) : Fin 9 → Bits
  | 0 => qN | 1 => qD | 2 => sN | 3 => sD | 8 => k.bits | _ => []

theorem read_all (k : ℕ) (qN qD sN sD : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.read 0 (.take (.read (.read .unary)))),default,
        memory (FramedTake.store (input k qN qD sN sD) [] [] [])
          (fun _ => []) (fun _ => []) (fun _ => []) []⟩
      ⟨some (.preprocess (.call 0 (.copy false .emit))),default,
        memory (FramedTake.store [] [] [] []) (inputRegisters k qN qD sN sD)
          (fun _ => []) (fun _ => []) []⟩
      (50000*(1+(input k qN qD sN sD).length)^3) := by
  let R0 : Fin 9 → Bits := fun _ => []
  let R1 := Function.update R0 8 k.bits
  let R2 := Function.update R1 0 qN
  let R3 := Function.update R2 1 qD
  let R4 := Function.update R3 2 sN
  let R5 := Function.update R4 3 sD
  let tail₁ := framed qN++(framed qD++(framed sN++framed sD))
  let tail₂ := framed qD++(framed sN++framed sD)
  let tail₃ := framed sN++framed sD
  have h0 := read_call 0 R0 (fun _ => []) (fun _ => []) [] k.bits tail₁ (by rfl)
  have h1 := read_call 1 R1 (fun _ => []) (fun _ => []) [] qN tail₂ (by rfl)
  have h2 := read_call 2 R2 (fun _ => []) (fun _ => []) [] qD tail₃ (by rfl)
  have h3 := read_call 3 R3 (fun _ => []) (fun _ => []) [] sN (framed sD) (by rfl)
  have h4 := read_call 4 R4 (fun _ => []) (fun _ => []) [] sD [] (by rfl)
  simp only [List.append_nil] at h4
  have hR : R5=inputRegisters k qN qD sN sD := by
    funext i
    fin_cases i <;> rfl
  have hall := (((h0.trans h1).trans h2).trans h3).trans h4
  change Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program _
    ⟨some (.preprocess (.call 0 (.copy false .emit))),default,
      memory (FramedTake.store [] [] [] []) R5 (fun _ => []) (fun _ => []) []⟩ _ at hall
  rw [hR] at hall
  apply hall.mono
  let N := 1+(input k qN qD sN sD).length
  have hp1 : (1+(framed qN++tail₂).length)^3 ≤ N^3 := by
    apply Nat.pow_le_pow_left
    dsimp [N,input,tail₂]
    simp only [List.length_append]
    omega
  have hp2 : (1+(framed qD++tail₃).length)^3 ≤ N^3 := by
    apply Nat.pow_le_pow_left
    dsimp [N,input,tail₃]
    simp only [List.length_append]
    omega
  have hp3 : (1+(framed sN++framed sD).length)^3 ≤ N^3 := by
    apply Nat.pow_le_pow_left
    dsimp [N,input]
    simp only [List.length_append]
    omega
  have hp4 : (1+(framed sD).length)^3 ≤ N^3 := by
    apply Nat.pow_le_pow_left
    dsimp [N,input]
    simp only [List.length_append]
    omega
  change 10000*N^3+10000*(1+(framed qN++tail₂).length)^3+
    10000*(1+(framed qD++tail₃).length)^3+10000*(1+(framed sN++framed sD).length)^3+
    10000*(1+(framed sD).length)^3 ≤ 50000*N^3
  nlinarith

def initialFrame (S : Fin 2 → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory (FramedTake.store (S 1) [] [] []) (fun _ => []) (fun _ => []) (fun _ => []) (S 0)

theorem initialFrame_at (S : Fin 2 → Bits) (i : Fin 2) : initialFrame S (initCode i)=S i := by
  fin_cases i <;> rfl

theorem initialFrame_update (S : Fin 2 → Bits) (i : Fin 2) (bits : Bits) :
    initialFrame (Function.update S i bits)=Function.update (initialFrame S) (initCode i) bits := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem init_call (word : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (TM2.init 30 word.reverse)
      ⟨some (.read 0 (.take (.read (.read .unary)))),default,
        memory (FramedTake.store word [] [] []) (fun _ => []) (fun _ => []) (fun _ => []) []⟩
      (10*(1+word.length)^2) := by
  have hstart : initialFrame (stackPair word.reverse [])=
      Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 word.reverse := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hr,hc⟩ := StackCall.execution initCode Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.init (.read 0 (.take (.read (.read .unary))))
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO initialFrame initialFrame_at initialFrame_update
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    default _ _ _ (transfer_run word.reverse [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO default))
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    List.append_nil,List.reverse_reverse,List.length_reverse,hstart] at hr hc
  refine ⟨word.length+1,hr,?_⟩
  have hc0 :=
      transfer_clock word.reverse []
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO default)
  simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hc0
  change stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (word.length+1)
    ⟨some (.init 0),default,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 word.reverse⟩ ≤ _
  have hio :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO default
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO default)=default := rfl
  rw [hio] at hc
  rw [hc,hc0]
  nlinarith

theorem frontend (k : ℕ) (qN qD sN sD : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (TM2.init 30 (input k qN qD sN sD).reverse)
      ⟨some (.preprocess (.call 0 (.copy false .emit))),default,
        memory (FramedTake.store [] [] [] []) (inputRegisters k qN qD sN sD)
          (fun _ => []) (fun _ => []) []⟩
      (60000*(1+(input k qN qD sN sD).length)^3) := by
  apply ((init_call (input k qN qD sN sD)).trans (read_all k qN qD sN sD)).mono
  let N := 1+(input k qN qD sN sD).length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have h23 : N^2 ≤ N^3 := by have h := Nat.mul_le_mul_left (N^2) hN; nlinarith
  change 10*N^2+50000*N^3 ≤ 60000*N^3
  nlinarith

def extendRegisters (R : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Register → Bits) (precision : Bits) : Fin 9 → Bits
  | 0 => R 0 | 1 => R 1 | 2 => R 2 | 3 => R 3 | 4 => R 4
  | 5 => R 5 | 6 => R 6 | 7 => R 7 | _ => precision

def productFrame (A : FramedTake.Slot → Bits) (F : FrameCopy.Slot → Bits) (raw precision : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory A (extendRegisters (fun i => S (.inr i)) precision) (fun i => S (.inl i)) F raw

theorem productFrame_at (A : FramedTake.Slot → Bits) (F : FrameCopy.Slot → Bits) (raw precision : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot) :
    productFrame A F raw precision S (productCode i)=S i := by
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

theorem productFrame_update (A : FramedTake.Slot → Bits) (F : FrameCopy.Slot → Bits) (raw precision : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot) (bits : Bits) :
    productFrame A F raw precision (Function.update S i bits)=
      Function.update (productFrame A F raw precision S) (productCode i) bits := by
  cases i with
  | inl i => fin_cases i <;> funext j <;> fin_cases j <;> rfl
  | inr i => fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem preprocess_call (k : ℕ) (qN qD sN sD : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.preprocess (.call 0 (.copy false .emit))),default,
        memory (FramedTake.store [] [] [] []) (inputRegisters k qN qD sN sD)
          (fun _ => []) (fun _ => []) []⟩
      ⟨some .launch,default,
        memory (FramedTake.store [] [] [] [])
          (extendRegisters (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.result qN qD sN sD) k.bits)
          (fun _ => []) (fun _ => []) []⟩
      ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400*(1+qN.length+qD.length+sN.length+sD.length)^4) := by
  have hInput : extendRegisters (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.initial qN qD sN sD) k.bits=
      inputRegisters k qN qD sN sD := by
    funext i
    fin_cases i <;> rfl
  let A := FramedTake.store [] [] [] []
  let F : FrameCopy.Slot → Bits := fun _ => []
  have hstart : productFrame A F [] k.bits
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.store (fun _ => []) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.initial qN qD sN sD))=
      memory A (inputRegisters k qN qD sN sD) (fun _ => []) F [] := by
    change memory A (extendRegisters (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.initial qN qD sN sD) k.bits)
      (fun _ => []) F []=_
    rw [hInput]
  obtain ⟨ticks,hr,hc⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.complete_bound qN qD sN sD
  obtain ⟨hN,hNC⟩ := StackCall.execution productCode Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.preprocess .launch getProduct putProduct
    (productFrame A F [] k.bits) (productFrame_at A F [] k.bits) (productFrame_update A F [] k.bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.program Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    default _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hstart] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

def loopReader (reader out : Bits) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) : FramedTake.Slot → Bits
  | .reader => reader | .markers => S (.inl 8) | .payload => S (.inl 9)
  | .count => S (.inl 10) | .temporary => S (.inl 11)
  | .header => S (.inr 1) | .output => out

def loopRegisters (R : Fin 9 → Bits) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) : Fin 9 → Bits
  | 0 => R 0 | 1 => R 1 | 2 => R 2 | 3 => R 3 | 4 => R 4
  | 5 => S (.inl 3) | 6 => R 6 | 7 => S (.inl 2) | _ => S (.inr 0)

def loopWorking (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) : Fin 6 → Bits
  | 0 => S (.inl 0) | 1 => S (.inl 1) | 2 => S (.inl 4)
  | 3 => S (.inl 5) | 4 => S (.inl 6) | _ => S (.inl 7)

def loopFrame (R : Fin 9 → Bits) (F : FrameCopy.Slot → Bits) (raw reader out : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory (loopReader reader out S) (loopRegisters R S) (loopWorking S) F raw

theorem loopFrame_at (R : Fin 9 → Bits) (F : FrameCopy.Slot → Bits) (raw reader out : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot) :
    loopFrame R F raw reader out S (loopCode i)=S i := by
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

theorem loopFrame_update (R : Fin 9 → Bits) (F : FrameCopy.Slot → Bits) (raw reader out : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot) (bits : Bits) :
    loopFrame R F raw reader out (Function.update S i bits)=
      Function.update (loopFrame R F raw reader out S) (loopCode i) bits := by
  cases i with
  | inl i => fin_cases i <;> funext j <;> fin_cases j <;> rfl
  | inr i => fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem loop_call (k : ℕ) (counter : Bits) (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local)
    (R : Fin 9 → Bits) (F : FrameCopy.Slot → Bits) (raw reader out : Bits)
    (hnum : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue counter=k) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.loop (.counter .borrow)),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        loopFrame R F raw reader out (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store counter [] d)⟩
      ⟨some (.emit 0 (.copy .emit)),putLoop v (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        loopFrame R F raw reader out (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store [] [] ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) d))⟩
      (4000000*(k+1)^2*(counter.length+d.width+10*k+10)^2) := by
  obtain ⟨ticks,hr,hc,_,_⟩ := Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.complete_bounds k counter d
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)) hnum
  obtain ⟨hN,hNC⟩ := StackCall.execution loopCode Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.loop (.emit 0 (.copy .emit)) getLoop putLoop
    (loopFrame R F raw reader out) (loopFrame_at R F raw reader out) (loopFrame_update R F raw reader out)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.program Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    v _ _ _ hr
  simp only [StackCall.cfg,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.loopCfg,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.haltedCfg,Option.map_some,Option.getD_some,
    Option.map_none,Option.getD_none] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

def joinRegisters (R : Fin 9 → Bits) (W : Fin 6 → Bits) : Fin 15 → Bits
  | 0 => R 0 | 1 => R 1 | 2 => R 2 | 3 => R 3 | 4 => R 4
  | 5 => R 5 | 6 => R 6 | 7 => R 7 | 8 => R 8
  | 9 => W 0 | 10 => W 1 | 11 => W 2 | 12 => W 3 | 13 => W 4 | _ => W 5

def writerRegisters (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Bits) : Fin 9 → Bits :=
  fun i => S (.inr (Fin.castLE (by decide) i))

def writerWorking (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Bits) : Fin 6 → Bits :=
  fun i => S (.inr ⟨9+i.val,by omega⟩)

def writerFrame (A : FramedTake.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory A (writerRegisters S) (writerWorking S) (fun s => S (.inl s)) raw

theorem writerFrame_at (A : FramedTake.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15)) :
    writerFrame A raw S (writeCode i)=S i := by
  cases i with
  | inl s => cases s <;> rfl
  | inr i => fin_cases i <;> rfl

theorem writerFrame_update (A : FramedTake.Slot → Bits) (raw : Bits)
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Bits) (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15)) (bits : Bits) :
    writerFrame A raw (Function.update S i bits)=
      Function.update (writerFrame A raw S) (writeCode i) bits := by
  cases i with
  | inl s => cases s <;> funext j <;> fin_cases j <;> rfl
  | inr i => fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem writerFrame_store (A : FramedTake.Slot → Bits) (raw : Bits) (R : Fin 9 → Bits)
    (W : Fin 6 → Bits) (source out : Bits) :
    writerFrame A raw (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.store (joinRegisters R W) source out)=
      memory A R W (FrameCopy.store source [] [] [] [] out) raw := by
  funext i
  fin_cases i <;> rfl

theorem emit_call (index : Fin 3) (A : FramedTake.Slot → Bits) (raw : Bits)
    (R : Fin 9 → Bits) (W : Fin 6 → Bits) (out : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.emit index (.copy .emit)),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,
        memory A R W (FrameCopy.store [] [] [] [] [] out) raw⟩
      ⟨some (nextEmit index),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,
        memory A R W (FrameCopy.store [] [] [] [] []
          (framed (joinRegisters R W (writeSrc index))++out)) raw⟩
      (11000*(1+(joinRegisters R W (writeSrc index)).length+out.length)^3) := by
  obtain ⟨ticks,hr,hc⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.complete
      (writeSrc index) (joinRegisters R W) out
  obtain ⟨hN,hNC⟩ := StackCall.execution writeCode (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.emit index) (nextEmit index) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO
    (writerFrame A raw) (writerFrame_at A raw) (writerFrame_update A raw)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.program (writeSrc index)) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    v _ _ _ hr
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    writerFrame_store] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

def preparedRegisters (k : ℕ) (qN qD sN sD : Bits) : Fin 9 → Bits :=
  extendRegisters (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.result qN qD sN sD) k.bits

theorem launch_call (k : ℕ) (qN qD sN sD : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some .launch,default,
        memory (FramedTake.store [] [] [] []) (preparedRegisters k qN qD sN sD)
          (fun _ => []) (fun _ => []) []⟩
      ⟨some (.loop (.counter .borrow)),putLoop default (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
        loopFrame (preparedRegisters k qN qD sN sD) (fun _ => []) [] [] []
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store k.bits [] (data qN qD sN sD))⟩
      (100*(1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length)^2) := by
  let S := memory (FramedTake.store [] [] [] []) (preparedRegisters k qN qD sN sD)
    (fun _ => []) (fun _ => []) []
  have hs : Function.update (Function.update S 12 (false::S 12)) 12 (false::false::S 12)=
      loopFrame (preparedRegisters k qN qD sN sD) (fun _ => []) [] [] []
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store k.bits [] (data qN qD sN sD)) := by
    funext i
    fin_cases i <;> rfl
  refine ⟨1,?_,?_⟩
  · change some (⟨some (.loop (.counter .borrow)),putLoop default (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none)),
      Function.update (Function.update S 12 (false::S 12)) 12 (false::false::S 12)⟩ :
      TM2.Cfg (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local)=_
    rw [hs]
  · change 1+(2*(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length+3+
      (2*((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length+1)+3+0))+0 ≤ _
    nlinarith

theorem emit_all (A : FramedTake.Slot → Bits) (raw : Bits) (R : Fin 9 → Bits)
    (W : Fin 6 → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some (.emit 0 (.copy .emit)),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,
        memory A R W (FrameCopy.store [] [] [] [] [] []) raw⟩
      ⟨some (.drain 0 0),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,
        memory A R W (FrameCopy.store [] [] [] [] []
          (framed (R 2)++(framed (R 3)++framed (W 2)))) raw⟩
      (11000*((1+(W 2).length)^3+(1+(R 3).length+(framed (W 2)).length)^3+
        (1+(R 2).length+(framed (R 3)++framed (W 2)).length)^3)) := by
  have h0 := emit_call 0 A raw R W [] v
  have h1 := emit_call 1 A raw R W (framed (W 2)) v
  have h2 := emit_call 2 A raw R W (framed (R 3)++framed (W 2)) v
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at h0
  have hall := (h0.trans h1).trans h2
  apply hall.mono
  change 11000*(1+(W 2).length)^3+11000*(1+(R 3).length+(framed (W 2)).length)^3+
    11000*(1+(R 2).length+(framed (R 3)++framed (W 2)).length)^3 ≤ _
  exact le_of_eq (by ring)

theorem drain_call (index : Fin 29) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ⟨some (.drain index 0),v,S⟩
      ⟨some (nextDrain index),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,Function.update S (Fin.castLE (by decide) index) []⟩
      (10*(1+(S (Fin.castLE (by decide) index)).length)^2) := by
  let code := drainCode index
  let bits := S (Fin.castLE (by decide) index)
  have hinj : Function.Injective code := fun a b _ => Subsingleton.elim a b
  have hsame : StackCall.frame code S (Normalization.singleStack bits)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    rfl
  have ht : Normalization.singleStack []=
      Function.update (Normalization.singleStack bits) (0 : Fin 1) [] := by
    funext i
    fin_cases i
    rfl
  have hfinal : StackCall.frame code S (Normalization.singleStack [])=
      Function.update S (Fin.castLE (by decide) index) [] := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    rfl
  obtain ⟨hr,hc⟩ := StackCall.execution code (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.drain index) (nextDrain index) Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    v _ _ _ (Normalization.drain_run bits (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO v))
  have hio :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO v)=v := rfl
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,hio] at hr hc
  refine ⟨bits.length+1,hr,?_⟩
  rw [hc,Normalization.drain_clock]
  nlinarith

def clearBefore
    (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits)
    (n : ℕ) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot →
    Bits := fun i => if i.val<n then [] else S i

theorem clearBefore_step (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits) (i : Fin 29) :
    Function.update (clearBefore S i.val) (Fin.castLE (by decide) i) []=
      clearBefore S (i.val+1) := by
  funext j
  by_cases heq : j=Fin.castLE (by decide) i
  · subst j
    rw [Function.update_self]
    exact (if_pos (show (Fin.castLE (by decide) i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot).val < i.val+1 by dsimp; omega)).symm
  · rw [Function.update_of_ne heq]
    have hne : j.val≠i.val := by
      intro h
      apply heq
      apply Fin.ext
      exact h
    dsimp only [clearBefore]
    by_cases hlt : j.val < i.val
    · rw [if_pos hlt,if_pos (by omega)]
    · rw [if_neg hlt,if_neg (by omega)]

def drainLabel (index : ℕ) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label :=
  if h : index<29 then .drain ⟨index,h⟩ 0 else .output 0

theorem nextDrain_label (i : Fin 29) : nextDrain i=drainLabel (i.val+1) := rfl

theorem drains_from (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) (H : ℕ) (hH : ∀ i, (S i).length≤H) :
    ∀ (n i : ℕ), i+n=29 →
      Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ⟨some (drainLabel i),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,clearBefore S i⟩
        ⟨some (.output 0),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,clearBefore S 29⟩ (10*n*(1+H)^2) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have heq : i=29 := by omega
    subst i
    refine ⟨0,rfl,?_⟩
    simp only [stackRunClock,Nat.mul_zero,Nat.zero_mul,le_refl]
  | succ n ih =>
    intro i hi
    have hiLt : i<29 := by omega
    let index : Fin 29 := ⟨i,hiLt⟩
    have hget : clearBefore S i (Fin.castLE (by decide) index)=S (Fin.castLE (by decide) index) := by
      change (if i < i then [] else S (Fin.castLE (by decide) index))=_
      rw [if_neg (Nat.lt_irrefl i)]
    have hStep :=
        drain_call index (clearBefore S i)
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none)
    rw [hget] at hStep
    have hb := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left
      (Nat.add_le_add_left (hH (Fin.castLE (by decide) index)) 1) 2)
    have hStep' := hStep.mono hb
    have hv :
        Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none) none=Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none := rfl
    rw [clearBefore_step S index,hv,nextDrain_label] at hStep'
    have hl : drainLabel i=.drain index 0 := dif_pos hiLt
    rw [← hl] at hStep'
    have hRest := ih (i+1) (by omega)
    apply (hStep'.trans hRest).mono
    exact le_of_eq (by ring)

theorem drain_all (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) (H : ℕ) (hH : ∀ i, (S i).length≤H) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ⟨some (.drain 0 0),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,S⟩
      ⟨some (.output 0),Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,clearBefore S 29⟩ (290*(1+H)^2) := by
  have h := drains_from S v H hH 29 0 (by omega)
  have hzero : clearBefore S 0=S := by
    funext i
    exact if_neg (Nat.not_lt_zero i.val)
  rw [hzero] at h
  exact h

def outputFrame (S : Fin 2 → Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  Function.update (Function.update (fun _ => []) 29 (S 0)) 30 (S 1)

theorem outputFrame_at (S : Fin 2 → Bits) (i : Fin 2) : outputFrame S (outputCode i)=S i := by
  fin_cases i <;> rfl

theorem outputFrame_update (S : Fin 2 → Bits) (i : Fin 2) (bits : Bits) :
    outputFrame (Function.update S i bits)=Function.update (outputFrame S) (outputCode i) bits := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem output_call (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Local) (hraw : S 30=[]) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ⟨some (.output 0),v,clearBefore S 29⟩
      ⟨none,default,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (S 29).reverse⟩
      (10*(1+(S 29).length)^2+1) := by
  have hstart : outputFrame (stackPair (S 29) [])=clearBefore S 29 := by
    funext i
    fin_cases i <;> first | rfl | exact hraw.symm
  have hfinal : outputFrame (stackPair [] (S 29).reverse)=
      Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (S 29).reverse := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hr,hc⟩ := StackCall.execution outputCode Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Label.output .done Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO
    outputFrame outputFrame_at outputFrame_update
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (fun _ => rfl)
    v _ _ _ (transfer_run (S 29) [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO v))
  have hio :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.getIO v)=v := rfl
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    List.append_nil,hstart,hfinal,hio] at hr hc
  have e0 : Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ⟨some (.output 0),v,clearBefore S 29⟩
      ⟨some .done,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (S 29).reverse⟩
      (10*(1+(S 29).length)^2) := by
    refine ⟨(S 29).length+1,hr,?_⟩
    rw [hc,transfer_clock]
    simp only [List.length_nil,Nat.add_zero]
    nlinarith
  have e1 : Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
      ⟨some .done,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (S 29).reverse⟩
      ⟨none,default,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (S 29).reverse⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  exact e0.trans e1

def completedData (k : ℕ) (qN qD sN sD : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
  (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) (data qN qD sN sD)

def completedRegisters (k : ℕ) (qN qD sN sD : Bits) : Fin 9 → Bits :=
  loopRegisters (preparedRegisters k qN qD sN sD) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store [] [] (completedData k qN qD sN sD))

def completedWorking (k : ℕ) (qN qD sN sD : Bits) : Fin 6 → Bits :=
  loopWorking (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store [] [] (completedData k qN qD sN sD))

def lastMemory (k : ℕ) (qN qD sN sD : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot → Bits :=
  memory (FramedTake.store [] [] [] []) (completedRegisters k qN qD sN sD)
    (completedWorking k qN qD sN sD) (FrameCopy.store [] [] [] [] [] (output k qN qD sN sD)) []

noncomputable def executionBudget (k : ℕ) (qN qD sN sD : Bits) : ℕ :=
  let d := completedData k qN qD sN sD
  60000*(1+(input k qN qD sN sD).length)^3+
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400*(1+qN.length+qD.length+sN.length+sD.length)^4+
    100*(1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length)^2+
    4000000*(k+1)^2*(k.bits.length+(data qN qD sN sD).width+10*k+10)^2+
    11000*((1+d.a.length)^3+(1+sD.length+(framed d.a).length)^3+
      (1+sN.length+(framed sD++framed d.a).length)^3)+
    290*(1+Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (lastMemory k qN qD sN sD))^2+
    (10*(1+(output k qN qD sN sD).length)^2+1)

theorem complete (k : ℕ) (qN qD sN sD : Bits) :
    Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (TM2.init 30 (input k qN qD sN sD).reverse)
      ⟨none,default,Function.update (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot => []) 30 (output k qN qD sN sD).reverse⟩
      (executionBudget k qN qD sN sD) := by
  let R := preparedRegisters k qN qD sN sD
  let d := completedData k qN qD sN sD
  let v :=
      putLoop default
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialRound.resetLocal,(false,none))
  let A := FramedTake.store [] [] [] []
  let R' := completedRegisters k qN qD sN sD
  let W' := completedWorking k qN qD sN sD
  let S := lastMemory k qN qD sN sD
  have h0 := frontend k qN qD sN sD
  have h1 := preprocess_call k qN qD sN sD
  have h2 := launch_call k qN qD sN sD
  have hL := loop_call k k.bits (data qN qD sN sD) default R (fun _ => []) [] [] []
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits k)
  have hLmem : loopFrame R (fun _ => []) [] [] [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.store [] [] d)=
      memory A R' W' (FrameCopy.store [] [] [] [] [] []) [] := by
    funext i
    fin_cases i <;> rfl
  dsimp only [d,completedData] at hLmem
  rw [hLmem] at hL
  have hE := emit_all A [] R' W' v
  have hio :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.putIO v none=v :=
      rfl
  rw [hio] at hE
  change Execution Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program
    ⟨some (.emit 0 (.copy .emit)),v,memory A R' W' (FrameCopy.store [] [] [] [] [] []) []⟩
    ⟨some (.drain 0 0),v,S⟩ _ at hE
  have hH (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.Slot) : (S i).length ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight S :=
    Finset.le_sup (f:=fun i => (S i).length) (Finset.mem_univ i)
  have hD :=
      drain_all S v (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight S) hH
  rw [hio] at hD
  have hO := output_call S v (by rfl)
  have hall := ((((((h0.trans h1).trans h2).trans hL).trans hE ).trans hD).trans hO)
  exact hall

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtExec
