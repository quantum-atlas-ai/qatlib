/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

abbrev Slot := Fin 31
abbrev Local :=
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Local × Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Local × Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Local × Symbol

inductive Label where
  | init (l : Fin 1)
  | read (index : Fin 5) (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Label)
  | preprocess (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.Label)
  | launch
  | loop (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Label)
  | emit (index : Fin 3) (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Label)
  | drain (index : Fin 29) (l : Fin 1)
  | output (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.init 0⟩

def getReader (v : Local) := v.1
def putReader (v : Local)
    (w : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Local) :
    Local := (w,v.2)
def getProduct (v : Local) := v.2.1
def putProduct (v : Local)
    (w : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Local) :
    Local := (v.1,w,v.2.2)
def getLoop (v : Local) := v.2.2.1
def putLoop (v : Local)
    (w : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Local) : Local :=
    (v.1,v.2.1,w,v.2.2.2)
def getIO (v : Local) := v.2.2.2
def putIO (v : Local) (w : Symbol) : Local := (v.1,v.2.1,v.2.2.1,w)

def parserCode : FramedTake.Slot → Slot
  | .reader => 0 | .markers => 1 | .payload => 2 | .count => 3
  | .temporary => 4 | .header => 5 | .output => 6

def readCode : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.Slot (Fin 9) → Slot
  | .inl s => parserCode s
  | .inr i => ⟨7+i.val,by omega⟩

def readDst : Fin 5 → Fin 9 | 0 => 8 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 3

def nextRead (i : Fin 5) : Label :=
  if h : i.val+1<5 then .read ⟨i.val+1,h⟩ (.take (.read (.read .unary)))
  else .preprocess (.call 0 (.copy false .emit))

def productCode : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Slot → Slot
  | .inl i => ⟨16+i.val,by omega⟩
  | .inr i => ⟨7+i.val,by omega⟩

def loopCode : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Slot → Slot
  | .inl 0 => 16 | .inl 1 => 17 | .inl 2 => 14 | .inl 3 => 12
  | .inl 4 => 18 | .inl 5 => 19 | .inl 6 => 20 | .inl 7 => 21
  | .inl 8 => 1 | .inl 9 => 2 | .inl 10 => 3 | .inl _ => 4
  | .inr 0 => 15 | .inr _ => 5

def frameCode : FrameCopy.Slot → Slot
  | .source => 22 | .restore => 23 | .copy => 24 | .count => 25
  | .temporary => 26 | .markers => 27 | .header => 28 | .output => 29

def writeCode : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.Slot (Fin 15) → Slot
  | .inl s => frameCode s
  | .inr i => ⟨7+i.val,by omega⟩

def writeSrc : Fin 3 → Fin 15 | 0 => 11 | 1 => 3 | _ => 2
def nextEmit (i : Fin 3) : Label :=
  if h : i.val+1<3 then .emit ⟨i.val+1,h⟩ (.copy .emit) else .drain 0 0

def initCode : Fin 2 → Slot | 0 => 30 | _ => 0
def outputCode : Fin 2 → Slot | 0 => 29 | _ => 30
def drainCode (i : Fin 29) (_ : Fin 1) : Slot := Fin.castLE (by decide) i
def nextDrain (i : Fin 29) : Label :=
  if h : i.val+1<29 then .drain ⟨i.val+1,h⟩ 0 else .output 0

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .init l => StackCall.stmt initCode Label.init (.read 0 (.take (.read (.read .unary))))
      getIO putIO (transferProgram l)
  | .read i l => StackCall.stmt readCode (Label.read i) (nextRead i)
      getReader putReader (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareReader.program (readDst i) l)
  | .preprocess l => StackCall.stmt productCode Label.preprocess .launch
      getProduct putProduct (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.program l)
  | .launch => .push 12 (fun _ => false) (.push 12 (fun _ => false)
      (.load (fun v => putLoop v (TrialRound.resetLocal,(false,none)))
        (.goto (fun _ => .loop (.counter .borrow)))))
  | .loop l => StackCall.stmt loopCode Label.loop (.emit 0 (.copy .emit))
      getLoop putLoop (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.program l)
  | .emit i l => StackCall.stmt writeCode (Label.emit i) (nextEmit i)
      getIO putIO (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareWriter.program (writeSrc i) l)
  | .drain i l => StackCall.stmt (drainCode i) (Label.drain i) (nextDrain i)
      getIO putIO (Normalization.drainProgram l)
  | .output l => StackCall.stmt outputCode Label.output .done getIO putIO (transferProgram l)
  | .done => .load (fun _ => default) .halt

def input (k : ℕ) (qN qD sN sD : Bits) : Bits :=
  framed k.bits ++ (framed qN ++ (framed qD ++ (framed sN ++ framed sD)))

def data (qN qD sN sD : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data :=
  ⟨[],[],Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.denominator qD sN,
    false::false::Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD,[]⟩

def output (k : ℕ) (qN qD sN sD : Bits) : Bits :=
  framed sN ++ (framed sD ++ framed (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) (data qN qD sN sD)).a))

theorem data_models (qN qD sN sD : Bits) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Models (binaryValue qD*(binaryValue sN)^2)
      (TrialEmit.mInit (binaryValue qN*(binaryValue sD)^2)) (data qN qD sN sD) := by
  have hP :=
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.result_value qN qD sN sD).1
  have hQ :=
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.result_value qN qD sN sD).2
  change binaryValue
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD)=_ at hP
  change binaryValue
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.denominator qD sN)=_ at hQ
  refine ⟨rfl,rfl,hQ,?_,rfl⟩
  change 2*(2*binaryValue (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD))=
    4*(binaryValue qN*(binaryValue sD)^2)
  rw [hP]
  ring

theorem output_value (k : ℕ) (qN qD sN sD : Bits) :
    binaryValue (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) (data qN qD sN sD)).a)=
      intBisect (binaryValue qN*(binaryValue sD)^2) (binaryValue qD*(binaryValue sN)^2) k := by
  have h :=
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.models_iterate (data_models qN qD sN sD) k).2.2.2.2
  exact h.trans (TrialEmit.mIterate_intBisect _ _ k)

theorem output_precision (k : ℕ) (qN qD sN sD : Bits) :
    (((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) (data qN qD sN sD)).a).length=k := by
  simpa only [data,List.length_nil,Nat.zero_add] using!
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.iterate_a_length k (data qN qD sN sD)

def readFrame (word : Bits) : Option (Bits × Bits) := do
  let (n,rest) ← Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat word
  if n≤rest.length then some (rest.take n,rest.drop n) else none

theorem readFrame_complete (bits tail : Bits) :
    readFrame (framed bits++tail)=some (bits,tail) := by
  unfold readFrame Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed
  rw [List.append_assoc,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat_complete]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [if_pos (show bits.length≤(bits++tail).length by simp only [List.length_append]; omega)]
  rw [take_append_length,drop_append_length]

def decode (word : Bits) : Option (ℚ × ℚ) := do
  let (sn,tail₁) ← readFrame word
  let (sd,tail₂) ← readFrame tail₁
  let (a,tail₃) ← readFrame tail₂
  if tail₃=[] ∧ 0<binaryValue sd then
    let S : ℚ := (binaryValue sn : ℚ)/(binaryValue sd : ℚ)
    some (S*((binaryValue a : ℚ)/2^a.length),S*(((binaryValue a : ℚ)+1)/2^a.length))
  else none

theorem decode_frames (sn sd a : Bits) (hD : 0<binaryValue sd) :
    decode (framed sn++(framed sd++framed a))=
      some (((binaryValue sn : ℚ)/(binaryValue sd : ℚ))*((binaryValue a : ℚ)/2^a.length),
        ((binaryValue sn : ℚ)/(binaryValue sd : ℚ))*(((binaryValue a : ℚ)+1)/2^a.length)) := by
  have hA := readFrame_complete a ([] : Bits)
  simp only [List.append_nil] at hA
  simp only [decode,readFrame_complete,hA,Option.bind_eq_bind,Option.bind_some,hD,and_true,↓reduceIte]

def rationalInput (q S : ℚ) (k : ℕ) : Bits :=
  input k q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits

def rationalOutput (q S : ℚ) (k : ℕ) : Bits :=
  output k q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits

theorem rationalOutput_decodes (q S : ℚ) (k : ℕ) (hq : 0≤q) (hS : 0<S) :
    decode (rationalOutput q S k)=some (sqrtLo q S k,sqrtHi q S k) := by
  let a :=
      ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.next^[k]) (data q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits)).a
  have hD : 0<binaryValue S.den.bits := by
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    exact S.den_pos
  have ha : binaryValue a=intBisect (sqNum q S) (sqDen q S) k := by
    have h := output_value k q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits
    simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,sqNum,sqDen,pow_two,Nat.mul_assoc] using! h
  have hlen : a.length=k := output_precision k _ _ _ _
  have hscale : (binaryValue S.num.natAbs.bits : ℚ)/(binaryValue S.den.bits : ℚ)=S := by
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      cast_natAbs_num_of_nonneg S hS.le,Rat.num_div_den]
  change decode (framed S.num.natAbs.bits++(framed S.den.bits++framed a))=_
  rw [decode_frames _ _ _ hD,hscale,ha,hlen,sqrtLo_eq_intBisect q S hq hS,
    sqrtHi_eq_intBisect q S hq hS]

theorem rationalOutput_certified (q S : ℚ) (k : ℕ) (hq : 0≤q) (hS : 0<S) (hSq : q≤S*S) :
    ∃ lo hi : ℚ, decode (rationalOutput q S k)=some (lo,hi) ∧
      0≤lo ∧ lo≤hi ∧ hi≤S ∧ lo^2≤q ∧ q≤hi^2 ∧ hi-lo=S/2^k := by
  refine ⟨sqrtLo q S k,sqrtHi q S k,rationalOutput_decodes q S k hq hS,?_⟩
  have h := sqrtInterval_certified q S k hS hq hSq
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt
