/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib
open scoped BigOperators

structure Difference where
  positive : ℕ
  negative : ℕ
  deriving DecidableEq, Repr

namespace Difference

def value (x : Difference) : ℚ := (x.positive : ℚ)-x.negative

def add (x y : Difference) : Difference :=
  ⟨x.positive+y.positive,x.negative+y.negative⟩
def neg (x : Difference) : Difference := ⟨x.negative,x.positive⟩
def scale (n : ℕ) (x : Difference) : Difference := ⟨n*x.positive,n*x.negative⟩
def mul (x y : Difference) : Difference :=
  ⟨x.positive*y.positive+x.negative*y.negative,
    x.positive*y.negative+x.negative*y.positive⟩

theorem add_value (x y : Difference) : (add x y).value = x.value+y.value := by
  simp only [value,add,Nat.cast_add]
  ring

theorem neg_value (x : Difference) : (neg x).value = -x.value := by
  simp only [value,neg]
  ring

theorem scale_value (n : ℕ) (x : Difference) : (scale n x).value = (n:ℚ)*x.value := by
  simp only [value,scale,Nat.cast_mul]
  ring

theorem mul_value (x y : Difference) : (mul x y).value = x.value*y.value := by
  simp only [value,mul,Nat.cast_add,Nat.cast_mul]
  ring
end Difference

@[ext] structure GaussianRat where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace GaussianRat

def zero : GaussianRat := ⟨0,0⟩
def one : GaussianRat := ⟨1,0⟩
def add (x y : GaussianRat) : GaussianRat := ⟨x.re+y.re,x.im+y.im⟩
def neg (x : GaussianRat) : GaussianRat := ⟨-x.re,-x.im⟩
def conjugate (x : GaussianRat) : GaussianRat := ⟨x.re,-x.im⟩
def mul (x y : GaussianRat) : GaussianRat :=
  ⟨x.re*y.re-x.im*y.im,x.re*y.im+x.im*y.re⟩
def toComplex (x : GaussianRat) : ℂ := ⟨x.re,x.im⟩

theorem toComplex_add (x y : GaussianRat) : (add x y).toComplex = x.toComplex+y.toComplex := by
  apply Complex.ext <;> simp [toComplex,add]

theorem toComplex_mul (x y : GaussianRat) : (mul x y).toComplex = x.toComplex*y.toComplex := by
  apply Complex.ext <;> simp [toComplex,mul,Complex.mul_re,Complex.mul_im]

theorem toComplex_conjugate (x : GaussianRat) : (conjugate x).toComplex = star x.toComplex := by
  apply Complex.ext <;> simp [toComplex,conjugate]
end GaussianRat

structure GaussianCode where
  realPart : Difference
  imagPart : Difference
  denominator : ℕ
  deriving DecidableEq, Repr

namespace GaussianCode

def Valid (x : GaussianCode) : Prop := 0 < x.denominator

def decode (x : GaussianCode) : GaussianRat :=
  ⟨x.realPart.value/x.denominator,x.imagPart.value/x.denominator⟩
def zero : GaussianCode := ⟨⟨0,0⟩,⟨0,0⟩,1⟩
def one : GaussianCode := ⟨⟨1,0⟩,⟨0,0⟩,1⟩
def conjugate (x : GaussianCode) : GaussianCode := ⟨x.realPart,x.imagPart.neg,x.denominator⟩
def add (x y : GaussianCode) : GaussianCode :=
  ⟨(x.realPart.scale y.denominator).add (y.realPart.scale x.denominator),
    (x.imagPart.scale y.denominator).add (y.imagPart.scale x.denominator),
    x.denominator*y.denominator⟩
def mul (x y : GaussianCode) : GaussianCode :=
  ⟨(x.realPart.mul y.realPart).add ((x.imagPart.mul y.imagPart).neg),
    (x.realPart.mul y.imagPart).add (x.imagPart.mul y.realPart),
    x.denominator*y.denominator⟩

theorem conjugate_valid (x : GaussianCode) (hx : x.Valid) : (conjugate x).Valid := hx

theorem add_valid (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) : (add x y).Valid :=
  Nat.mul_pos hx hy

theorem mul_valid (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) : (mul x y).Valid :=
  Nat.mul_pos hx hy

theorem decode_conjugate (x : GaussianCode) : (conjugate x).decode = x.decode.conjugate := by
  cases x
  simp [decode,conjugate,GaussianRat.conjugate,Difference.neg_value,neg_div]

theorem decode_add (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) :
    (add x y).decode = x.decode.add y.decode := by
  have hx0 : (x.denominator : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy0 : (y.denominator : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  apply GaussianRat.ext
  all_goals simp only [decode,add,GaussianRat.add,Difference.add_value,Difference.scale_value,Nat.cast_mul]
  all_goals field_simp [hx0,hy0]

theorem decode_mul (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) :
    (mul x y).decode = x.decode.mul y.decode := by
  have hx0 : (x.denominator : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy0 : (y.denominator : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  apply GaussianRat.ext
  all_goals simp only [decode,mul,GaussianRat.mul,Difference.add_value,Difference.neg_value,
    Difference.mul_value,Nat.cast_mul]
  all_goals field_simp [hx0,hy0]
  all_goals rw [sub_eq_add_neg]
end GaussianCode

end Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

inductive Instruction where
  | literal (payload : Bits)
  | parameter (index : ℕ)
  | add
  | multiply
  | store
  deriving DecidableEq, Repr

namespace Instruction

def code : Instruction → Bits
  | .literal bits => [false,false,false] ++ framed bits
  | .parameter i => [false,false,true] ++ framed i.bits
  | .add => [false,true,false]
  | .multiply => [false,true,true]
  | .store => [true,false,false]
end Instruction

def programCode (p : List Instruction) : Bits := p.flatMap Instruction.code

def valueStack (values : List Bits) : Bits := values.flatMap framed

structure WordState where
  parameters : List Bits
  values : List Bits
  deriving DecidableEq, Repr

def execute : Instruction → WordState → Option WordState
  | .literal bits,s => some ⟨s.parameters,bits::s.values⟩
  | .parameter i,s => some ⟨s.parameters,(s.parameters.getD i [])::s.values⟩
  | .add,⟨ps,b::a::rest⟩ => some ⟨ps,bitAdd a b::rest⟩
  | .multiply,⟨ps,b::a::rest⟩ => some ⟨ps,mulAcc a b b.length::rest⟩
  | .store,⟨ps,a::rest⟩ => some ⟨ps++[a],rest⟩
  | _,_ => none

def run : List Instruction → WordState → Option WordState
  | [],s => some s
  | op::rest,s => (execute op s).bind (run rest)

theorem run_append (p q : List Instruction) (s : WordState) :
    run (p++q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => rfl
  | cons op p ih =>
    simp only [List.cons_append,run]
    cases he : execute op s <;> simp [ih]

inductive Expression where
  | literal (bits : Bits)
  | parameter (index : ℕ)
  | add (x y : Expression)
  | multiply (x y : Expression)
  deriving DecidableEq, Repr

namespace Expression

def compile : Expression → List Instruction
  | .literal bits => [.literal bits]
  | .parameter i => [.parameter i]
  | .add x y => x.compile ++ y.compile ++ [.add]
  | .multiply x y => x.compile ++ y.compile ++ [.multiply]

def word (parameters : List Bits) : Expression → Bits
  | .literal bits => bits
  | .parameter i => parameters.getD i []
  | .add x y => bitAdd (word parameters x) (word parameters y)
  | .multiply x y => mulAcc (word parameters x) (word parameters y) (word parameters y).length

def eval (parameters : List ℕ) : Expression → ℕ
  | .literal bits => binaryValue bits
  | .parameter i => parameters.getD i 0
  | .add x y => eval parameters x+eval parameters y
  | .multiply x y => eval parameters x*eval parameters y

theorem compile_run (e : Expression) (ps stack : List Bits) :
    run e.compile ⟨ps,stack⟩ = some ⟨ps,e.word ps::stack⟩ := by
  induction e generalizing stack with
  | literal bits => rfl
  | parameter i => rfl
  | add x y hx hy =>
    simp only [compile,run_append,hx,Option.bind_some,hy,run,execute,word]
  | multiply x y hx hy =>
    simp only [compile,run_append,hx,Option.bind_some,hy,run,execute,word]
end Expression
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.Expression
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

theorem parameter_value (ps : List Bits) (i : ℕ) :
    binaryValue (ps.getD i []) = (ps.map binaryValue).getD i 0 := by
  simp only [List.getD,List.getElem?_map]
  cases ps[i]? <;> rfl

theorem word_value (e : Expression) (ps : List Bits) :
    binaryValue (e.word ps) = e.eval (ps.map binaryValue) := by
  induction e with
  | literal bits => rfl
  | parameter i => exact parameter_value ps i
  | add x y hx hy =>
    rw [word,bitAdd_value,hx,hy]
    rfl
  | multiply x y hx hy =>
    rw [word,mulAcc_value_full,hx,hy]
    rfl

def append (e : Expression) : List Instruction := e.compile ++ [.store]

theorem append_run (e : Expression) (ps stack : List Bits) :
    run (Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression.append e) ⟨ps,stack⟩ = some ⟨ps++[e.word ps],stack⟩ := by
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression.append,run_append,compile_run]
  rfl
end Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression
