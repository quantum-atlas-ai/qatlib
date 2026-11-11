/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Gaussian rational arithmetic and word expressions

This file represents signed numerators by `Difference` and Gaussian rationals by `GaussianRat`
and `GaussianCode`. The decoding lemmas show that code-level conjugation, addition, and
multiplication agree with their rational semantics when the required denominators are positive.

The word machine `SqRationalMachineCost.Instruction` and its expression compiler provide
executable arithmetic on binary words. `SqRationalMachineCost.Expression.compile_run` describes
stack execution, and `Expression.word_value` connects word evaluation to natural-number
evaluation. For general background on classical and quantum computation, see
[KitaevShenVyalyi2002].

## Main statements

* `GaussianCode.decode_add`: decoding preserves addition of valid codes.
* `GaussianCode.decode_mul`: decoding preserves multiplication of valid codes.
* `Expression.compile_run`: execution of compiled natural-number expressions.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002], *Classical and Quantum Computation*.
-/

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

/-- A formal difference of two natural numbers. -/
structure Difference where
  positive : ℕ
  negative : ℕ
  deriving DecidableEq, Repr

namespace Difference

/-- The rational value obtained by subtracting the negative component from the positive
component. -/
def value (x : Difference) : ℚ := (x.positive : ℚ)-x.negative

/-- Add two formal differences componentwise. -/
def add (x y : Difference) : Difference :=
  ⟨x.positive+y.positive,x.negative+y.negative⟩
/-- Negate a formal difference by exchanging its components. -/
def neg (x : Difference) : Difference := ⟨x.negative,x.positive⟩
/-- Multiply both components of a formal difference by a natural number. -/
def scale (n : ℕ) (x : Difference) : Difference := ⟨n*x.positive,n*x.negative⟩
/-- Multiply formal differences by distributing products into positive and negative components. -/
def mul (x y : Difference) : Difference :=
  ⟨x.positive*y.positive+x.negative*y.negative,
    x.positive*y.negative+x.negative*y.positive⟩

/-- The value of the sum of two formal differences is the sum of their values. -/
theorem add_value (x y : Difference) : (add x y).value = x.value+y.value := by
  simp only [value,add,Nat.cast_add]
  ring

/-- Exchanging the components of a formal difference negates its value. -/
theorem neg_value (x : Difference) : (neg x).value = -x.value := by
  simp only [value,neg]
  ring

/-- Scaling a formal difference by `n` multiplies its value by the rational cast of `n`. -/
theorem scale_value (n : ℕ) (x : Difference) : (scale n x).value = (n:ℚ)*x.value := by
  simp only [value,scale,Nat.cast_mul]
  ring

/-- The value of the product of two formal differences is the product of their values. -/
theorem mul_value (x y : Difference) : (mul x y).value = x.value*y.value := by
  simp only [value,mul,Nat.cast_add,Nat.cast_mul]
  ring
end Difference

/-- A complex number specified by rational real and imaginary parts. -/
@[ext] structure GaussianRat where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace GaussianRat

/-- The Gaussian rational with both components equal to zero. -/
def zero : GaussianRat := ⟨0,0⟩
/-- The Gaussian rational with real part one and imaginary part zero. -/
def one : GaussianRat := ⟨1,0⟩
/-- Add Gaussian rationals componentwise. -/
def add (x y : GaussianRat) : GaussianRat := ⟨x.re+y.re,x.im+y.im⟩
/-- Negate both components of a Gaussian rational. -/
def neg (x : GaussianRat) : GaussianRat := ⟨-x.re,-x.im⟩
/-- Conjugate a Gaussian rational by negating its imaginary part. -/
def conjugate (x : GaussianRat) : GaussianRat := ⟨x.re,-x.im⟩
/-- Multiply Gaussian rationals using the usual complex multiplication formula. -/
def mul (x y : GaussianRat) : GaussianRat :=
  ⟨x.re*y.re-x.im*y.im,x.re*y.im+x.im*y.re⟩
/-- Interpret rational real and imaginary parts as a complex number. -/
def toComplex (x : GaussianRat) : ℂ := ⟨x.re,x.im⟩

/-- Interpretation in the complex numbers preserves Gaussian rational addition. -/
theorem toComplex_add (x y : GaussianRat) : (add x y).toComplex = x.toComplex+y.toComplex := by
  apply Complex.ext <;> simp [toComplex,add]

/-- Interpretation in the complex numbers preserves Gaussian rational multiplication. -/
theorem toComplex_mul (x y : GaussianRat) : (mul x y).toComplex = x.toComplex*y.toComplex := by
  apply Complex.ext <;> simp [toComplex,mul,Complex.mul_re,Complex.mul_im]

/-- Interpretation in the complex numbers sends Gaussian rational conjugation to complex
conjugation. -/
theorem toComplex_conjugate (x : GaussianRat) : (conjugate x).toComplex = star x.toComplex := by
  apply Complex.ext <;> simp [toComplex,conjugate]
end GaussianRat

/-- A representation of a Gaussian rational by two formal differences and a shared natural
denominator. Positivity of the denominator is expressed separately by `GaussianCode.Valid`. -/
structure GaussianCode where
  realPart : Difference
  imagPart : Difference
  denominator : ℕ
  deriving DecidableEq, Repr

namespace GaussianCode

/-- A Gaussian code is valid when its denominator is positive. -/
def Valid (x : GaussianCode) : Prop := 0 < x.denominator

/-- Decode a Gaussian code by dividing the values of its real and imaginary numerators by its
denominator. -/
def decode (x : GaussianCode) : GaussianRat :=
  ⟨x.realPart.value/x.denominator,x.imagPart.value/x.denominator⟩
/-- A Gaussian code for zero with denominator one. -/
def zero : GaussianCode := ⟨⟨0,0⟩,⟨0,0⟩,1⟩
/-- A Gaussian code for one with denominator one. -/
def one : GaussianCode := ⟨⟨1,0⟩,⟨0,0⟩,1⟩
/-- Conjugate a Gaussian code by negating its imaginary numerator. -/
def conjugate (x : GaussianCode) : GaussianCode := ⟨x.realPart,x.imagPart.neg,x.denominator⟩
/-- Add Gaussian codes by scaling their numerators to the product of their denominators. -/
def add (x y : GaussianCode) : GaussianCode :=
  ⟨(x.realPart.scale y.denominator).add (y.realPart.scale x.denominator),
    (x.imagPart.scale y.denominator).add (y.imagPart.scale x.denominator),
    x.denominator*y.denominator⟩
/-- Multiply Gaussian codes using complex multiplication on their formal-difference numerators
and multiplying their denominators. -/
def mul (x y : GaussianCode) : GaussianCode :=
  ⟨(x.realPart.mul y.realPart).add ((x.imagPart.mul y.imagPart).neg),
    (x.realPart.mul y.imagPart).add (x.imagPart.mul y.realPart),
    x.denominator*y.denominator⟩

/-- Conjugation preserves validity of a Gaussian code. -/
theorem conjugate_valid (x : GaussianCode) (hx : x.Valid) : (conjugate x).Valid := hx

/-- Addition preserves validity of Gaussian codes. -/
theorem add_valid (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) : (add x y).Valid :=
  Nat.mul_pos hx hy

/-- Multiplication preserves validity of Gaussian codes. -/
theorem mul_valid (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) : (mul x y).Valid :=
  Nat.mul_pos hx hy

/-- Decoding a conjugated Gaussian code gives the conjugate of its decoded value. -/
theorem decode_conjugate (x : GaussianCode) : (conjugate x).decode = x.decode.conjugate := by
  cases x
  simp [decode,conjugate,GaussianRat.conjugate,Difference.neg_value,neg_div]

/-- Decoding the sum of valid Gaussian codes gives the sum of their decoded values. -/
theorem decode_add (x y : GaussianCode) (hx : x.Valid) (hy : y.Valid) :
    (add x y).decode = x.decode.add y.decode := by
  have hx0 : (x.denominator : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy0 : (y.denominator : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  apply GaussianRat.ext
  all_goals simp only [decode,add,GaussianRat.add,Difference.add_value,Difference.scale_value,Nat.cast_mul]
  all_goals field_simp [hx0,hy0]

/-- Decoding the product of valid Gaussian codes gives the product of their decoded values. -/
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

/-- Instructions for a word stack machine with literals, parameter reads, arithmetic, and
storage. -/
inductive Instruction where
  | literal (payload : Bits)
  | parameter (index : ℕ)
  | add
  | multiply
  | store
  deriving DecidableEq, Repr

namespace Instruction

/-- Encode an instruction with a three-bit tag and a framed payload when required. -/
def code : Instruction → Bits
  | .literal bits => [false,false,false] ++ framed bits
  | .parameter i => [false,false,true] ++ framed i.bits
  | .add => [false,true,false]
  | .multiply => [false,true,true]
  | .store => [true,false,false]
end Instruction

/-- Encode a program by concatenating its instruction encodings. -/
def programCode (p : List Instruction) : Bits := p.flatMap Instruction.code

/-- Serialize a list of words by concatenating their framed encodings. -/
def valueStack (values : List Bits) : Bits := values.flatMap framed

/-- A word machine state consisting of a parameter list and a value stack. -/
structure WordState where
  parameters : List Bits
  values : List Bits
  deriving DecidableEq, Repr

/-- Execute one word instruction, returning `none` if the value stack has too few operands.
Parameter reads outside the list yield the empty word, and storage appends the top word to
the parameter list. -/
def execute : Instruction → WordState → Option WordState
  | .literal bits,s => some ⟨s.parameters,bits::s.values⟩
  | .parameter i,s => some ⟨s.parameters,(s.parameters.getD i [])::s.values⟩
  | .add,⟨ps,b::a::rest⟩ => some ⟨ps,bitAdd a b::rest⟩
  | .multiply,⟨ps,b::a::rest⟩ => some ⟨ps,mulAcc a b b.length::rest⟩
  | .store,⟨ps,a::rest⟩ => some ⟨ps++[a],rest⟩
  | _,_ => none

/-- Execute a list of word instructions, propagating failure from any instruction. -/
def run : List Instruction → WordState → Option WordState
  | [],s => some s
  | op::rest,s => (execute op s).bind (run rest)

/-- Running concatenated programs is the sequential composition of their runs. -/
theorem run_append (p q : List Instruction) (s : WordState) :
    run (p++q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => rfl
  | cons op p ih =>
    simp only [List.cons_append,run]
    cases he : execute op s <;> simp [ih]

/-- Natural-number expressions built from binary literals, parameter reads, addition, and
multiplication. -/
inductive Expression where
  | literal (bits : Bits)
  | parameter (index : ℕ)
  | add (x y : Expression)
  | multiply (x y : Expression)
  deriving DecidableEq, Repr

namespace Expression

/-- Compile an expression to stack instructions in left-to-right evaluation order. -/
def compile : Expression → List Instruction
  | .literal bits => [.literal bits]
  | .parameter i => [.parameter i]
  | .add x y => x.compile ++ y.compile ++ [.add]
  | .multiply x y => x.compile ++ y.compile ++ [.multiply]

/-- Evaluate an expression as a bit word using word addition and multiplication. Parameter reads
outside the list yield the empty word. -/
def word (parameters : List Bits) : Expression → Bits
  | .literal bits => bits
  | .parameter i => parameters.getD i []
  | .add x y => bitAdd (word parameters x) (word parameters y)
  | .multiply x y => mulAcc (word parameters x) (word parameters y) (word parameters y).length

/-- Evaluate an expression in natural numbers, interpreting literal words by `binaryValue` and
missing parameters as zero. -/
def eval (parameters : List ℕ) : Expression → ℕ
  | .literal bits => binaryValue bits
  | .parameter i => parameters.getD i 0
  | .add x y => eval parameters x+eval parameters y
  | .multiply x y => eval parameters x*eval parameters y

/-- Running a compiled expression pushes its word value onto the stack and preserves the
parameters. -/
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

/-- Decoding a word parameter read agrees with reading the corresponding natural-number
parameter, including the default value. -/
theorem parameter_value (ps : List Bits) (i : ℕ) :
    binaryValue (ps.getD i []) = (ps.map binaryValue).getD i 0 := by
  simp only [List.getD,List.getElem?_map]
  cases ps[i]? <;> rfl

/-- The binary value of word evaluation equals natural-number evaluation on the decoded
parameters. -/
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

/-- Compile an expression followed by an instruction that appends its result to the parameter
list. -/
def append (e : Expression) : List Instruction := e.compile ++ [.store]

/-- Running the append program adds the expression's word value to the parameter list and
restores the original value stack. -/
theorem append_run (e : Expression) (ps stack : List Bits) :
    run (Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression.append e) ⟨ps,stack⟩ = some ⟨ps++[e.word ps],stack⟩ := by
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression.append,run_append,compile_run]
  rfl
end Qatlib.Concepts.AdversaryBounds.AdvDuality.Expression
