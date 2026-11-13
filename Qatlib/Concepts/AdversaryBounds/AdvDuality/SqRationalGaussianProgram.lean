/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalArithmetic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExt

/-!
# Gaussian expressions and their word programs

This file builds `GaussianExpression` from five natural-number expressions, using
`DifferenceExpression` for signed numerators. Literal construction, conjugation, addition, and
multiplication commute with evaluation to `GaussianCode`.

`GaussianExpression.compile_run` and `GaussianExpression.append_run` describe the corresponding
stack and parameter-list behavior. `decodeGaussian` and `GaussianExpression.decode_words`
connect framed output words to evaluated Gaussian codes. For general background on the
computational setting, see [KitaevShenVyalyi2002].

## Main statements

* `GaussianExpression.compile_run`: stack execution of Gaussian expressions.
* `GaussianExpression.append_run`: storing the five result words.
* `GaussianExpression.decode_words`: decoding framed expression results.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002], *Classical and Quantum Computation*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
/-- A formal difference whose positive and negative components are natural-number expressions. -/
structure DifferenceExpression where
  positive : Expression
  negative : Expression
  deriving DecidableEq, Repr

namespace DifferenceExpression

/-- Evaluate the two components of a difference expression to obtain a formal difference. -/
def eval (e : DifferenceExpression) (ps : List ℕ) : Difference :=
  ⟨e.positive.eval ps,e.negative.eval ps⟩
/-- Construct componentwise addition of difference expressions. -/
def add (x y : DifferenceExpression) : DifferenceExpression :=
  ⟨.add x.positive y.positive,.add x.negative y.negative⟩
/-- Negate a difference expression by exchanging its positive and negative components. -/
def neg (x : DifferenceExpression) : DifferenceExpression := ⟨x.negative,x.positive⟩
/-- Scale both components of a difference expression by a natural-number expression. -/
def scale (n : Expression) (x : DifferenceExpression) : DifferenceExpression :=
  ⟨.multiply n x.positive,.multiply n x.negative⟩
/-- Construct multiplication of difference expressions by distributing products into positive
and negative components. -/
def mul (x y : DifferenceExpression) : DifferenceExpression :=
  ⟨.add (.multiply x.positive y.positive) (.multiply x.negative y.negative),
    .add (.multiply x.positive y.negative) (.multiply x.negative y.positive)⟩

end DifferenceExpression

/-- Five natural-number expressions specifying the two signed numerators and denominator of a
Gaussian code. -/
structure GaussianExpression where
  realPositive : Expression
  realNegative : Expression
  imagPositive : Expression
  imagNegative : Expression
  denominator : Expression
  deriving DecidableEq, Repr

namespace GaussianExpression

/-- Evaluate the five component expressions to obtain a Gaussian code. -/
def eval (e : GaussianExpression) (ps : List ℕ) : GaussianCode :=
  ⟨⟨e.realPositive.eval ps,e.realNegative.eval ps⟩,
    ⟨e.imagPositive.eval ps,e.imagNegative.eval ps⟩,e.denominator.eval ps⟩

/-- Evaluate the five component expressions as words, ordered as real positive, real negative,
imaginary positive, imaginary negative, and denominator. -/
def words (e : GaussianExpression) (ps : List Bits) : List Bits :=
  [e.realPositive.word ps,e.realNegative.word ps,e.imagPositive.word ps,
    e.imagNegative.word ps,e.denominator.word ps]

/-- Extract the formal-difference expression for the real numerator. -/
def real (e : GaussianExpression) : DifferenceExpression := ⟨e.realPositive,e.realNegative⟩
/-- Extract the formal-difference expression for the imaginary numerator. -/
def imag (e : GaussianExpression) : DifferenceExpression := ⟨e.imagPositive,e.imagNegative⟩
/-- Assemble a Gaussian expression from its real numerator, imaginary numerator, and denominator
expressions. -/
def ofParts (r i : DifferenceExpression) (d : Expression) : GaussianExpression :=
  ⟨r.positive,r.negative,i.positive,i.negative,d⟩

/-- Construct a Gaussian expression from literal words encoding the five fields of a Gaussian
code. -/
def literal (x : GaussianCode) : GaussianExpression :=
  ⟨.literal x.realPart.positive.bits,.literal x.realPart.negative.bits,
    .literal x.imagPart.positive.bits,.literal x.imagPart.negative.bits,.literal x.denominator.bits⟩

/-- Read a Gaussian code from five consecutive natural-number parameters starting at `base`. -/
def parameter (base : ℕ) : GaussianExpression :=
  ⟨.parameter base,.parameter (base+1),.parameter (base+2),.parameter (base+3),.parameter (base+4)⟩

/-- Construct conjugation by negating the imaginary numerator expression. -/
def conjugate (e : GaussianExpression) : GaussianExpression :=
    ofParts e.real e.imag.neg e.denominator

/-- Construct Gaussian addition by scaling numerator expressions to the product of the
denominator expressions. -/
def add (x y : GaussianExpression) : GaussianExpression :=
  ofParts ((x.real.scale y.denominator).add (y.real.scale x.denominator))
    ((x.imag.scale y.denominator).add (y.imag.scale x.denominator))
    (.multiply x.denominator y.denominator)

/-- Construct Gaussian multiplication using complex multiplication on numerator expressions and
multiplying the denominator expressions. -/
def mul (x y : GaussianExpression) : GaussianExpression :=
  ofParts ((x.real.mul y.real).add ((x.imag.mul y.imag).neg))
    ((x.real.mul y.imag).add (x.imag.mul y.real)) (.multiply x.denominator y.denominator)

/-- Evaluating a literal Gaussian expression returns the original Gaussian code. -/
theorem eval_literal (x : GaussianCode) (ps : List ℕ) : (literal x).eval ps=x := by
  simp only [literal,eval,Expression.eval,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]

/-- Evaluation commutes with conjugation of Gaussian expressions. -/
theorem eval_conjugate (x : GaussianExpression) (ps : List ℕ) :
    (conjugate x).eval ps=GaussianCode.conjugate (x.eval ps) := rfl

/-- Evaluation commutes with addition of Gaussian expressions. -/
theorem eval_add (x y : GaussianExpression) (ps : List ℕ) :
    (add x y).eval ps=GaussianCode.add (x.eval ps) (y.eval ps) := rfl

/-- Evaluation commutes with multiplication of Gaussian expressions. -/
theorem eval_mul (x y : GaussianExpression) (ps : List ℕ) :
    (mul x y).eval ps=GaussianCode.mul (x.eval ps) (y.eval ps) := rfl

/-- Compile the five component expressions in reverse field order so that their words appear in
field order on the stack. -/
def compile (e : GaussianExpression) : List Instruction :=
  e.denominator.compile++e.imagNegative.compile++e.imagPositive.compile++
    e.realNegative.compile++e.realPositive.compile

/-- Running a compiled Gaussian expression pushes its five words in field order and preserves
the parameters. -/
theorem compile_run (e : GaussianExpression) (ps stack : List Bits) :
    run e.compile ⟨ps,stack⟩=some ⟨ps,e.words ps++stack⟩ := by
  simp only [compile,run_append,Expression.compile_run,Option.bind_some,words,
    List.cons_append,List.nil_append]

/-- Compile a Gaussian expression followed by five store instructions. -/
def append (e : GaussianExpression) : List Instruction :=
  e.compile++[.store,.store,.store,.store,.store]

/-- Running the append program appends the expression's five words to the parameters and
restores the original value stack. -/
theorem append_run (e : GaussianExpression) (ps stack : List Bits) :
    run e.append ⟨ps,stack⟩=some ⟨ps++e.words ps,stack⟩ := by
  rw [append,run_append,compile_run]
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,words,List.append_assoc]
end GaussianExpression

/-- Read five framed words as the fields of a Gaussian code and return the unconsumed input. -/
def decodeGaussian (input : Bits) : GaussianCode × Bits :=
  let rp := frameSplit input
  let rn := frameSplit rp.2
  let ip := frameSplit rn.2
  let inn := frameSplit ip.2
  let den := frameSplit inn.2
  (⟨⟨binaryValue rp.1,binaryValue rn.1⟩,
    ⟨binaryValue ip.1,binaryValue inn.1⟩,binaryValue den.1⟩,den.2)

/-- Decoding five framed field words recovers their binary values as a Gaussian code and leaves
the following input unchanged. -/
theorem decodeGaussian_fields (rp rn ip inn den tail : Bits) :
    decodeGaussian (valueStack [rp,rn,ip,inn,den]++tail)=
      (⟨⟨binaryValue rp,binaryValue rn⟩,⟨binaryValue ip,binaryValue inn⟩,binaryValue den⟩,tail) := by
  simp only [decodeGaussian,valueStack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.append_assoc,frameSplit_framed]

/-- Decoding the framed words of a Gaussian expression gives its evaluation on decoded
parameters and leaves the following input unchanged. -/
theorem GaussianExpression.decode_words (e : GaussianExpression) (ps : List Bits) (tail : Bits) :
    decodeGaussian (valueStack (e.words ps)++tail)=(e.eval (ps.map binaryValue),tail) := by
  simp only [GaussianExpression.words,decodeGaussian_fields,Expression.word_value,GaussianExpression.eval]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
