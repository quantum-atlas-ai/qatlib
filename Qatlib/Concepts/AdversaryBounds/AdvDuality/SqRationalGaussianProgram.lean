/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalArithmetic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
structure DifferenceExpression where
  positive : Expression
  negative : Expression
  deriving DecidableEq, Repr

namespace DifferenceExpression

def eval (e : DifferenceExpression) (ps : List ℕ) : Difference :=
  ⟨e.positive.eval ps,e.negative.eval ps⟩
def add (x y : DifferenceExpression) : DifferenceExpression :=
  ⟨.add x.positive y.positive,.add x.negative y.negative⟩
def neg (x : DifferenceExpression) : DifferenceExpression := ⟨x.negative,x.positive⟩
def scale (n : Expression) (x : DifferenceExpression) : DifferenceExpression :=
  ⟨.multiply n x.positive,.multiply n x.negative⟩
def mul (x y : DifferenceExpression) : DifferenceExpression :=
  ⟨.add (.multiply x.positive y.positive) (.multiply x.negative y.negative),
    .add (.multiply x.positive y.negative) (.multiply x.negative y.positive)⟩

end DifferenceExpression

structure GaussianExpression where
  realPositive : Expression
  realNegative : Expression
  imagPositive : Expression
  imagNegative : Expression
  denominator : Expression
  deriving DecidableEq, Repr

namespace GaussianExpression

def eval (e : GaussianExpression) (ps : List ℕ) : GaussianCode :=
  ⟨⟨e.realPositive.eval ps,e.realNegative.eval ps⟩,
    ⟨e.imagPositive.eval ps,e.imagNegative.eval ps⟩,e.denominator.eval ps⟩

def words (e : GaussianExpression) (ps : List Bits) : List Bits :=
  [e.realPositive.word ps,e.realNegative.word ps,e.imagPositive.word ps,
    e.imagNegative.word ps,e.denominator.word ps]

def real (e : GaussianExpression) : DifferenceExpression := ⟨e.realPositive,e.realNegative⟩
def imag (e : GaussianExpression) : DifferenceExpression := ⟨e.imagPositive,e.imagNegative⟩
def ofParts (r i : DifferenceExpression) (d : Expression) : GaussianExpression :=
  ⟨r.positive,r.negative,i.positive,i.negative,d⟩

def literal (x : GaussianCode) : GaussianExpression :=
  ⟨.literal x.realPart.positive.bits,.literal x.realPart.negative.bits,
    .literal x.imagPart.positive.bits,.literal x.imagPart.negative.bits,.literal x.denominator.bits⟩

def parameter (base : ℕ) : GaussianExpression :=
  ⟨.parameter base,.parameter (base+1),.parameter (base+2),.parameter (base+3),.parameter (base+4)⟩

def conjugate (e : GaussianExpression) : GaussianExpression :=
    ofParts e.real e.imag.neg e.denominator

def add (x y : GaussianExpression) : GaussianExpression :=
  ofParts ((x.real.scale y.denominator).add (y.real.scale x.denominator))
    ((x.imag.scale y.denominator).add (y.imag.scale x.denominator))
    (.multiply x.denominator y.denominator)

def mul (x y : GaussianExpression) : GaussianExpression :=
  ofParts ((x.real.mul y.real).add ((x.imag.mul y.imag).neg))
    ((x.real.mul y.imag).add (x.imag.mul y.real)) (.multiply x.denominator y.denominator)

theorem eval_literal (x : GaussianCode) (ps : List ℕ) : (literal x).eval ps=x := by
  simp only [literal,eval,Expression.eval,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]

theorem eval_conjugate (x : GaussianExpression) (ps : List ℕ) :
    (conjugate x).eval ps=GaussianCode.conjugate (x.eval ps) := rfl

theorem eval_add (x y : GaussianExpression) (ps : List ℕ) :
    (add x y).eval ps=GaussianCode.add (x.eval ps) (y.eval ps) := rfl

theorem eval_mul (x y : GaussianExpression) (ps : List ℕ) :
    (mul x y).eval ps=GaussianCode.mul (x.eval ps) (y.eval ps) := rfl

def compile (e : GaussianExpression) : List Instruction :=
  e.denominator.compile++e.imagNegative.compile++e.imagPositive.compile++
    e.realNegative.compile++e.realPositive.compile

theorem compile_run (e : GaussianExpression) (ps stack : List Bits) :
    run e.compile ⟨ps,stack⟩=some ⟨ps,e.words ps++stack⟩ := by
  simp only [compile,run_append,Expression.compile_run,Option.bind_some,words,
    List.cons_append,List.nil_append]

def append (e : GaussianExpression) : List Instruction :=
  e.compile++[.store,.store,.store,.store,.store]

theorem append_run (e : GaussianExpression) (ps stack : List Bits) :
    run e.append ⟨ps,stack⟩=some ⟨ps++e.words ps,stack⟩ := by
  rw [append,run_append,compile_run]
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,words,List.append_assoc]
end GaussianExpression

def decodeGaussian (input : Bits) : GaussianCode × Bits :=
  let rp := frameSplit input
  let rn := frameSplit rp.2
  let ip := frameSplit rn.2
  let inn := frameSplit ip.2
  let den := frameSplit inn.2
  (⟨⟨binaryValue rp.1,binaryValue rn.1⟩,
    ⟨binaryValue ip.1,binaryValue inn.1⟩,binaryValue den.1⟩,den.2)

theorem decodeGaussian_fields (rp rn ip inn den tail : Bits) :
    decodeGaussian (valueStack [rp,rn,ip,inn,den]++tail)=
      (⟨⟨binaryValue rp,binaryValue rn⟩,⟨binaryValue ip,binaryValue inn⟩,binaryValue den⟩,tail) := by
  simp only [decodeGaussian,valueStack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.append_assoc,frameSplit_framed]

theorem GaussianExpression.decode_words (e : GaussianExpression) (ps : List Bits) (tail : Bits) :
    decodeGaussian (valueStack (e.words ps)++tail)=(e.eval (ps.map binaryValue),tail) := by
  simp only [GaussianExpression.words,decodeGaussian_fields,Expression.word_value,GaussianExpression.eval]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
