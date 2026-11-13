/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Erased
import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Semantics
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Rational arithmetic kernels for finite table programs

This module binds exact bit-rational routines to the quadratic algebra `Scalar`, with rational
real and imaginary coordinates. `valueKernel` implements addition, multiplication, and
conjugation, while `gateAdd`, `gateMul`, and `gateConj` retain scheduled gate counts. Exact
arithmetic kernels are computational components in the setting of [KitaevShenVyalyi2002].

The value kernel agrees with `algebraKernel Scalar`. The observed gate kernel refines it, so
`gateDriver` returns the same tables as the plain driver and decodes to the specified
finite-tail values.

## Main statements

* `valueKernel_eq_algebra`: the bit-rational value kernel equals the algebraic kernel.
* `gateKernel_refines`: observed arithmetic refines exact scalar arithmetic.
* `gateDriver_value`: metering preserves the plain driver result.
* `gateDriver_decode`: decoding a metered output table gives `tail A v D s`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram

namespace BinomialErased

/-- The erased rational multiplication routine equals rational multiplication. -/
@[simp] theorem ratMul_value (a b : ℚ) : ratMul a b = a*b := by
  rw [ratMul_eq]
  exact (binomial_rat_mul_bits a b).1

/-- The erased rational division routine equals rational division. -/
@[simp] theorem ratDiv_value (a b : ℚ) : ratDiv a b = a/b := by
  rw [ratDiv_eq]
  exact (binomial_rat_div_bits a b).1

/-- The erased rational addition routine equals rational addition. -/
@[simp] theorem ratAdd_value (a b : ℚ) : ratAdd a b = a+b := by
  rw [ratAdd_eq]
  exact (binomial_rat_add_bits a b).1

/-- The erased rational subtraction routine equals rational subtraction. -/
@[simp] theorem ratSub_value (a b : ℚ) : ratSub a b = a-b := by
  rw [ratSub_eq]
  exact (binomial_rat_sub_bits a b).1

/-- The erased signed rational constructor agrees with `mkRat`. -/
@[simp] theorem signed_value (a : ℤ) (d : ℕ) : signed a d = mkRat a d := by
  rw [signed_eq]
  exact (binomial_signed_rat a d).1

end BinomialErased

/-- The quadratic algebra over the rationals with a generator whose square is -1. -/
abbrev Scalar := QuadraticAlgebra ℚ (-1) 0

/-- Adds the real and imaginary rational coordinates using erased rational addition. -/
def valueAdd (x y : Scalar) : Scalar :=
  ⟨BinomialErased.ratAdd x.re y.re, BinomialErased.ratAdd x.im y.im⟩

/-- Keeps the real coordinate and negates the imaginary coordinate using erased rational
subtraction. -/
def valueConj (x : Scalar) : Scalar := ⟨x.re, BinomialErased.ratSub 0 x.im⟩

/-- Multiplies quadratic scalars using four erased rational products and the usual real and
imaginary component formulas. -/
def valueMul (x y : Scalar) : Scalar :=
  let ac := BinomialErased.ratMul x.re y.re
  let bd := BinomialErased.ratMul x.im y.im
  let ad := BinomialErased.ratMul x.re y.im
  let bc := BinomialErased.ratMul x.im y.re
  ⟨BinomialErased.ratSub ac bd, BinomialErased.ratAdd ad bc⟩

/-- The rational-coordinate addition implementation equals addition in `Scalar`. -/
@[simp] theorem valueAdd_eq (x y : Scalar) : valueAdd x y = x+y := by
  ext <;> simp [valueAdd]

/-- The rational-coordinate conjugation implementation equals the star operation on `Scalar`. -/
@[simp] theorem valueConj_eq (x : Scalar) : valueConj x = star x := by
  ext <;> simp [valueConj]

/-- The rational-coordinate multiplication implementation equals multiplication in `Scalar`. -/
@[simp] theorem valueMul_eq (x y : Scalar) : valueMul x y = x*y := by
  ext <;> simp [valueMul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, sub_eq_add_neg]

/-- The finite-table arithmetic kernel with zero, rational-coordinate addition, multiplication,
and conjugation. -/
def valueKernel : Kernel Scalar := ⟨0,valueAdd,valueMul,valueConj⟩

/-- The rational-coordinate value kernel equals the standard algebraic kernel on `Scalar`. -/
theorem valueKernel_eq_algebra : valueKernel = algebraKernel Scalar := by
  unfold valueKernel algebraKernel
  rw [show valueAdd = (fun x y : Scalar => x+y) from funext fun x => funext fun y => valueAdd_eq x y,
    show valueMul = (fun x y : Scalar => x*y) from funext fun x => funext fun y => valueMul_eq x y,
    show valueConj = (star : Scalar → Scalar) from funext valueConj_eq]

/-- Decoding any output table of the plain value-kernel driver yields the corresponding
finite-tail value `tail A v D s`. -/
theorem value_driver_decode {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((Plain.driver valueKernel v A D)[s]) = tail A v D s := by
  rw [valueKernel_eq_algebra]
  exact driver_decode v A D s

/-- Pairs a computed value with its scheduled gate count. -/
structure GateRun (α : Type) where
  value : α
  scheduledGates : ℕ

/-- Adds the real and imaginary coordinates with counted bit-rational routines and sums their
gate counts. -/
def gateAdd (x y : Scalar) : GateRun Scalar :=
  let re := binomialRatAddBits x.re y.re
  let im := binomialRatAddBits x.im y.im
  ⟨⟨re.1,im.1⟩,re.2+im.2⟩

/-- Negates the imaginary coordinate with counted rational subtraction and records its gate
count. -/
def gateConj (x : Scalar) : GateRun Scalar :=
  let im := binomialRatSubBits 0 x.im
  ⟨⟨x.re,im.1⟩,im.2⟩

/-- Multiplies scalar coordinates with four counted rational products and two counted component
combinations, summing all six gate counts. -/
def gateMul (x y : Scalar) : GateRun Scalar :=
  let ac := binomialRatMulBits x.re y.re
  let bd := binomialRatMulBits x.im y.im
  let ad := binomialRatMulBits x.re y.im
  let bc := binomialRatMulBits x.im y.re
  let re := binomialRatSubBits ac.1 bd.1
  let im := binomialRatAddBits ad.1 bc.1
  ⟨⟨re.1,im.1⟩,ac.2+bd.2+ad.2+bc.2+re.2+im.2⟩

/-- The value returned by counted bit-rational multiplication is the exact rational product. -/
@[simp] theorem ratMulBits_value (a b : ℚ) : (binomialRatMulBits a b).1 = a*b :=
  (binomial_rat_mul_bits a b).1

/-- The value returned by counted bit-rational addition is the exact rational sum. -/
@[simp] theorem ratAddBits_value (a b : ℚ) : (binomialRatAddBits a b).1 = a+b :=
  (binomial_rat_add_bits a b).1

/-- The value returned by counted bit-rational subtraction is the exact rational difference. -/
@[simp] theorem ratSubBits_value (a b : ℚ) : (binomialRatSubBits a b).1 = a-b :=
  (binomial_rat_sub_bits a b).1

/-- The value component of counted scalar addition equals scalar addition. -/
@[simp] theorem gateAdd_eq (x y : Scalar) : (gateAdd x y).value = x+y := by
  ext <;> simp [gateAdd]

/-- The value component of counted scalar conjugation equals the star operation. -/
@[simp] theorem gateConj_eq (x : Scalar) : (gateConj x).value = star x := by
  ext <;> simp [gateConj]

/-- The value component of counted scalar multiplication equals scalar multiplication. -/
@[simp] theorem gateMul_eq (x y : Scalar) : (gateMul x y).value = x*y := by
  ext <;> simp [gateMul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, sub_eq_add_neg]

/-- Converts a gate-counted run into a saved-table observation, using scheduled gates as
arithmetic work and setting the other counters to zero. -/
private def observe {α : Type} (r : GateRun α) : Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Observed α :=
  ⟨⟨r.value,r.scheduledGates,0⟩,0⟩

/-- The observed scalar kernel built from gate-counted addition, multiplication, and
conjugation. -/
private def gateKernel : ObservedKernel Scalar where
  zero := 0
  add x y := observe (gateAdd x y)
  mul x y := observe (gateMul x y)
  conj x := observe (gateConj x)

/-- The observed gate kernel refines the standard algebraic kernel on `Scalar`. -/
private theorem gateKernel_refines : Refines (algebraKernel Scalar) gateKernel := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x y; exact gateAdd_eq x y
  · intro x y; exact gateMul_eq x y
  · intro x; exact gateConj_eq x

/-- Runs the metered finite-table driver and returns its table vector with the accumulated
arithmetic work as scheduled gates. -/
def gateDriver {k r : ℕ} (v : Vector Scalar r) (A : Vector (Table Scalar r) k) (D : ℕ) :
    GateRun (Vector (Table Scalar r) (D+1)) :=
  let out := Metered.driver gateKernel v A D
  ⟨out.arithmetic.value,out.arithmetic.work⟩

/-- The value returned by the gate-counted driver equals the plain value-kernel driver output. -/
theorem gateDriver_value {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) :
    (gateDriver v A D).value = Plain.driver valueKernel v A D := by
  rw [valueKernel_eq_algebra]
  exact driver_refines _ _ gateKernel_refines _ _ _

/-- Decoding any output table of the gate-counted driver yields the corresponding finite-tail
value `tail A v D s`. -/
theorem gateDriver_decode {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((gateDriver v A D).value[s]) = tail A v D s := by
  rw [gateDriver_value]
  exact value_driver_decode v A D s

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
