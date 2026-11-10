/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Erased
import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Semantics
import Mathlib.Algebra.QuadraticAlgebra.Basic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram

namespace BinomialErased

@[simp] theorem ratMul_value (a b : ℚ) : ratMul a b = a*b := by
  rw [ratMul_eq]
  exact (binomial_rat_mul_bits a b).1

@[simp] theorem ratDiv_value (a b : ℚ) : ratDiv a b = a/b := by
  rw [ratDiv_eq]
  exact (binomial_rat_div_bits a b).1

@[simp] theorem ratAdd_value (a b : ℚ) : ratAdd a b = a+b := by
  rw [ratAdd_eq]
  exact (binomial_rat_add_bits a b).1

@[simp] theorem ratSub_value (a b : ℚ) : ratSub a b = a-b := by
  rw [ratSub_eq]
  exact (binomial_rat_sub_bits a b).1

@[simp] theorem signed_value (a : ℤ) (d : ℕ) : signed a d = mkRat a d := by
  rw [signed_eq]
  exact (binomial_signed_rat a d).1

end BinomialErased

abbrev Scalar := QuadraticAlgebra ℚ (-1) 0

def valueAdd (x y : Scalar) : Scalar :=
  ⟨BinomialErased.ratAdd x.re y.re, BinomialErased.ratAdd x.im y.im⟩

def valueConj (x : Scalar) : Scalar := ⟨x.re, BinomialErased.ratSub 0 x.im⟩

def valueMul (x y : Scalar) : Scalar :=
  let ac := BinomialErased.ratMul x.re y.re
  let bd := BinomialErased.ratMul x.im y.im
  let ad := BinomialErased.ratMul x.re y.im
  let bc := BinomialErased.ratMul x.im y.re
  ⟨BinomialErased.ratSub ac bd, BinomialErased.ratAdd ad bc⟩

@[simp] theorem valueAdd_eq (x y : Scalar) : valueAdd x y = x+y := by
  ext <;> simp [valueAdd]

@[simp] theorem valueConj_eq (x : Scalar) : valueConj x = star x := by
  ext <;> simp [valueConj]

@[simp] theorem valueMul_eq (x y : Scalar) : valueMul x y = x*y := by
  ext <;> simp [valueMul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, sub_eq_add_neg]

def valueKernel : Kernel Scalar := ⟨0,valueAdd,valueMul,valueConj⟩

theorem valueKernel_eq_algebra : valueKernel = algebraKernel Scalar := by
  unfold valueKernel algebraKernel
  rw [show valueAdd = (fun x y : Scalar => x+y) from funext fun x => funext fun y => valueAdd_eq x y,
    show valueMul = (fun x y : Scalar => x*y) from funext fun x => funext fun y => valueMul_eq x y,
    show valueConj = (star : Scalar → Scalar) from funext valueConj_eq]

theorem value_driver_decode {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((Plain.driver valueKernel v A D)[s]) = tail A v D s := by
  rw [valueKernel_eq_algebra]
  exact driver_decode v A D s

structure GateRun (α : Type) where
  value : α
  scheduledGates : ℕ

def gateAdd (x y : Scalar) : GateRun Scalar :=
  let re := binomialRatAddBits x.re y.re
  let im := binomialRatAddBits x.im y.im
  ⟨⟨re.1,im.1⟩,re.2+im.2⟩

def gateConj (x : Scalar) : GateRun Scalar :=
  let im := binomialRatSubBits 0 x.im
  ⟨⟨x.re,im.1⟩,im.2⟩

def gateMul (x y : Scalar) : GateRun Scalar :=
  let ac := binomialRatMulBits x.re y.re
  let bd := binomialRatMulBits x.im y.im
  let ad := binomialRatMulBits x.re y.im
  let bc := binomialRatMulBits x.im y.re
  let re := binomialRatSubBits ac.1 bd.1
  let im := binomialRatAddBits ad.1 bc.1
  ⟨⟨re.1,im.1⟩,ac.2+bd.2+ad.2+bc.2+re.2+im.2⟩

@[simp] theorem ratMulBits_value (a b : ℚ) : (binomialRatMulBits a b).1 = a*b :=
  (binomial_rat_mul_bits a b).1

@[simp] theorem ratAddBits_value (a b : ℚ) : (binomialRatAddBits a b).1 = a+b :=
  (binomial_rat_add_bits a b).1

@[simp] theorem ratSubBits_value (a b : ℚ) : (binomialRatSubBits a b).1 = a-b :=
  (binomial_rat_sub_bits a b).1

@[simp] theorem gateAdd_eq (x y : Scalar) : (gateAdd x y).value = x+y := by
  ext <;> simp [gateAdd]

@[simp] theorem gateConj_eq (x : Scalar) : (gateConj x).value = star x := by
  ext <;> simp [gateConj]

@[simp] theorem gateMul_eq (x y : Scalar) : (gateMul x y).value = x*y := by
  ext <;> simp [gateMul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, sub_eq_add_neg]

private def observe {α : Type} (r : GateRun α) : Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Observed α :=
  ⟨⟨r.value,r.scheduledGates,0⟩,0⟩

private def gateKernel : ObservedKernel Scalar where
  zero := 0
  add x y := observe (gateAdd x y)
  mul x y := observe (gateMul x y)
  conj x := observe (gateConj x)

private theorem gateKernel_refines : Refines (algebraKernel Scalar) gateKernel := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x y; exact gateAdd_eq x y
  · intro x y; exact gateMul_eq x y
  · intro x; exact gateConj_eq x

def gateDriver {k r : ℕ} (v : Vector Scalar r) (A : Vector (Table Scalar r) k) (D : ℕ) :
    GateRun (Vector (Table Scalar r) (D+1)) :=
  let out := Metered.driver gateKernel v A D
  ⟨out.arithmetic.value,out.arithmetic.work⟩

theorem gateDriver_value {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) :
    (gateDriver v A D).value = Plain.driver valueKernel v A D := by
  rw [valueKernel_eq_algebra]
  exact driver_refines _ _ gateKernel_refines _ _ _

theorem gateDriver_decode {k r : ℕ} (v : Vector Scalar r)
    (A : Vector (Table Scalar r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((gateDriver v A D).value[s]) = tail A v D s := by
  rw [gateDriver_value]
  exact value_driver_decode v A D s

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
