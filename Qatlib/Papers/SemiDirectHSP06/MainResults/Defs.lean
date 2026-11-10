/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

def mulAutOfUnit (n : ℕ) (u : (ZMod n)ˣ) : MulAut (Multiplicative (ZMod n)) where
  toFun x := Multiplicative.ofAdd (↑u * x.toAdd)
  invFun x := Multiplicative.ofAdd (↑u⁻¹ * x.toAdd)
  left_inv x := by
    apply Multiplicative.ext
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    apply Multiplicative.ext
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_mul' x y := by
    apply Multiplicative.ext
    simp only [toAdd_ofAdd, toAdd_mul]
    rw [mul_add]

@[simp]
lemma mulAutOfUnit_apply (n : ℕ) (u : (ZMod n)ˣ) (x : Multiplicative (ZMod n)) :
    mulAutOfUnit n u x = Multiplicative.ofAdd (↑u * x.toAdd) := rfl

def shiftVal (p r : ℕ) : ℕ := 2 * p ^ (r - 1) + 1

theorem shiftUnit_coprime (_hp : p.Prime) (hr : 2 ≤ r) :
    Nat.Coprime (shiftVal p r) (2 * p ^ r) := by
  unfold shiftVal
  refine Nat.Coprime.mul_right ?_ ?_
  · exact Nat.coprime_two_right.mpr ⟨p ^ (r - 1), by ring⟩
  · rw [Nat.coprime_pow_right_iff (by omega : 0 < r)]
    have hp1 : p ^ (r - 1) = p ^ (r - 2) * p := by
      have h1 : r - 2 + 1 = r - 1 := by omega
      rw [← h1, Nat.pow_succ]
    have heq : 2 * p ^ (r - 1) + 1 = 1 + p * (2 * p ^ (r - 2)) := by
      rw [hp1]; ring
    rw [heq]
    exact (Nat.coprime_add_mul_left_left 1 p (2 * p ^ (r - 2))).mpr (by simp)

def shiftUnit (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) : (ZMod (2 * p ^ r))ˣ :=
  ZMod.unitOfCoprime (shiftVal p r) (shiftUnit_coprime hp hr)

@[simp]
lemma coe_shiftUnit (hp : p.Prime) (hr : 2 ≤ r) :
    ((shiftUnit p r hp hr : (ZMod (2 * p ^ r))ˣ) : ZMod (2 * p ^ r)) =
      (shiftVal p r : ZMod (2 * p ^ r)) :=
  ZMod.coe_unitOfCoprime _ _

def shiftAut (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) :
    MulAut (Multiplicative (ZMod (2 * p ^ r))) :=
  mulAutOfUnit _ (shiftUnit p r hp hr)

abbrev SDP (p r : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    Type :=
  SemidirectProduct (Multiplicative (ZMod (2 * p ^ r))) (Multiplicative (ZMod p)) φ

def genX (p r : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    SDP p r φ :=
  inl (Multiplicative.ofAdd 1)

def genY (p r : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    SDP p r φ :=
  inr (Multiplicative.ofAdd 1)

lemma ofAdd_one_pow (n m : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod n)) ^ m = Multiplicative.ofAdd (m : ZMod n) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]

@[simp]
lemma genX_pow (m : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    genX p r φ ^ m =
      inl (Multiplicative.ofAdd (m : ZMod (2 * p ^ r))) := by
  rw [genX, ← map_pow, ofAdd_one_pow]

lemma genY_mul_genX (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) :
    genY p r φ * genX p r φ = genX p r φ ^ shiftVal p r * genY p r φ := by
  have hcomm :
      genY p r φ * genX p r φ =
        inl (φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd (1 : ZMod (2 * p ^ r)))) *
          genY p r φ := by
    apply SemidirectProduct.ext <;> simp [genY, genX]
  rw [hcomm, hφ]
  simp only [shiftAut, mulAutOfUnit_apply, toAdd_ofAdd, mul_one, coe_shiftUnit, genX_pow]

end Qatlib.Papers.SemiDirectHSP06.MainResults
