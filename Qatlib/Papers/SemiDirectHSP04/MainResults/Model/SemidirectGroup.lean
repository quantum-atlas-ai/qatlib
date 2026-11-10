/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

abbrev Cyc (n : ℕ) : Type := Multiplicative (ZMod n)

def canonicalUnit (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) : (ZMod (p ^ r))ˣ :=
  ZMod.unitOfCoprime (1 + p ^ (r - 1)) (by
    have h1 : 1 ≤ r - 1 := by omega
    have hpdvd : p ∣ p ^ (r - 1) := dvd_pow_self p (by omega)
    have hpndvd : ¬ p ∣ (1 + p ^ (r - 1)) := by
      intro h
      have hsub : p ∣ (1 + p ^ (r - 1)) - p ^ (r - 1) :=
        Nat.dvd_sub h hpdvd
      rw [Nat.add_sub_cancel] at hsub
      exact hp.not_dvd_one hsub
    have hcop : Nat.Coprime (1 + p ^ (r - 1)) p :=
      ((hp.coprime_iff_not_dvd).mpr hpndvd).symm
    rw [Nat.coprime_pow_right_iff (by omega)]
    exact hcop)

def unitMulAutHom (n : ℕ) : (ZMod n)ˣ →* MulAut (Cyc n) :=
  (MulAutMultiplicative (ZMod n)).symm.toMonoidHom.comp (AddAut.mulLeft (R := ZMod n))

def unitMulAut (n : ℕ) (u : (ZMod n)ˣ) : MulAut (Cyc n) :=
  unitMulAutHom n u

@[simp]
theorem unitMulAutHom_apply (n : ℕ) (u : (ZMod n)ˣ) :
    unitMulAutHom n u = unitMulAut n u := rfl

@[simp]
theorem unitMulAut_apply (n : ℕ) (u : (ZMod n)ˣ) (a : ZMod n) :
    (unitMulAut n u) (Multiplicative.ofAdd a) = Multiplicative.ofAdd (u * a) := by
  simp [unitMulAut, unitMulAutHom, AddAut.mulLeft, Units.smul_def]

def cyclicAction (p n : ℕ) (u : (ZMod n)ˣ) (hu : u ^ p = 1) :
    Cyc p →* MulAut (Cyc n) :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift p
      ⟨zmultiplesHom (Additive (MulAut (Cyc n))) (Additive.ofMul (unitMulAut n u)), by
        have hpow : (unitMulAut n u) ^ p = 1 := by
          change (unitMulAutHom n u) ^ p = 1
          rw [← map_pow, hu, map_one]
        rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hpow, ofMul_one]⟩)

abbrev Pqr (q n : ℕ) (u : (ZMod n)ˣ) (hu : u ^ q = 1) : Type :=
  Cyc n ⋊[cyclicAction q n u hu] Cyc q

abbrev Ppr (p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) : Type :=
  Pqr p (p ^ r) u hu

def xGen (p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) : Ppr p r u hu :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod (p ^ r)))

def yGen (p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) : Ppr p r u hu :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod p))

theorem canonicalUnit_pow_eq_one (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    canonicalUnit p r hp hr ^ p = 1 := by
  have hm0 : r - 1 ≠ 0 := by omega
  have hm1 : 1 ≤ r - 1 := by omega
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hmul : 3 * (r - 1) ≤ p * (r - 1) := Nat.mul_le_mul_right _ hp3
  have hpm : (r - 1) + 2 ≤ p * (r - 1) := by nlinarith
  have hnot : ¬ (p : ℤ) ∣ (1 : ℤ) := by
    intro h
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h
    have : p ≤ 1 := by exact_mod_cast hle
    omega
  have hord := ZMod.orderOf_one_add_mul_prime_pow hp (r - 1) hm0 hpm (1 : ℤ) hnot 1
  rw [show 1 + (r - 1) = r from by omega, pow_one] at hord
  have hcoe : ((canonicalUnit p r hp hr : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = (1 + p ^ (r - 1) * (1 : ℤ) : ZMod (p ^ r)) := by
    simp only [canonicalUnit, ZMod.coe_unitOfCoprime]
    push_cast
    ring
  have hord' : orderOf (canonicalUnit p r hp hr) = p := by
    rw [← orderOf_units, hcoe]
    exact hord
  rw [← orderOf_dvd_iff_pow_eq_one, hord']

def canonicalX (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    Ppr p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr) :=
  xGen p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr)

def canonicalY (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    Ppr p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr) :=
  yGen p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr)

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
