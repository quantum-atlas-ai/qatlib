/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

structure MultFamily (p q : ℕ) where
  m : ZMod q → (ZMod p)ˣ
  map_add : ∀ s u, m (s + u) = m s * m u

namespace MultFamily

variable {p q : ℕ} (M : MultFamily p q)

@[simp] theorem m_zero : M.m 0 = 1 := by
  have h : M.m 0 = M.m 0 * M.m 0 := by simpa using M.map_add 0 0
  have h2 : M.m 0 * 1 = M.m 0 * M.m 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

theorem m_neg (s : ZMod q) : M.m (-s) = (M.m s)⁻¹ := by
  have h := M.map_add s (-s)
  rw [add_neg_cancel, m_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

def ofUnit (p q : ℕ) [NeZero q] (a : (ZMod p)ˣ) (ha : a ^ q = 1) :
    MultFamily p q where
  m s := a ^ s.val
  map_add s u := by
    have hq : orderOf a ∣ q := orderOf_dvd_iff_pow_eq_one.mpr ha
    have hm : (s.val + u.val) % q ≡ s.val + u.val [MOD orderOf a] :=
      Nat.ModEq.of_dvd hq (Nat.mod_modEq (s.val + u.val) q)
    rw [ZMod.val_add, pow_eq_pow_iff_modEq.mpr hm, pow_add]

theorem ofUnit_m_one (p q : ℕ) [NeZero q] (a : (ZMod p)ˣ) (ha : a ^ q = 1) :
    (ofUnit p q a ha).m 1 = a := by
  change a ^ (1 : ZMod q).val = a
  by_cases hq1 : q = 1
  · subst hq1
    rw [ZMod.val_one_eq_one_mod, Nat.mod_one, pow_zero]
    rw [pow_one] at ha
    exact ha.symm
  · rw [ZMod.val_one'' hq1, pow_one]

end MultFamily

structure QHG {p q : ℕ} (M : MultFamily p q) where

  x : ZMod p

  s : ZMod q

namespace QHG

variable {p q : ℕ} (M : MultFamily p q)

@[ext] theorem ext {a b : QHG M} (hx : a.x = b.x) (hs : a.s = b.s) : a = b := by
  cases a; cases b; simp_all

instance instGroup : Group (QHG M) where
  mul a b := ⟨a.x + (M.m a.s : ZMod p) * b.x, a.s + b.s⟩
  one := ⟨0, 0⟩
  inv a := ⟨-(((M.m a.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * a.x, -a.s⟩
  mul_assoc := by
    intro x y z
    ext
    · show (x.x + (M.m x.s : ZMod p) * y.x)
          + (M.m (x.s + y.s) : ZMod p) * z.x
          = x.x + (M.m x.s : ZMod p) * (y.x + (M.m y.s : ZMod p) * z.x)
      rw [M.map_add, Units.val_mul]
      ring
    · show x.s + y.s + z.s = x.s + (y.s + z.s)
      ring
  one_mul := by
    intro x
    ext
    · show (0 : ZMod p) + (M.m 0 : ZMod p) * x.x = x.x
      rw [M.m_zero, Units.val_one]
      ring
    · show (0 : ZMod q) + x.s = x.s
      ring
  mul_one := by
    intro x
    ext
    · show x.x + (M.m x.s : ZMod p) * 0 = x.x
      ring
    · show x.s + 0 = x.s
      ring
  inv_mul_cancel := by
    intro x
    ext
    · show -(((M.m x.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * x.x
          + (M.m (-x.s) : ZMod p) * x.x = 0
      rw [M.m_neg]
      ring
    · show -x.s + x.s = 0
      ring

@[simp] theorem mul_x (a b : QHG M) :
    (a * b).x = a.x + (M.m a.s : ZMod p) * b.x := rfl

@[simp] theorem mul_s (a b : QHG M) : (a * b).s = a.s + b.s := rfl

@[simp] theorem one_x : (1 : QHG M).x = 0 := rfl

@[simp] theorem one_s : (1 : QHG M).s = 0 := rfl

@[simp] theorem inv_x (a : QHG M) :
    a⁻¹.x = -(((M.m a.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * a.x := rfl

@[simp] theorem inv_s (a : QHG M) : a⁻¹.s = -a.s := rfl

def equivProd : QHG M ≃ ZMod p × ZMod q where
  toFun a := (a.x, a.s)
  invFun y := ⟨y.1, y.2⟩
  left_inv a := by cases a; rfl
  right_inv y := rfl

instance instFintype [NeZero p] [NeZero q] : Fintype (QHG M) :=
  Fintype.ofEquiv (ZMod p × ZMod q) (equivProd M).symm

theorem card [NeZero p] [NeZero q] : Fintype.card (QHG M) = p * q := by
  rw [Fintype.card_congr (equivProd M), Fintype.card_prod, ZMod.card, ZMod.card]

def proj : QHG M →* Multiplicative (ZMod q) where
  toFun a := Multiplicative.ofAdd a.s
  map_one' := rfl
  map_mul' := by intro x y; rfl

theorem mem_ker_proj_iff (a : QHG M) :
    a ∈ (proj M).ker ↔ a.s = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd a.s = 1 ↔ a.s = 0
  rw [ofAdd_eq_one]

def translations : Subgroup (QHG M) where
  carrier := {a | a.s = 0}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    have ha' : a.s = 0 := ha
    have hb' : b.s = 0 := hb
    show a.s + b.s = 0
    rw [ha', hb', add_zero]
  inv_mem' := by
    intro a ha
    have ha' : a.s = 0 := ha
    show -a.s = 0
    rw [ha', neg_zero]

theorem translations_eq_ker : translations M = (proj M).ker := by
  ext a
  rw [mem_ker_proj_iff]
  rfl

theorem translations_normal : (translations M).Normal := by
  rw [translations_eq_ker]
  infer_instance

def translationsEquiv [NeZero p] [NeZero q] : translations M ≃ ZMod p where
  toFun a := a.1.x
  invFun z := ⟨⟨z, 0⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    ext
    · rfl
    · show (0 : ZMod q) = a.1.s
      exact a.2.symm
  right_inv z := rfl

instance instFintypeTranslations [NeZero p] [NeZero q] : Fintype (translations M) :=
  Fintype.ofEquiv (ZMod p) (translationsEquiv M).symm

theorem card_translations [NeZero p] [NeZero q] :
    Fintype.card (translations M) = p := by
  rw [Fintype.card_congr (translationsEquiv M), ZMod.card]

theorem pow_multiplier (k : ℕ) :
    ((⟨0, 1⟩ : QHG M)) ^ k = ⟨0, (k : ZMod q)⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp [Nat.cast_add, Nat.cast_one]

theorem orderOf_multiplier [NeZero q] :
    orderOf ((⟨0, 1⟩ : QHG M)) = q := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_multiplier]
    ext <;> simp
  · rw [← ZMod.natCast_eq_zero_iff]
    have h := pow_orderOf_eq_one ((⟨0, 1⟩ : QHG M))
    rw [pow_multiplier] at h
    have h2 := congrArg QHG.s h
    simpa using h2

end QHG

end Qatlib.Papers.AffineHSP02.MainResults
