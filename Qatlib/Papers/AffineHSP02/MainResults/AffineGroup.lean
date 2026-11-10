/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

structure Aff (p : ℕ) where
  a : (ZMod p)ˣ
  b : ZMod p

namespace Aff

variable {p : ℕ}

@[ext] theorem ext {x y : Aff p} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance instGroup : Group (Aff p) where
  mul x y := ⟨x.a * y.a, x.b + (x.a : ZMod p) * y.b⟩
  one := ⟨1, 0⟩
  inv x := ⟨x.a⁻¹, -((x.a⁻¹ : (ZMod p)ˣ) : ZMod p) * x.b⟩
  mul_assoc := by
    intro x y z
    apply Aff.ext
    · show x.a * y.a * z.a = x.a * (y.a * z.a)
      rw [mul_assoc]
    · show (x.b + (x.a : ZMod p) * y.b) + ((x.a : ZMod p) * y.a) * z.b
        = x.b + (x.a : ZMod p) * (y.b + (y.a : ZMod p) * z.b)
      ring
  one_mul := by
    intro x
    apply Aff.ext
    · show (1 : (ZMod p)ˣ) * x.a = x.a
      rw [one_mul]
    · show (0 : ZMod p) + ((1 : (ZMod p)ˣ) : ZMod p) * x.b = x.b
      simp
  mul_one := by
    intro x
    apply Aff.ext
    · show x.a * 1 = x.a
      rw [mul_one]
    · show x.b + (x.a : ZMod p) * (0 : ZMod p) = x.b
      simp
  inv_mul_cancel := by
    intro x
    apply Aff.ext
    · show x.a⁻¹ * x.a = 1
      simp
    · show (-((x.a⁻¹ : (ZMod p)ˣ) : ZMod p) * x.b)
        + ((x.a⁻¹ : (ZMod p)ˣ) : ZMod p) * x.b = 0
      ring

@[simp] theorem mul_a (x y : Aff p) : (x * y).a = x.a * y.a := rfl

@[simp] theorem mul_b (x y : Aff p) : (x * y).b = x.b + (x.a : ZMod p) * y.b := rfl

@[simp] theorem one_a : (1 : Aff p).a = 1 := rfl

@[simp] theorem one_b : (1 : Aff p).b = 0 := rfl

@[simp] theorem inv_a (x : Aff p) : x⁻¹.a = x.a⁻¹ := rfl

@[simp] theorem inv_b (x : Aff p) : x⁻¹.b = -((x.a⁻¹ : (ZMod p)ˣ) : ZMod p) * x.b := rfl

def trans (b : ZMod p) : Aff p := ⟨1, b⟩

@[simp] theorem trans_a (b : ZMod p) : (trans b).a = 1 := rfl

@[simp] theorem trans_b (b : ZMod p) : (trans b).b = b := rfl

def mult (a : (ZMod p)ˣ) : Aff p := ⟨a, 0⟩

@[simp] theorem mult_a (a : (ZMod p)ˣ) : (mult a).a = a := rfl

@[simp] theorem mult_b (a : (ZMod p)ˣ) : (mult a).b = 0 := rfl

def multHom (p : ℕ) : (ZMod p)ˣ →* Aff p where
  toFun := mult
  map_one' := by apply Aff.ext <;> simp [mult]
  map_mul' := by intro a b; apply Aff.ext <;> simp [mult]

@[simp] theorem multHom_apply (a : (ZMod p)ˣ) : multHom p a = mult a := rfl

theorem multHom_injective (p : ℕ) : Function.Injective (multHom p) := by
  intro a b h
  simpa [mult] using congrArg Aff.a h

theorem orderOf_mult (a : (ZMod p)ˣ) : orderOf (mult a) = orderOf a := by
  have h := orderOf_injective (multHom p) (multHom_injective p) a
  simpa using h

theorem inv_trans (b : ZMod p) : (trans b)⁻¹ = trans (-b) := by
  ext <;> simp [trans]

theorem mult_zpow (a : (ZMod p)ˣ) (t : ℤ) :
    (mult a) ^ t = (⟨a ^ t, 0⟩ : Aff p) := by
  induction t using Int.induction_on with
  | zero => ext <;> simp [mult]
  | succ n ih =>
    rw [zpow_add_one, ih]
    apply Aff.ext
    · rw [mul_a, mult_a]
      show (a ^ (n : ℤ)) * a = a ^ ((n : ℤ) + 1)
      rw [zpow_add_one]
    · rw [mul_b, mult_b]
      simp
  | pred n ih =>
    rw [zpow_sub_one, ih]
    apply Aff.ext
    · rw [mul_a, inv_a, mult_a]
      show (a ^ (-(n : ℤ))) * a⁻¹ = a ^ (-(n : ℤ) - 1)
      rw [zpow_sub_one]
    · rw [mul_b, inv_b, mult_b]
      simp

theorem conj_trans_mult (a : (ZMod p)ˣ) (b : ZMod p) (t : ℤ) :
    trans b * (mult a) ^ t * (trans b)⁻¹ =
      (⟨a ^ t, (1 - ((a ^ t : (ZMod p)ˣ) : ZMod p)) * b⟩ : Aff p) := by
  rw [mult_zpow]
  apply Aff.ext
  · simp [trans]
  · simp only [mul_b, mul_a, trans_a, trans_b, inv_trans, one_mul]
    ring

theorem conj_trans_mult_one (a : (ZMod p)ˣ) (b : ZMod p) :
    trans b * mult a * (trans b)⁻¹ =
      (⟨a, (1 - (a : ZMod p)) * b⟩ : Aff p) := by
  have h := conj_trans_mult a b 1
  simpa using h

def conjMult (a : (ZMod p)ˣ) (b : ZMod p) : Subgroup (Aff p) :=
  (Subgroup.zpowers (mult a)).map (MulAut.conj (trans b))

theorem mem_conjMult_iff (a : (ZMod p)ˣ) (b : ZMod p) (x : Aff p) :
    x ∈ conjMult a b ↔
      ∃ t : ℤ, x = (⟨a ^ t, (1 - ((a ^ t : (ZMod p)ˣ) : ZMod p)) * b⟩ : Aff p) := by
  unfold conjMult
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, by
      change trans b * (mult a) ^ t * (trans b)⁻¹ = _
      rw [conj_trans_mult]⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(mult a) ^ t, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    change trans b * (mult a) ^ t * (trans b)⁻¹ = _
    rw [conj_trans_mult]

theorem conjMult_injective (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) (ha : a ≠ 1) :
    Function.Injective (fun b : ZMod p => conjMult a b) := by
  intro b b' hbb'
  by_cases hb : b = b'
  · exact hb
  exfalso
  have hmem : (⟨a, (1 - (a : ZMod p)) * b⟩ : Aff p) ∈ conjMult a b := by
    rw [mem_conjMult_iff]
    exact ⟨1, by simp⟩
  have hbb'' : conjMult a b = conjMult a b' := hbb'
  rw [hbb''] at hmem
  rw [mem_conjMult_iff] at hmem
  obtain ⟨t, ht⟩ := hmem

  have hat : a ^ t = a := by
    have := congrArg Aff.a ht
    simpa using this.symm

  have hbcoord := congrArg Aff.b ht
  simp only at hbcoord
  rw [hat] at hbcoord
  have hzero : (1 - (a : ZMod p)) * (b - b') = 0 := by
    linear_combination hbcoord
  have hne : (1 - (a : ZMod p)) ≠ 0 := by
    intro h
    exact ha (Units.val_injective (by simpa using (sub_eq_zero.mp h).symm))
  have : b - b' = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hne
    · exact h
  exact hb (sub_eq_zero.mp this)

theorem conj_trans_mult_eq_of_ne_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ)
    (ha : a ≠ 1) (b : ZMod p) :
    ∃ c : ZMod p, trans c * mult a * (trans c)⁻¹ = (⟨a, b⟩ : Aff p) := by
  have hne : (1 - (a : ZMod p)) ≠ 0 := by
    intro h
    exact ha (Units.val_injective (by simpa using (sub_eq_zero.mp h).symm))
  refine ⟨(1 - (a : ZMod p))⁻¹ * b, ?_⟩
  rw [conj_trans_mult_one]
  apply Aff.ext
  · rfl
  · simp only
    field_simp

def affEquivProd (p : ℕ) : Aff p ≃ (ZMod p) × (ZMod p)ˣ where
  toFun x := (x.b, x.a)
  invFun y := ⟨y.2, y.1⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl

instance (p : ℕ) [NeZero p] : Fintype (Aff p) :=
  Fintype.ofEquiv (ZMod p × (ZMod p)ˣ) (affEquivProd p).symm

theorem card_aff (p : ℕ) [Fact p.Prime] : Fintype.card (Aff p) = p * (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Fintype.card_congr (affEquivProd p), Fintype.card_prod, ZMod.card,
    Fintype.card_units, ZMod.card]

end Aff

end Qatlib.Papers.AffineHSP02.MainResults
