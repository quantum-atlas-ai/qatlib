/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup

structure Wreath (n : ℕ) where
  x : Fin n → ZMod 2
  y : Fin n → ZMod 2
  a : ZMod 2

deriving instance DecidableEq for Wreath

namespace Wreath

variable {n : ℕ}

@[ext]
theorem ext {g h : Wreath n} (hx : g.x = h.x) (hy : g.y = h.y) (ha : g.a = h.a) : g = h := by
  cases g
  cases h
  cases hx
  cases hy
  cases ha
  rfl

def mulW (g h : Wreath n) : Wreath n :=
  ⟨fun i => g.x i + h.x i + h.a * (g.x i + g.y i),
   fun i => g.y i + h.y i + h.a * (g.x i + g.y i),
   g.a + h.a⟩

def oneW : Wreath n := ⟨0, 0, 0⟩

def invW (g : Wreath n) : Wreath n :=
  ⟨fun i => g.x i + g.a * (g.x i + g.y i),
   fun i => g.y i + g.a * (g.x i + g.y i),
   g.a⟩

instance : Mul (Wreath n) := ⟨mulW⟩
instance : One (Wreath n) := ⟨oneW⟩
instance : Inv (Wreath n) := ⟨invW⟩

@[simp] lemma mulW_x (g h : Wreath n) (i : Fin n) :
    (mulW g h).x i = g.x i + h.x i + h.a * (g.x i + g.y i) := rfl

@[simp] lemma mulW_y (g h : Wreath n) (i : Fin n) :
    (mulW g h).y i = g.y i + h.y i + h.a * (g.x i + g.y i) := rfl

@[simp] lemma mulW_a (g h : Wreath n) : (mulW g h).a = g.a + h.a := rfl

@[simp] lemma oneW_x (i : Fin n) : (oneW : Wreath n).x i = 0 := rfl

@[simp] lemma oneW_y (i : Fin n) : (oneW : Wreath n).y i = 0 := rfl

@[simp] lemma oneW_a : (oneW : Wreath n).a = 0 := rfl

@[simp] lemma invW_x (g : Wreath n) (i : Fin n) :
    (invW g).x i = g.x i + g.a * (g.x i + g.y i) := rfl

@[simp] lemma invW_y (g : Wreath n) (i : Fin n) :
    (invW g).y i = g.y i + g.a * (g.x i + g.y i) := rfl

@[simp] lemma invW_a (g : Wreath n) : (invW g).a = g.a := rfl

def t (n : ℕ) : Wreath n := ⟨0, 0, 1⟩

@[simp] lemma t_x (i : Fin n) : (t n).x i = 0 := rfl

@[simp] lemma t_y (i : Fin n) : (t n).y i = 0 := rfl

@[simp] lemma t_a : (t n).a = 1 := rfl

def swapFun (g : Wreath n) : Wreath n := ⟨g.y, g.x, g.a⟩

@[simp] lemma swapFun_x (g : Wreath n) (i : Fin n) : (swapFun g).x i = g.y i := rfl

@[simp] lemma swapFun_y (g : Wreath n) (i : Fin n) : (swapFun g).y i = g.x i := rfl

@[simp] lemma swapFun_a (g : Wreath n) : (swapFun g).a = g.a := rfl

@[simp] lemma swapFun_swapFun (g : Wreath n) : swapFun (swapFun g) = g := rfl

macro "zring" : tactic => `(tactic| (ring_nf <;> reduce_mod_char))

macro "wclose" : tactic => `(tactic| (first
      | (simp only [mulW_x, mulW_y, mulW_a, oneW_x, oneW_y, oneW_a,
          invW_x, invW_y, invW_a, swapFun_x, swapFun_y, swapFun_a,
          t_x, t_y, t_a] <;> zring)
      | zring))

macro "wext" : tactic => `(tactic| (apply Wreath.ext <;> (first | (funext i; wclose) | wclose)))

lemma swapFun_mul (g h : Wreath n) : swapFun (mulW g h) = mulW (swapFun g) (swapFun h) := by
  change swapFun (mulW g h) = mulW (swapFun g) (swapFun h)
  wext

lemma swapFun_one : swapFun (oneW : Wreath n) = oneW := by
  change swapFun oneW = oneW
  wext

lemma swapFun_inv (g : Wreath n) : swapFun (invW g) = invW (swapFun g) := by
  change swapFun (invW g) = invW (swapFun g)
  wext

instance : Group (Wreath n) where
  mul := mulW
  one := oneW
  inv := invW
  mul_assoc g h k := by
    change mulW (mulW g h) k = mulW g (mulW h k)
    wext
  one_mul g := by
    change mulW oneW g = g
    wext
  mul_one g := by
    change mulW g oneW = g
    wext
  inv_mul_cancel g := by
    change mulW (invW g) g = oneW
    wext

instance : Fintype (Wreath n) :=
  Fintype.ofEquiv ((Fin n → ZMod 2) × (Fin n → ZMod 2) × ZMod 2)
    ((⟨fun g => (g.x, g.y, g.a), fun p => ⟨p.1, p.2.1, p.2.2⟩,
       fun g => by cases g; rfl,
       fun p => by rcases p with ⟨x, y, a⟩; rfl⟩ :
      Wreath n ≃ ((Fin n → ZMod 2) × (Fin n → ZMod 2) × ZMod 2))).symm

def base (n : ℕ) : Subgroup (Wreath n) where
  carrier := {g | g.a = 0}
  mul_mem' := by
    intro g h hg hh
    change (mulW g h).a = 0
    simp only [mulW_a]
    rw [hg, hh, add_zero]
  one_mem' := by
    change (oneW : Wreath n).a = 0
    rfl
  inv_mem' := by
    intro g hg
    change (invW g).a = 0
    simp only [invW_a]
    exact hg

@[simp] lemma mem_base {g : Wreath n} : g ∈ base n ↔ g.a = 0 := Iff.rfl

lemma t_mul_t : t n * t n = 1 := by
  change mulW (t n) (t n) = oneW
  wext

lemma mul_at_a_zero (x y : Fin n → ZMod 2) :
    (⟨x, y, 0⟩ : Wreath n) * ⟨x, y, 0⟩ = 1 := by
  change mulW ⟨x, y, 0⟩ ⟨x, y, 0⟩ = oneW
  wext

lemma base_mul_self {g : Wreath n} (hg : g ∈ base n) : g * g = 1 := by
  have hga : g.a = 0 := hg
  have hg' : g = ⟨g.x, g.y, (0 : ZMod 2)⟩ := by
    apply Wreath.ext
    · rfl
    · rfl
    · exact hga
  rw [hg']
  exact mul_at_a_zero g.x g.y

lemma mul_self (g : Wreath n) :
    g * g = ⟨fun i => g.a * (g.x i + g.y i), fun i => g.a * (g.x i + g.y i), 0⟩ := by
  change mulW g g = ⟨fun i => g.a * (g.x i + g.y i), fun i => g.a * (g.x i + g.y i), 0⟩
  wext

lemma sq_mem_base (g : Wreath n) : g * g ∈ base n := by
  rw [mul_self]
  exact mem_base.mpr rfl

lemma sq_at_a_one (x y : Fin n → ZMod 2) :
    (⟨x, y, 1⟩ : Wreath n) * ⟨x, y, 1⟩ = ⟨fun i => x i + y i, fun i => x i + y i, 0⟩ := by
  change mulW ⟨x, y, 1⟩ ⟨x, y, 1⟩
      = ⟨fun i => x i + y i, fun i => x i + y i, (0 : ZMod 2)⟩
  wext

lemma sq_of_a_one {g : Wreath n} (hg : g.a = 1) :
    g * g = ⟨fun i => g.x i + g.y i, fun i => g.x i + g.y i, 0⟩ := by
  have hg' : g = ⟨g.x, g.y, (1 : ZMod 2)⟩ := by
    apply Wreath.ext
    · rfl
    · rfl
    · exact hg
  rw [hg']
  exact sq_at_a_one g.x g.y

lemma cube_at_a_one (x y : Fin n → ZMod 2) :
    (⟨x, y, 1⟩ : Wreath n) * ⟨x, y, 1⟩ * ⟨x, y, 1⟩ = swapFun ⟨x, y, 1⟩ := by
  change mulW (mulW ⟨x, y, 1⟩ ⟨x, y, 1⟩) ⟨x, y, 1⟩ = swapFun ⟨x, y, 1⟩
  wext

lemma cube_of_a_one {g : Wreath n} (hg : g.a = 1) : g * g * g = swapFun g := by
  have hg' : g = ⟨g.x, g.y, (1 : ZMod 2)⟩ := by
    apply Wreath.ext
    · rfl
    · rfl
    · exact hg
  rw [hg']
  exact cube_at_a_one g.x g.y

lemma cube_eq_swap {g : Wreath n} (hg : g.a = 1) : g ^ 3 = swapFun g := by
  have h : g ^ 3 = g * g * g := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  rw [h]
  exact cube_of_a_one hg

def conjSub (U : Subgroup (Wreath n)) : Subgroup (Wreath n) where
  carrier := swapFun '' (U : Set (Wreath n))
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, U.mul_mem ha hb, ?_⟩
    change swapFun (mulW a b) = mulW (swapFun a) (swapFun b)
    exact swapFun_mul a b
  one_mem' := ⟨1, U.one_mem, swapFun_one⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, U.inv_mem ha, swapFun_inv a⟩

@[simp] lemma mem_conjSub {U : Subgroup (Wreath n)} {g : Wreath n} :
    g ∈ conjSub U ↔ ∃ u ∈ U, swapFun u = g := Iff.rfl

lemma conjSub_conjSub (U : Subgroup (Wreath n)) : conjSub (conjSub U) = U := by
  ext g
  constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    simpa using hv
  · intro hg
    exact ⟨swapFun g, ⟨g, hg, rfl⟩, swapFun_swapFun g⟩

end Wreath

end Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
