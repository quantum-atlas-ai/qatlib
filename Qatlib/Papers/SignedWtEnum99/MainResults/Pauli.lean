/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults.Pauli

def sgn (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma ZMod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have h : z.val = 0 ∨ z.val = 1 := by
    have := ZMod.val_lt (n := 2) z
    omega
  rcases h with h | h
  · left; exact (ZMod.val_eq_zero z).mp h
  · right
    refine ZMod.val_injective (n := 2) ?_
    rw [h, ZMod.val_one]

lemma sgn_eq_one_or (z : ZMod 2) : sgn z = 1 ∨ sgn z = -1 := by
  rcases ZMod2_cases z with h | h <;> simp [sgn, h]

@[simp] lemma two_smul_zmod2 (z : ZMod 2) : 2 • z = 0 := by
  rw [two_nsmul]
  rcases ZMod2_cases z with rfl | rfl
  · simp
  · have h : (1 : ZMod 2) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]; exact ZMod.natCast_self 2
    rw [h]

lemma self_add_zmod2 (z : ZMod 2) : z + z = 0 := by
  rw [← two_nsmul, two_smul_zmod2]

lemma sgn_mul_self (z : ZMod 2) : sgn z * sgn z = 1 := by
  rcases sgn_eq_one_or z with h | h <;> simp [h]

lemma sgn_mul (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases ZMod2_cases a with rfl | rfl <;> rcases ZMod2_cases b with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have h : (1 : ZMod 2) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]; exact ZMod.natCast_self 2
    simp [sgn, h]

abbrev PV (n : ℕ) := Fin n × Fin 2 → ZMod 2

def zpart {n : ℕ} (b : PV n) : Fin n → ZMod 2 := fun i => b (i, 0)

def xpart {n : ℕ} (b : PV n) : Fin n → ZMod 2 := fun i => b (i, 1)

def bform {n : ℕ} (b c : PV n) : ZMod 2 := ∑ i : Fin n, b (i, 0) * c (i, 1)

def yWeight {n : ℕ} (b : PV n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => b (i, 0) = 1 ∧ b (i, 1) = 1)).card

def isZ {n : ℕ} (b : PV n) : Prop := ∀ i, b (i, 1) = 0

lemma isZ_iff_xpart {n : ℕ} (b : PV n) : isZ b ↔ xpart b = 0 := by
  constructor
  · intro h; funext i; simpa [xpart] using h i
  · intro h i; simpa [xpart] using congrFun h i

lemma yWeight_eq_zero_of_isZ {n : ℕ} {b : PV n} (h : isZ b) : yWeight b = 0 := by
  unfold yWeight
  have : (Finset.univ.filter (fun i : Fin n => b (i, 0) = 1 ∧ b (i, 1) = 1)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i _
    have := h i
    simp [this]
  simp [this]

def ybit {n : ℕ} (b : PV n) : ZMod 2 := ∑ i : Fin n, b (i, 0) * b (i, 1)

lemma sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_mul, ih]

lemma sgn_mul_bits (a c : ZMod 2) :
    sgn (a * c) = if a = 1 ∧ c = 1 then (-1 : ℂ) else 1 := by
  rcases ZMod2_cases a with rfl | rfl <;> rcases ZMod2_cases c with rfl | rfl <;>
    simp [sgn]

lemma prod_ite_neg_one {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∏ i ∈ s, (if p i then (-1 : ℂ) else 1)) = (-1 : ℂ) ^ (s.filter p).card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.filter_insert, ih]
      by_cases hp : p a
      · rw [if_pos hp, if_pos hp, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, ha])]
        rw [pow_succ]
        ring
      · rw [if_neg hp, if_neg hp]
        simp

lemma sgn_ybit {n : ℕ} (b : PV n) : sgn (ybit b) = (-1 : ℂ) ^ yWeight b := by
  unfold ybit yWeight
  rw [sgn_sum]
  have h : ∀ i : Fin n,
      sgn (b (i, 0) * b (i, 1)) = if (b (i, 0) = 1 ∧ b (i, 1) = 1) then (-1 : ℂ) else 1 :=
    fun i => sgn_mul_bits _ _
  simp only [h]
  exact prod_ite_neg_one _ _

def xshift {n : ℕ} (b : PV n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x i + b (i, 1)

def dotz {n : ℕ} (b : PV n) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, b (i, 0) * x i

def sMat {n : ℕ} (b : PV n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of (fun x y => if y = xshift b x then
    ((-1 : ℂ) ^ yWeight b) * sgn (dotz b x) else 0)

@[simp] lemma sMat_apply_same {n : ℕ} (b : PV n) (x : Fin n → ZMod 2) :
    sMat b x (xshift b x) = ((-1 : ℂ) ^ yWeight b) * sgn (dotz b x) := by
  simp [sMat]

lemma sMat_apply_ne {n : ℕ} (b : PV n) (x y : Fin n → ZMod 2) (h : y ≠ xshift b x) :
    sMat b x y = 0 := by
  simp [sMat, h]

lemma sMat_zero {n : ℕ} : sMat (0 : PV n) = 1 := by
  ext x y
  rw [sMat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = x
  · subst h
    have hx : y = xshift (0 : PV n) y := by
      funext i; simp [xshift]
    rw [if_pos hx, if_pos rfl]
    simp [yWeight, dotz, sgn]
  · have hx : ¬ (y = xshift (0 : PV n) x) := by
      intro hh
      apply h
      funext i
      have h2 := congrFun hh i
      simpa [xshift] using h2
    rw [if_neg hx, if_neg (fun hxy => h hxy.symm)]

lemma dotz_add {n : ℕ} (b c : PV n) (x : Fin n → ZMod 2) :
    dotz (b + c) x = dotz b x + dotz c x := by
  unfold dotz
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotz_trans {n : ℕ} (b c : PV n) (x : Fin n → ZMod 2) :
    dotz c (xshift b x) = dotz c x + bform c b := by
  unfold dotz xshift bform
  simp only [mul_add, Finset.sum_add_distrib]

lemma ybit_add {n : ℕ} (b c : PV n) :
    ybit (b + c) = ybit b + ybit c + bform b c + bform c b := by
  unfold ybit bform
  simp only [Pi.add_apply]
  have h : ∀ i : Fin n,
      (b (i, 0) + c (i, 0)) * (b (i, 1) + c (i, 1)) =
        (b (i, 0) * b (i, 1) + b (i, 0) * c (i, 1)) +
          (c (i, 0) * b (i, 1) + c (i, 0) * c (i, 1)) := fun i => by ring
  simp only [h, Finset.sum_add_distrib]
  abel

lemma sgn_neg' (z : ZMod 2) : sgn (-z) = sgn z := by
  rcases ZMod2_cases z with rfl | rfl <;> simp [sgn]

lemma xshift_add {n : ℕ} (b c : PV n) (x : Fin n → ZMod 2) :
    xshift (b + c) x = xshift c (xshift b x) := by
  funext i
  simp [xshift, add_assoc]

lemma sMat_mul {n : ℕ} (b c : PV n) :
    sMat b * sMat c = (sgn (bform b c) : ℂ) • sMat (b + c) := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (xshift b x)]
  · rw [sMat_apply_same]
    by_cases hy : y = xshift c (xshift b x)
    · rw [hy, sMat_apply_same c (xshift b x)]
      rw [← xshift_add]
      rw [sMat_apply_same (b + c) x]
      have key : (((-1 : ℂ) ^ yWeight b) * sgn (dotz b x)) *
          (((-1 : ℂ) ^ yWeight c) * sgn (dotz c (xshift b x)))
          = sgn (bform b c) * (((-1 : ℂ) ^ yWeight (b + c)) * sgn (dotz (b + c) x)) := by
        rw [← sgn_ybit b, ← sgn_ybit c, ← sgn_ybit (b + c), dotz_trans, dotz_add]
        simp only [← sgn_mul]
        congr 1
        rw [ybit_add]
        have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        ring_nf
        simp [h2]
      calc (((-1 : ℂ) ^ yWeight b) * sgn (dotz b x)) *
            (((-1 : ℂ) ^ yWeight c) * sgn (dotz c (xshift b x)))
          = sgn (bform b c) * (((-1 : ℂ) ^ yWeight (b + c)) * sgn (dotz (b + c) x)) := key
        _ = sgn (bform b c) * ((-1 : ℂ) ^ yWeight (b + c) * sgn (dotz (b + c) x)) := rfl
    · have hy' : y ≠ xshift (b + c) x := by
        rw [xshift_add]; exact hy
      rw [sMat_apply_ne c (xshift b x) y hy, sMat_apply_ne (b + c) x y hy']
      simp
  · intro z hz hza
    rw [sMat_apply_ne b x z hza, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (xshift b x)) h

end Qatlib.Papers.SignedWtEnum99.MainResults.Pauli
