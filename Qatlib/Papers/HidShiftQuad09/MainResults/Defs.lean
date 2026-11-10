/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.Defs

open scoped BigOperators
open Finset

abbrev Cube (n : ℕ) := Fin n → ZMod 2

def agreeChar {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) : ℝ :=
  if f x = g x then 1 else -1

def disagreeFrac {n : ℕ} (f g : Cube n → ZMod 2) : ℝ :=
  (∑ x : Cube n, if f x = g x then (0 : ℝ) else 1) / (Fintype.card (Cube n) : ℝ)

def corr {n : ℕ} (f g : Cube n → ZMod 2) : ℝ :=
  (∑ x : Cube n, agreeChar f g x) / (Fintype.card (Cube n) : ℝ)

def fourierCoeff {n : ℕ} (f : Cube n → ZMod 2) (w : Cube n) : ℝ :=
  (∑ x : Cube n, agreeChar f (fun y => ∑ i, w i * y i) x) / (Fintype.card (Cube n) : ℝ)

structure QuadPoly (n : ℕ) where

  Q : Fin n → Fin n → ZMod 2

  L : Fin n → ZMod 2

namespace QuadPoly

def eval {n : ℕ} (p : QuadPoly n) (x : Cube n) : ZMod 2 :=
  (∑ i, ∑ j, p.Q i j * x i * x j) + ∑ i, p.L i * x i

def form {n : ℕ} (p : QuadPoly n) : Fin n → Fin n → ZMod 2 := p.Q

def SameForm {n : ℕ} (p q : QuadPoly n) : Prop := p.Q = q.Q

end QuadPoly

def IsQuadratic {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∃ p : QuadPoly n, f = p.eval

def HasNoPeriod {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∀ a : Cube n, (∀ x, f (x + a) = f x) → a = 0

def HiddenShift {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n) : Prop :=
  ∀ x, g x = f (x + s)

def phase {n : ℕ} (f : Cube n → ZMod 2) (x : Cube n) : ℝ :=
  if f x = 0 then 1 else -1

def gowersU3 {n : ℕ} (f : Cube n → ZMod 2) : ℝ :=
  |(∑ x : Cube n, ∑ h : Fin 3 → Cube n,
      ∏ S : Finset (Fin 3), phase f (x + ∑ i ∈ S, h i)) /
    ((Fintype.card (Cube n) : ℝ) * (Fintype.card (Fin 3 → Cube n) : ℝ))| ^ (1 / 8 : ℝ)

def bent {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∀ w : Cube n, |fourierCoeff f w| = (2 : ℝ) ^ (-(n : ℝ) / 2)

theorem agreeChar_eq {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) :
    agreeChar f g x = 1 - 2 * (if f x = g x then (0 : ℝ) else 1) := by
  unfold agreeChar
  split_ifs <;> norm_num

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

theorem card_cube_ne_zero (n : ℕ) : (Fintype.card (Cube n) : ℝ) ≠ 0 := by
  rw [card_cube]
  positivity

theorem corr_eq_one_sub_two_disagree {n : ℕ} (f g : Cube n → ZMod 2) :
    corr f g = 1 - 2 * disagreeFrac f g := by
  unfold corr disagreeFrac
  have hchar : ∀ x : Cube n, agreeChar f g x = 1 - 2 * (if f x = g x then (0 : ℝ) else 1) :=
    fun x => agreeChar_eq f g x
  have hsum : (∑ x : Cube n, agreeChar f g x)
      = (Fintype.card (Cube n) : ℝ) - 2 * ∑ x : Cube n, (if f x = g x then (0 : ℝ) else 1) := by
    calc (∑ x : Cube n, agreeChar f g x)
        = ∑ x : Cube n, (1 - 2 * (if f x = g x then (0 : ℝ) else 1)) := by
          exact Finset.sum_congr rfl (fun x _ => hchar x)
      _ = (∑ x : Cube n, (1 : ℝ))
            - ∑ x : Cube n, 2 * (if f x = g x then (0 : ℝ) else 1) := by
          rw [Finset.sum_sub_distrib]
      _ = (Fintype.card (Cube n) : ℝ)
            - 2 * ∑ x : Cube n, (if f x = g x then (0 : ℝ) else 1) := by
          rw [← Finset.mul_sum]
          simp
  rw [hsum]
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := card_cube_ne_zero n
  field_simp [hc]

theorem disagreeFrac_bounds {n : ℕ} (f g : Cube n → ZMod 2) :
    0 ≤ disagreeFrac f g ∧ disagreeFrac f g ≤ 1 := by
  constructor
  · unfold disagreeFrac
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      split_ifs <;> norm_num
    · positivity
  · unfold disagreeFrac
    rw [div_le_one (by positivity)]
    calc (∑ x : Cube n, if f x = g x then (0 : ℝ) else 1)
        ≤ ∑ _x : Cube n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          split_ifs <;> norm_num
      _ = (Fintype.card (Cube n) : ℝ) := by simp

theorem abs_corr_le_one {n : ℕ} (f g : Cube n → ZMod 2) : |corr f g| ≤ 1 := by
  rw [corr_eq_one_sub_two_disagree]
  have h := disagreeFrac_bounds f g
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem corr_nonneg_of_half_agree {n : ℕ} (f g : Cube n → ZMod 2)
    (h : disagreeFrac f g ≤ 1 / 2) : 0 ≤ corr f g := by
  rw [corr_eq_one_sub_two_disagree]
  linarith

theorem bernstein_pow (k : ℕ) (ε : ℝ) (hε : ε ≤ 1) :
    1 - (k : ℝ) * ε ≤ (1 - ε) ^ k := by
  have h := one_add_mul_le_pow (a := -ε) (by linarith) k
  simpa [sub_eq_add_neg] using h

theorem pow_le_pow_of_le_one {r : ℝ} (k : ℕ) (_hr0 : 0 ≤ r) (_hr1 : r ≤ 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ r) : a ^ k ≤ r ^ k := by
  exact pow_le_pow_left₀ ha0 ha k

def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by
    have := ZMod.val_lt a
    omega
  rcases h with h | h
  · left; exact (ZMod.val_eq_zero a).mp h
  · right; exact (ZMod.val_eq_one (by norm_num) a).mp h

theorem sgn_zero : sgn 0 = 1 := rfl

theorem sgn_one : sgn 1 = -1 := by
  rw [sgn]
  rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · rw [zero_add, sgn_zero, sgn_one]; norm_num
  · rw [add_zero, sgn_zero, sgn_one]; norm_num
  · have h : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h, sgn_zero, sgn_one]; norm_num

theorem sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> norm_num [sgn_zero, sgn_one]

theorem sgn_sum {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) :
    sgn (∑ i ∈ s, g i) = ∏ i ∈ s, sgn (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem phase_eq_sgn {n : ℕ} (f : Cube n → ZMod 2) (x : Cube n) :
    phase f x = sgn (f x) := rfl

theorem agreeChar_eq_sgn_add {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) :
    agreeChar f g x = sgn (f x + g x) := by
  unfold agreeChar
  rcases zmod2_cases (f x) with hf | hf <;> rcases zmod2_cases (g x) with hg | hg
  · rw [hf, hg, if_pos rfl, zero_add, sgn_zero]
  · rw [hf, hg, if_neg (by decide : (0 : ZMod 2) ≠ 1), zero_add, sgn_one]
  · rw [hf, hg, if_neg (by decide : (1 : ZMod 2) ≠ 0), add_zero, sgn_one]
  · rw [hf, hg, if_pos rfl]
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h, sgn_zero]

theorem agreeChar_eq_phase_mul {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) :
    agreeChar f g x = phase f x * phase g x := by
  rw [agreeChar_eq_sgn_add, phase_eq_sgn, phase_eq_sgn]
  exact sgn_add _ _

def dot {n : ℕ} (w x : Cube n) : ZMod 2 := ∑ i, w i * x i

theorem dot_add {n : ℕ} (w x h : Cube n) : dot w (x + h) = dot w x + dot w h := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem dot_comm {n : ℕ} (w x : Cube n) : dot w x = dot x w := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

def chi {n : ℕ} (w x : Cube n) : ℝ := sgn (dot w x)

theorem chi_eq_prod {n : ℕ} (w x : Cube n) :
    chi w x = ∏ i, sgn (w i * x i) := by
  unfold chi dot
  simpa using sgn_sum (Finset.univ) (fun i : Fin n => w i * x i)

theorem chi_add {n : ℕ} (w x h : Cube n) : chi w (x + h) = chi w x * chi w h := by
  unfold chi
  rw [dot_add, sgn_add]

theorem piFinset_univ (n : ℕ) :
    (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))))
      = (Finset.univ : Finset (Cube n)) := by
  ext f
  simp

theorem coord_chi_sum (z : ZMod 2) :
    (∑ a : ZMod 2, sgn (a * z)) = if z = 0 then (2 : ℝ) else 0 := by
  have h2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rcases zmod2_cases z with rfl | rfl
  · rw [h2]; norm_num [sgn]
  · rw [h2]; norm_num [sgn_zero, sgn_one]

theorem chi_sum (n : ℕ) (x : Cube n) :
    (∑ w : Cube n, chi w x) = if x = 0 then (2 : ℝ) ^ n else 0 := by
  have hchi : ∀ w : Cube n, chi w x = ∏ i, sgn (w i * x i) := fun w => chi_eq_prod w x
  simp only [hchi]
  rw [← piFinset_univ n]
  rw [Finset.sum_prod_piFinset (s := Finset.univ) (g := fun i a => sgn (a * x i))]
  have hcoord : ∀ i, (∑ a : ZMod 2, sgn (a * x i)) = if x i = 0 then (2 : ℝ) else 0 :=
    fun i => coord_chi_sum (x i)
  simp only [hcoord]
  by_cases hx : x = 0
  · rw [if_pos hx]
    have hx' : ∀ i, x i = 0 := fun i => congrFun hx i
    simp [hx']
  · rw [if_neg hx]
    have hx' : ∃ i, x i ≠ 0 := by
      simpa [funext_iff] using hx
    obtain ⟨i, hi⟩ := hx'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ b = a := by
  constructor
  · intro h
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp_all
  · intro h; rw [h]
    rcases zmod2_cases a with rfl | rfl <;> decide

theorem add_eq_zero_iff_eq {n : ℕ} (s x : Cube n) : s + x = 0 ↔ x = s := by
  constructor
  · intro h
    funext i
    exact (zmod2_add_eq_zero_iff (s i) (x i)).mp (by simpa using congrFun h i)
  · intro h; rw [h]
    funext i
    simpa using (zmod2_add_eq_zero_iff (s i) (s i)).mpr rfl

theorem chi_sum_eq_delta (n : ℕ) (s x : Cube n) :
    (∑ w : Cube n, chi w (s + x)) = if x = s then (2 : ℝ) ^ n else 0 := by
  rw [chi_sum]
  by_cases h : (s + x = 0)
  · rw [if_pos h, if_pos (add_eq_zero_iff_eq s x |>.mp h)]
  · rw [if_neg h, if_neg]
    intro hc
    exact h ((add_eq_zero_iff_eq s x).mpr hc)

theorem fourierCoeff_shift {n : ℕ} (f : Cube n → ZMod 2) (s w : Cube n) :
    fourierCoeff (fun x => f (x + s)) w = chi w s * fourierCoeff f w := by
  unfold fourierCoeff chi
  have hcard : (Fintype.card (Cube n) : ℝ) ≠ 0 := card_cube_ne_zero n
  set dw : Cube n → ZMod 2 := fun y => ∑ i, w i * y i with hdw
  have hterm : ∀ x : Cube n,
      agreeChar (fun x => f (x + s)) dw x
        = agreeChar f dw (x + s) * sgn (dw s) := by
    intro x
    rw [agreeChar_eq_sgn_add, agreeChar_eq_sgn_add]
    have hds : dw (x + s) = dw x + dw s := by
      simpa [dot, hdw] using dot_add w x s
    rw [hds]
    have e1 : f (x + s) + (dw x + dw s) = (f (x + s) + dw x) + dw s := by ring
    rw [e1]
    conv_rhs => rw [sgn_add]
    rw [mul_assoc, sgn_mul_self, mul_one]
  have hsum : (∑ x : Cube n, agreeChar (fun x => f (x + s)) dw x)
      = ∑ y : Cube n, agreeChar f dw y * sgn (dw s) := by
    rw [← Fintype.sum_equiv (Equiv.addRight s)
      (fun x : Cube n => agreeChar (fun x => f (x + s)) dw x)
      (fun y : Cube n => agreeChar f dw y * sgn (dw s))]
    intro x
    rw [hterm x]
    rfl
  rw [hsum]
  rw [← Finset.sum_mul]
  have hchi : sgn (dot w s) = sgn (dw s) := rfl
  rw [hchi]
  ring

theorem gowersU3_nonneg {n : ℕ} (f : Cube n → ZMod 2) : 0 ≤ gowersU3 f := by
  unfold gowersU3
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem abs_phase_prod {n : ℕ} (f : Cube n → ZMod 2) (x : Cube n)
    (h : Fin 3 → Cube n) :
    |∏ S : Finset (Fin 3), phase f (x + ∑ i ∈ S, h i)| = 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro S _
  unfold phase
  split_ifs <;> norm_num

theorem gowersU3_le_one {n : ℕ} (f : Cube n → ZMod 2) : gowersU3 f ≤ 1 := by
  unfold gowersU3
  set S : ℝ := ∑ x : Cube n, ∑ h : Fin 3 → Cube n,
      ∏ T : Finset (Fin 3), phase f (x + ∑ i ∈ T, h i) with hS
  set c1 : ℝ := (Fintype.card (Cube n) : ℝ) with hc1
  set c2 : ℝ := (Fintype.card (Fin 3 → Cube n) : ℝ) with hc2
  have hc1pos : 0 < c1 := by rw [hc1, card_cube]; positivity
  have hc2pos : 0 < c2 := by
    rw [hc2]
    have hpos : 0 < Fintype.card (Fin 3 → Cube n) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    exact_mod_cast hpos
  have hbound : |S| ≤ c1 * c2 := by
    calc |S| ≤ ∑ x : Cube n, ∑ h : Fin 3 → Cube n,
            |∏ T : Finset (Fin 3), phase f (x + ∑ i ∈ T, h i)| := by
          rw [hS]
          calc |∑ x : Cube n, ∑ h : Fin 3 → Cube n,
                ∏ T : Finset (Fin 3), phase f (x + ∑ i ∈ T, h i)|
              ≤ ∑ x : Cube n, |∑ h : Fin 3 → Cube n,
                ∏ T : Finset (Fin 3), phase f (x + ∑ i ∈ T, h i)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ x : Cube n, ∑ h : Fin 3 → Cube n,
                |∏ T : Finset (Fin 3), phase f (x + ∑ i ∈ T, h i)| := by
                apply Finset.sum_le_sum
                intro x _
                exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _x : Cube n, ∑ _h : Fin 3 → Cube n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro hh _
          exact abs_phase_prod f x hh
      _ = c1 * c2 := by
          simp [hc1, hc2, Finset.sum_const, Finset.card_univ, mul_comm]
  have habs : |S / (c1 * c2)| ≤ 1 := by
    rw [abs_div, abs_of_pos (mul_pos hc1pos hc2pos), div_le_one (mul_pos hc1pos hc2pos)]
    exact hbound
  have h0 : 0 ≤ |S / (c1 * c2)| := abs_nonneg _
  calc |S / (c1 * c2)| ^ (1 / 8 : ℝ) ≤ 1 ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow h0 habs (by norm_num)
    _ = 1 := Real.one_rpow _

end Qatlib.Papers.HidShiftQuad09.MainResults.Defs
