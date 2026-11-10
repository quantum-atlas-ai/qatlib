/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.SignedWtEnum99.MainResults.Pauli
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults.Pauli

lemma xshift_eq_self_of_xpart_eq_zero {n : ℕ} {b : PV n} (h : xpart b = 0)
    (x : Fin n → ZMod 2) : xshift b x = x := by
  funext i
  have hi : b (i, 1) = 0 := by
    have := congrFun h i
    simpa [xpart] using this
  simp [xshift, hi]

lemma add_right_eq_self {n : ℕ} {b : PV n} {x : Fin n → ZMod 2}
    (h : xshift b x = x) : xpart b = 0 := by
  funext i
  have hi : x i + b (i, 1) = x i := by
    have := congrFun h i
    simpa [xshift] using this
  have h0 : x i + b (i, 1) = x i + 0 := by rw [add_zero]; exact hi
  exact add_left_cancel h0

lemma sMat_diag_of_xpart_eq_zero {n : ℕ} {b : PV n} (h : xpart b = 0)
    (x : Fin n → ZMod 2) :
    sMat b x x = ((-1 : ℂ) ^ yWeight b) * sgn (dotz b x) := by
  have hx : x = xshift b x := (xshift_eq_self_of_xpart_eq_zero h x).symm
  rw [sMat, Matrix.of_apply, if_pos hx]

theorem sMat_vacuum {n : ℕ} (b : PV n) :
    sMat b 0 0 = if xpart b = 0 then ((-1 : ℂ) ^ yWeight b) else 0 := by
  by_cases h : xpart b = 0
  · rw [sMat_diag_of_xpart_eq_zero h 0, if_pos h]
    simp [dotz, sgn]
  · have hne : (0 : Fin n → ZMod 2) ≠ xshift b 0 := by
      intro hh
      exact h (add_right_eq_self hh.symm)
    rw [sMat_apply_ne b 0 0 hne, if_neg h]

def coord {n : ℕ} (i₀ : Fin n) : Fin n → ZMod 2 := fun i => if i = i₀ then 1 else 0

lemma dotz_coord_add {n : ℕ} (b : PV n) (i₀ : Fin n) (x : Fin n → ZMod 2) :
    dotz b (x + coord i₀) = dotz b x + b (i₀, 0) := by
  unfold dotz coord
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma exists_zbit_one {n : ℕ} {b : PV n} (h : zpart b ≠ 0) :
    ∃ i₀ : Fin n, b (i₀, 0) = 1 := by
  by_contra hc
  apply h
  funext i
  have hne : b (i, 0) ≠ 1 := by
    intro hi
    exact hc ⟨i, hi⟩
  rcases ZMod2_cases (b (i, 0)) with h0 | h1
  · exact h0
  · exact absurd h1 hne

lemma sgn_add_one (z : ZMod 2) : sgn (z + 1) = - sgn z := by
  rw [sgn_mul]
  have h1 : sgn (1 : ZMod 2) = -1 := by simp [sgn]
  rw [h1]
  ring

lemma sum_sgn_dotz_eq_zero {n : ℕ} {b : PV n} (h : zpart b ≠ 0) :
    (∑ x : Fin n → ZMod 2, sgn (dotz b x)) = 0 := by
  obtain ⟨i₀, hi₀⟩ := exists_zbit_one h
  let T : ℂ := ∑ x : Fin n → ZMod 2, sgn (dotz b x)
  have hflip : ∀ x : Fin n → ZMod 2,
      sgn (dotz b (x + coord i₀)) = - sgn (dotz b x) := by
    intro x
    rw [dotz_coord_add, hi₀, sgn_add_one]
  have hcomp : (∑ x : Fin n → ZMod 2, sgn (dotz b (x + coord i₀))) = T :=
    Equiv.sum_comp (Equiv.addRight (coord i₀)) (fun x => sgn (dotz b x))
  have hflip_all : (∑ x : Fin n → ZMod 2, sgn (dotz b (x + coord i₀)))
      = ∑ x : Fin n → ZMod 2, (-sgn (dotz b x)) := by
    apply Finset.sum_congr rfl
    intro x _
    exact hflip x
  have hS : (∑ x : Fin n → ZMod 2, sgn (dotz b (x + coord i₀))) = -T := by
    rw [hflip_all, Finset.sum_neg_distrib]
  have hneg : T = -T := hcomp.symm.trans hS
  have h2 : T + T = 0 := (eq_neg_iff_add_eq_zero).mp hneg
  have hT : T = 0 := by
    have h2' : (2 : ℂ) * T = 0 := by rw [two_mul]; exact h2
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  exact hT

theorem trace_sMat_eq_zero_of_xpart_ne {n : ℕ} {b : PV n} (h : xpart b ≠ 0) :
    Matrix.trace (sMat b) = 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply sMat_apply_ne
  intro hx
  exact h (add_right_eq_self hx.symm)

theorem trace_sMat_eq_zero_of_zpart_ne {n : ℕ} {b : PV n} (hx : xpart b = 0)
    (hz : zpart b ≠ 0) : Matrix.trace (sMat b) = 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  have hterm : ∀ x : Fin n → ZMod 2,
      sMat b x x = ((-1 : ℂ) ^ yWeight b) * sgn (dotz b x) :=
    fun x => sMat_diag_of_xpart_eq_zero hx x
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum,
    sum_sgn_dotz_eq_zero hz, mul_zero]

lemma eq_zero_iff_parts {n : ℕ} (b : PV n) : b = 0 ↔ zpart b = 0 ∧ xpart b = 0 := by
  constructor
  · intro h
    subst h
    exact ⟨by funext i; simp [zpart], by funext i; simp [xpart]⟩
  · intro ⟨h1, h2⟩
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases j
    · have := congrFun h1 i
      simpa [zpart] using this
    · have := congrFun h2 i
      simpa [xpart] using this

theorem trace_sMat {n : ℕ} (b : PV n) :
    Matrix.trace (sMat b) = if b = 0 then (2 : ℂ) ^ n else 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [if_pos rfl, sMat_zero, Matrix.trace_one]
    have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin]
      norm_num [ZMod.card]
    exact_mod_cast hcard
  · rw [if_neg hb]
    by_cases hx : xpart b = 0
    · have hz : zpart b ≠ 0 := by
        intro hz0
        exact hb ((eq_zero_iff_parts b).mpr ⟨hz0, hx⟩)
      exact trace_sMat_eq_zero_of_zpart_ne hx hz
    · exact trace_sMat_eq_zero_of_xpart_ne hx

end Qatlib.Papers.SignedWtEnum99.MainResults.Pauli
