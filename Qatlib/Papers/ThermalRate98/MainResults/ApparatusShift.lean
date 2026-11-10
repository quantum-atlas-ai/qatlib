/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

section Shift

variable {M : ℕ} [NeZero M]

def shiftPerm (E : I → ZMod M) : (I × ZMod M) ≃ (I × ZMod M) where
  toFun p := (p.1, p.2 + E p.1)
  invFun p := (p.1, p.2 - E p.1)
  left_inv p := by simp
  right_inv p := by simp

def jointShift (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) : I × ZMod M → ℂ :=
  fun p => Ψ ((shiftPerm E).symm p)

@[simp] theorem jointShift_apply (E : I → ZMod M) (Ψ : I × ZMod M → ℂ)
    (n : I) (x : ZMod M) :
    jointShift E Ψ (n, x) = Ψ (n, x - E n) := rfl

def jointDelta (n : I) (x : ZMod M) : I × ZMod M → ℂ :=
  fun p => if p = (n, x) then 1 else 0

theorem jointShift_delta (E : I → ZMod M) (n : I) (x : ZMod M) :
    jointShift E (jointDelta n x) = jointDelta n (x + E n) := by
  funext p
  rw [jointShift_apply]
  unfold jointDelta
  have hiff : ((p.1, p.2 - E p.1) = (n, x)) ↔ (p = (n, x + E n)) := by
    constructor
    · intro h
      have h1 : p.1 = n := by simpa using congrArg Prod.fst h
      have h2 : p.2 - E p.1 = x := by simpa using congrArg Prod.snd h
      rw [h1] at h2
      exact Prod.ext h1 (sub_eq_iff_eq_add.mp h2)
    · intro h
      rw [h]
      simp
  by_cases h : p = (n, x + E n)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hp => h (hiff.mp hp)), if_neg h]

theorem jointShift_norm (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) :
    (∑ p, Complex.normSq (jointShift E Ψ p)) = ∑ p, Complex.normSq (Ψ p) := by
  unfold jointShift
  exact Equiv.sum_comp (shiftPerm E).symm (fun p => Complex.normSq (Ψ p))

theorem jointShift_inverse (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) :
    jointShift (fun n => -E n) (jointShift E Ψ) = Ψ := by
  funext p
  rw [jointShift_apply, jointShift_apply]
  congr 2
  simp

def coherentState (ξ : I → ℂ) (x0 : ZMod M) : I × ZMod M → ℂ :=
  fun p => if p.2 = x0 then ξ p.1 else 0

def appProb (Ψ : I × ZMod M → ℂ) (x : ZMod M) : ℝ :=
  ∑ n, Complex.normSq (Ψ (n, x))

theorem appProb_nonneg (Ψ : I × ZMod M → ℂ) (x : ZMod M) : 0 ≤ appProb Ψ x := by
  unfold appProb
  exact Finset.sum_nonneg (fun n _ => Complex.normSq_nonneg _)

theorem appProb_total (Ψ : I × ZMod M → ℂ) :
    (∑ x, appProb Ψ x) = ∑ p, Complex.normSq (Ψ p) := by
  unfold appProb
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]

theorem apparatus_marginal (E : I → ZMod M) (ξ : I → ℂ) (x0 x : ZMod M) :
    appProb (jointShift E (coherentState ξ x0)) x =
      ∑ n, if x = x0 + E n then Complex.normSq (ξ n) else 0 := by
  unfold appProb
  apply Finset.sum_congr rfl
  intro n _
  rw [jointShift_apply]
  unfold coherentState
  have hiff : (x - E n = x0) ↔ (x = x0 + E n) := sub_eq_iff_eq_add
  by_cases h : x = x0 + E n
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
    simp

theorem apparatus_marginal_total (E : I → ZMod M) (ξ : I → ℂ) (x0 : ZMod M) :
    (∑ x, appProb (jointShift E (coherentState ξ x0)) x) =
      ∑ n, Complex.normSq (ξ n) := by
  rw [appProb_total, jointShift_norm]
  unfold coherentState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro n _
  calc (∑ x, Complex.normSq (if x = x0 then ξ n else 0))
      = ∑ x, (if x = x0 then Complex.normSq (ξ n) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : x = x0 <;> simp [h]
    _ = Complex.normSq (ξ n) := by
        rw [Finset.sum_ite_eq']
        simp

end Shift

section Recovery

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem amplitude_recovery_eq47 (A : J → I → ℂ) (ψ : J → ℂ) (ξ : I → ℂ)
    (hξ : ∀ n, ξ n = ∑ j, star (A j n) * ψ j)
    (hunit : ∀ j j', (∑ n, star (A j' n) * A j n) = if j' = j then 1 else 0)
    (j : J) :
    (∑ n, ξ n * A j n) = ψ j := by
  simp only [hξ]
  calc (∑ n, (∑ j', star (A j' n) * ψ j') * A j n)
      = ∑ n, ∑ j', (star (A j' n) * ψ j') * A j n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_mul]
    _ = ∑ j', ∑ n, (star (A j' n) * ψ j') * A j n := Finset.sum_comm
    _ = ∑ j', ψ j' * (∑ n, star (A j' n) * A j n) := by
        apply Finset.sum_congr rfl
        intro j' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = ∑ j', ψ j' * (if j' = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j' _
        rw [hunit]
    _ = ψ j := by
        rw [show (∑ j', ψ j' * (if j' = j then 1 else 0)) =
          ∑ j', if j' = j then ψ j' else 0 by
            apply Finset.sum_congr rfl
            intro j' _
            by_cases h : j' = j <;> simp [h]]
        rw [Finset.sum_ite_eq']
        simp

end Recovery

end Qatlib.Papers.ThermalRate98.MainResults
