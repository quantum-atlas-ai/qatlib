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

/-!
# Finite measurement apparatus shifts

This module defines a controlled translation of a cyclic pointer register and computes its
marginal weights. The finite model `jointShift` records the energy-dependent pointer
displacement used in the measurement apparatus of [LidarWang1999].

The translation preserves total squared amplitude and has an explicit inverse. The module also
proves an amplitude reconstruction identity under a stated orthogonality hypothesis.

## Main statements

* `jointShift_delta`: a joint basis vector acquires the corresponding pointer displacement.
* `apparatus_marginal`: the pointer weight sums the squared amplitudes of all indices producing
  that readout.
* `amplitude_recovery_eq47`: orthogonality recovers the original position amplitudes from
  transformed coefficients.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

section Shift

variable {M : ℕ} [NeZero M]

/-- The permutation that preserves the system index `n` and adds `E n` to the cyclic pointer
coordinate. -/
def shiftPerm (E : I → ZMod M) : (I × ZMod M) ≃ (I × ZMod M) where
  toFun p := (p.1, p.2 + E p.1)
  invFun p := (p.1, p.2 - E p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The action of the controlled pointer translation on joint amplitudes by composition with the
inverse of `shiftPerm E`. -/
def jointShift (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) : I × ZMod M → ℂ :=
  fun p => Ψ ((shiftPerm E).symm p)

/-- The translated joint amplitude at `(n, x)` equals the original amplitude at `(n, x - E n)`. -/
@[simp] theorem jointShift_apply (E : I → ZMod M) (Ψ : I × ZMod M → ℂ)
    (n : I) (x : ZMod M) :
    jointShift E Ψ (n, x) = Ψ (n, x - E n) := rfl

/-- The joint basis amplitude supported at the system and pointer pair `(n, x)`. -/
def jointDelta (n : I) (x : ZMod M) : I × ZMod M → ℂ :=
  fun p => if p = (n, x) then 1 else 0

/-- The controlled translation sends the basis amplitude at `(n, x)` to the basis amplitude at
`(n, x + E n)`. -/
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

/-- The controlled pointer translation preserves the sum of squared complex amplitudes over the
joint register. -/
theorem jointShift_norm (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) :
    (∑ p, Complex.normSq (jointShift E Ψ p)) = ∑ p, Complex.normSq (Ψ p) := by
  unfold jointShift
  exact Equiv.sum_comp (shiftPerm E).symm (fun p => Complex.normSq (Ψ p))

/-- Translating by `E` and then by `-E` restores the original joint amplitude function. -/
theorem jointShift_inverse (E : I → ZMod M) (Ψ : I × ZMod M → ℂ) :
    jointShift (fun n => -E n) (jointShift E Ψ) = Ψ := by
  funext p
  rw [jointShift_apply, jointShift_apply]
  congr 2
  simp

/-- The joint amplitude function with system amplitudes `ξ` and pointer fixed at `x0`. -/
def coherentState (ξ : I → ℂ) (x0 : ZMod M) : I × ZMod M → ℂ :=
  fun p => if p.2 = x0 then ξ p.1 else 0

/-- The pointer marginal weight at `x`, obtained by summing squared joint amplitudes over the
system index. -/
def appProb (Ψ : I × ZMod M → ℂ) (x : ZMod M) : ℝ :=
  ∑ n, Complex.normSq (Ψ (n, x))

/-- Every pointer marginal weight is nonnegative. -/
theorem appProb_nonneg (Ψ : I × ZMod M → ℂ) (x : ZMod M) : 0 ≤ appProb Ψ x := by
  unfold appProb
  exact Finset.sum_nonneg (fun n _ => Complex.normSq_nonneg _)

/-- The sum of pointer marginal weights equals the total squared amplitude of the joint
register. -/
theorem appProb_total (Ψ : I × ZMod M → ℂ) :
    (∑ x, appProb Ψ x) = ∑ p, Complex.normSq (Ψ p) := by
  unfold appProb
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]

/-- After controlled translation, the marginal weight at `x` is the sum of `Complex.normSq (ξ
n)` over all indices with `x = x0 + E n`. This retains all indices sharing the same pointer
readout in the finite apparatus model of [LidarWang1999]. -/
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

/-- The total pointer marginal weight after translating `coherentState ξ x0` equals the sum of
squared system amplitudes `ξ`. -/
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

/-- If `ξ` is the conjugate coefficient transform of `ψ` and the stated row orthogonality holds
for `A`, then summing `ξ n * A j n` recovers `ψ j`. This is the finite reconstruction
identity corresponding to Equation 47 of [LidarWang1999]. -/
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
