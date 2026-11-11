/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Order finding for an arbitrary permutation

Fixed source: `quant-ph/9508027v2` §5, final paragraph (printed p.21, continuing
to p.22): "Note that in this algorithm for determining the order of an element,
we did not use many of the properties of multiplication (mod n).  In fact, if we
have a permutation `f` mapping the set `{0,1,2,...}` into itself such that its
`k`-th iterate `f^{(k)}(a)` is computable ... the same algorithm will be able to
find the order of an element `a` under `f`, i.e., the minimum `r` such that
`f^{(r)}(a) = a`."

This module isolates the structural content of that remark.  For any finite type
`α`, any permutation `σ` of `α`, and any point `a`, we define the `σ`-order of
`a` as the minimal period of `a` and prove:

* the orbit `k ↦ σ^[k] a` is injective on `Fin r`, so the order-finding oracle
  takes exactly `r` distinct values;
* two iterates agree exactly when their exponents are congruent modulo `r`;
* consequently the "collision modulo the order" fibre structure used to derive
  the Born sampling law in the modular case is a property of *permutations*, not
  of modular multiplication;
* for a finite group acting on itself by left multiplication, the `σ`-order of
  the identity is exactly `orderOf`, so the modular order-finding instance is the
  regular-action case of this general statement.

This is a structural reduction.  It does not implement the controlled iterate
oracle as a gate array and makes no claim about its cost; the paper's efficient
iteration hypothesis is recorded as an external complexity assumption, not a
proved resource bound.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.OrderRecovery

open Function

variable {α : Type*}

/-- The `σ`-order of a point `a`: the smallest positive `r` with
`σ^[r] a = a`.  For a permutation this is `Function.minimalPeriod σ a`. -/
noncomputable def permOrder (σ : Equiv.Perm α) (a : α) : ℕ :=
  Function.minimalPeriod (σ : α → α) a

/-- A point of a finite type is periodic under a permutation, so its period is
positive. -/
theorem permOrder_pos [Finite α] (σ : Equiv.Perm α) (a : α) : 0 < permOrder σ a := by
  unfold permOrder
  exact minimalPeriod_pos_of_mem_periodicPts
    (Injective.mem_periodicPts σ.injective a)

/-- The defining property of the order: iterating `r` times returns to `a`. -/
theorem permOrder_spec (σ : Equiv.Perm α) (a : α) : σ^[permOrder σ a] a = a := by
  unfold permOrder
  exact isPeriodicPt_minimalPeriod (σ : α → α) a

/-- The order divides every period: if `σ^[k] a = a`, then `r ∣ k`. -/
theorem permOrder_dvd (σ : Equiv.Perm α) (a : α) {k : ℕ} (hk : σ^[k] a = a) :
    permOrder σ a ∣ k := by
  unfold permOrder
  exact (show IsPeriodicPt (σ : α → α) k a from hk).minimalPeriod_dvd

/-- The order is the least positive period. -/
theorem permOrder_le (σ : Equiv.Perm α) (a : α) {k : ℕ} (hk : 0 < k)
    (h : σ^[k] a = a) : permOrder σ a ≤ k := by
  unfold permOrder
  exact (show IsPeriodicPt (σ : α → α) k a from h).minimalPeriod_le hk

/-- The order is minimal: no smaller positive iterate fixes `a`. -/
theorem permOrder_minimal (σ : Equiv.Perm α) (a : α) {k : ℕ} (hk : 0 < k)
    (hlt : k < permOrder σ a) : σ^[k] a ≠ a := by
  intro h
  have hle := permOrder_le σ a hk h
  omega

/-- **The fibre of the order-finding oracle is a congruence class.**  Two
iterates of `a` coincide exactly when their exponents are congruent modulo the
order.  This is the `f`-iteration analogue of the modular statement
`x^i = x^j ↔ i ≡ j (mod r)`, and it is the only number-theoretic ingredient the
sampling law uses. -/
theorem perm_fiber_iff (σ : Equiv.Perm α) (a : α) (k j : ℕ) :
    σ^[k] a = σ^[j] a ↔ k ≡ j [MOD permOrder σ a] := by
  constructor
  · intro h
    rcases le_total j k with hjk | hkj
    · -- `k = j + (k - j)`, so the injective iterate cancels `j`.
      have hsub : σ^[k - j] a = a := by
        have h' : σ^[j] (σ^[k - j] a) = σ^[j] a := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le hjk]
          exact h
        exact (σ.injective.iterate j) h'
      exact ((Nat.modEq_iff_dvd' hjk).mpr (permOrder_dvd σ a hsub)).symm
    · have hsub : σ^[j - k] a = a := by
        have h' : σ^[k] (σ^[j - k] a) = σ^[k] a := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le hkj]
          exact h.symm
        exact (σ.injective.iterate k) h'
      exact (Nat.modEq_iff_dvd' hkj).mpr (permOrder_dvd σ a hsub)
  · intro hmod
    unfold permOrder at hmod
    have hk := iterate_mod_minimalPeriod_eq (f := (σ : α → α)) (x := a) (n := k)
    have hj := iterate_mod_minimalPeriod_eq (f := (σ : α → α)) (x := a) (n := j)
    rw [← hk, ← hj]
    exact congrArg (fun t => σ^[t] a) hmod

/-- **The orbit is injective on one period.**  The map `k ↦ σ^[k] a` takes `r`
distinct values on `Fin r`; these are exactly the possible second-register
values in the order-finding algorithm (the paper's `r` values of `x^k`). -/
theorem permOrder_orbit_injective (σ : Equiv.Perm α) (a : α) :
    Function.Injective (fun k : Fin (permOrder σ a) => σ^[k.val] a) := by
  intro k j hkj
  have hmod : k.val ≡ j.val [MOD permOrder σ a] := (perm_fiber_iff σ a _ _).mp hkj
  have : k.val = j.val := Nat.ModEq.eq_of_lt_of_lt hmod k.isLt j.isLt
  exact Fin.ext this

/-- **The general order-finding setup specializes to the regular action.**  For
a finite group `G` acting on itself by left multiplication, the `σ`-order of the
identity element under `x ↦ a * x` is exactly `orderOf a`.  Consequently the
fibre theorem above applies verbatim to the modular order-finding instance,
whose permutation is multiplication by a unit. -/
theorem permOrder_toPerm_eq_orderOf {G : Type*} [Group G] [Finite G] (a : G) :
    permOrder (MulAction.toPerm a) (1 : G) = orderOf a := by
  unfold permOrder
  rw [show (MulAction.toPerm a : G → G) = (fun x : G => a • x) from rfl]
  rw [show Function.minimalPeriod (fun x : G => a • x) (1 : G) =
      MulAction.period a (1 : G) from rfl]
  apply Nat.dvd_antisymm
  · exact MulAction.period_dvd_orderOf a 1
  · apply orderOf_dvd_of_pow_eq_one
    have h := MulAction.pow_period_smul a (1 : G)
    simpa using h

end Qatlib.Papers.ShorFactoring97.OrderRecovery
