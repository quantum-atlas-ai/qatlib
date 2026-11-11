/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Cyclic codes and polynomial shift invariance

The cyclic shift `cyclicShift` is bundled as the linear endomorphism `shiftEnd`. The module
proves that this endomorphism satisfies the polynomial relation X^n - 1 = 0 and characterizes
cyclic submodules by closure under polynomial evaluation at the shift [GeraciLidar2008].

## Main statements

* `shiftEnd_pow_n`: The n-fold shift is the identity.
* `isCyclicCode_iff`: Cyclic codes are precisely the submodules preserved by every polynomial in
  the shift.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.CodeStructure

open scoped BigOperators

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Shifts a word cyclically by sending its coordinate at `i` to the previous coordinate `i -
1`. -/
def cyclicShift (v : ZMod n → R) : ZMod n → R := fun i => v (i - 1)

/-- The cyclic shift on words indexed by `ZMod n`, bundled as an `R`-linear endomorphism. -/
noncomputable def shiftEnd : Module.End R (ZMod n → R) where
  toFun := cyclicShift
  map_add' := by
    intro x y
    ext i
    simp [cyclicShift]
  map_smul' := by
    intro a x
    ext i
    simp [cyclicShift]

/-- Evaluating `shiftEnd` on a word gives its cyclic shift. -/
@[simp] lemma shiftEnd_apply (v : ZMod n → R) : shiftEnd v = cyclicShift v := rfl

/-- A linear code is cyclic when it is closed under `cyclicShift`. -/
def IsCyclicCode (C : Submodule R (ZMod n → R)) : Prop :=
  ∀ v ∈ C, cyclicShift v ∈ C

/-- Applying the cyclic shift `k` times translates the coordinate index by subtraction of `k`. -/
theorem shiftEnd_pow_apply (k : ℕ) (v : ZMod n → R) :
    (shiftEnd (n := n) (R := R) ^ k) v = fun i => v (i - (k : ZMod n)) := by
  induction k with
  | zero => ext i; simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      ext i
      show v ((i - 1) - (k : ZMod n)) = v (i - ((k + 1 : ℕ) : ZMod n))
      congr 1
      push_cast
      ring

/-- The n-th power of the cyclic shift endomorphism on `ZMod n` is the identity. -/
theorem shiftEnd_pow_n : (shiftEnd (n := n) (R := R)) ^ n = 1 := by
  ext v i
  rw [shiftEnd_pow_apply]
  have hzero : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
  rw [hzero]
  simp

/-- Evaluating the polynomial X^n - 1 at the cyclic shift endomorphism gives zero. -/
theorem aeval_X_pow_sub_one :
    Polynomial.aeval (shiftEnd (n := n) (R := R))
      ((Polynomial.X : Polynomial R) ^ n - 1) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, map_one, shiftEnd_pow_n, sub_self]

/-- Every power of the shift endomorphism preserves a cyclic code. -/
theorem shiftEnd_pow_mem (C : Submodule R (ZMod n → R)) (hC : IsCyclicCode C) :
    ∀ (k : ℕ) {v : ZMod n → R}, v ∈ C → (shiftEnd (n := n) (R := R) ^ k) v ∈ C := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hC _ (ih hv)

/-- Evaluating any polynomial at the shift endomorphism preserves membership in a cyclic code
[GeraciLidar2008]. -/
theorem aeval_mem (C : Submodule R (ZMod n → R)) (hC : IsCyclicCode C)
    (p : Polynomial R) {v : ZMod n → R} (hv : v ∈ C) :
    Polynomial.aeval (shiftEnd (n := n) (R := R)) p v ∈ C := by
  rw [Polynomial.aeval_eq_sum_range]
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ ?_
  intro i _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (shiftEnd_pow_mem C hC i hv)

/-- A submodule preserved by every polynomial in the shift is a cyclic code. -/
theorem isCyclicCode_of_aeval (C : Submodule R (ZMod n → R))
    (h : ∀ (p : Polynomial R) (v : ZMod n → R), v ∈ C →
      Polynomial.aeval (shiftEnd (n := n) (R := R)) p v ∈ C) :
    IsCyclicCode C := by
  intro v hv
  have := h Polynomial.X v hv
  simpa [Polynomial.aeval_X, shiftEnd_apply] using this

/-- A submodule is cyclic if and only if every polynomial in the shift preserves it
[GeraciLidar2008]. -/
theorem isCyclicCode_iff (C : Submodule R (ZMod n → R)) :
    IsCyclicCode C ↔
      ∀ (p : Polynomial R) (v : ZMod n → R), v ∈ C →
        Polynomial.aeval (shiftEnd (n := n) (R := R)) p v ∈ C :=
  ⟨fun hC p v hv => aeval_mem C hC p hv, fun h => isCyclicCode_of_aeval C h⟩

end Qatlib.Papers.PottsPartEval07.CodeStructure
