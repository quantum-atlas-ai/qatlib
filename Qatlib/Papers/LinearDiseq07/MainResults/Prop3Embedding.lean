/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-!
# Embedding products of cyclic groups

The additive maps `embHom` and `embProd` send cyclic factors into a common modulus by scaling
coordinates. The injectivity theorem supplies the algebraic embedding used in Proposition 3 of
[Ivanyos2008].

## Main statements

* `embHom_apply`: Gives the representative formula for the cyclic map.
* `embProd_injective`: Proves injectivity for positive moduli.

## References

* [Ivanyos, 2008][Ivanyos2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LinearDiseq07.MainResults

/-- The additive map from `ZMod mi` to `ZMod m` induced by scaling by `m / mi` when `mi` divides
`m`. -/
def embHom (m mi : ℕ) (hmi : mi ∣ m) : ZMod mi →+ ZMod m :=
  ZMod.lift mi
    ⟨(AddMonoidHom.mulLeft ((m / mi : ℕ) : ZMod m)).comp (Int.castAddHom (ZMod m)), by
      show ((m / mi : ℕ) : ZMod m) * ((mi : ℤ) : ZMod m) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hmi, ZMod.natCast_self]⟩

/-- For nonzero `mi`, the cyclic map sends `x` to the residue of `(m / mi) * x.val` modulo `m`. -/
theorem embHom_apply (m mi : ℕ) [NeZero mi] (hmi : mi ∣ m) (x : ZMod mi) :
    embHom m mi hmi x = (((m / mi) * x.val : ℕ) : ZMod m) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [show ((x.val : ℕ) : ZMod mi) = ((x.val : ℤ) : ZMod mi) by rw [Int.cast_natCast]]
  unfold embHom
  rw [ZMod.lift_coe]
  simp [AddMonoidHom.comp_apply, Nat.cast_mul]

/-- The coordinatewise additive map from a product of cyclic groups into a power of `ZMod m`,
used in Proposition 3 of [Ivanyos2008]. -/
def embProd {n : ℕ} (m : ℕ) (mi : Fin n → ℕ) (hmi : ∀ i, mi i ∣ m) :
    (∀ i, ZMod (mi i)) →+ (Fin n → ZMod m) where
  toFun x i := embHom m (mi i) (hmi i) (x i)
  map_zero' := by funext i; exact map_zero _
  map_add' x y := by funext i; exact map_add _ _ _

/-- When all moduli are positive and each factor modulus divides `m`, the product embedding is
injective, as required in Proposition 3 of [Ivanyos2008]. -/
theorem embProd_injective {n : ℕ} (m : ℕ) (mi : Fin n → ℕ) (hm : 0 < m)
    (hmi : ∀ i, mi i ∣ m) (hpos : ∀ i, 0 < mi i) :
    Function.Injective (embProd m mi hmi) := by
  intro x y hxy
  have hzero : embProd m mi hmi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  funext i
  haveI : NeZero (mi i) := ⟨by have := hpos i; omega⟩
  have h0 : (((m / mi i) * ((x - y) i).val : ℕ) : ZMod m) = 0 := by
    have := congrFun hzero i
    simp only [Pi.zero_apply] at this
    simpa [embProd, embHom_apply] using this
  have hdvd : m ∣ (m / mi i) * ((x - y) i).val :=
    (ZMod.natCast_eq_zero_iff _ m).mp h0
  have hm' : m = mi i * (m / mi i) := by
    rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (hmi i)).symm
  have hdvd' : mi i * (m / mi i) ∣ (m / mi i) * ((x - y) i).val := by
    rw [← hm']; exact hdvd
  have hdvdk : mi i * (m / mi i) ∣ ((x - y) i).val * (m / mi i) := by
    rw [Nat.mul_comm ((x - y) i).val (m / mi i)]; exact hdvd'
  have hkpos : 0 < m / mi i := Nat.div_pos (Nat.le_of_dvd hm (hmi i)) (hpos i)
  have hd2 : mi i ∣ ((x - y) i).val := Nat.dvd_of_mul_dvd_mul_right hkpos hdvdk
  have hlt : ((x - y) i).val < mi i := ZMod.val_lt _
  have hval : ((x - y) i).val = 0 := Nat.eq_zero_of_dvd_of_lt hd2 hlt
  have hi : (x - y) i = 0 := by
    rw [← ZMod.natCast_zmod_val ((x - y) i), hval]
    simp
  have hsub : (x - y) i = x i - y i := rfl
  rw [hsub] at hi
  exact sub_eq_zero.mp hi

end Qatlib.Papers.LinearDiseq07.MainResults
