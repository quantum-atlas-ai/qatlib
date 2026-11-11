/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# A concrete q-hedral semidirect product

Defines a multiplier family `MultFamily p q` and the associated group `QHG M` on pairs of
residues modulo `p` and `q`. The module gives coordinate formulas for its group operations,
identifies the normal translation subgroup as a kernel, and computes the relevant cardinalities
and the distinguished multiplier order. See [MooreEtAl2002].

## Main statements

* `QHG`: the semidirect-product group determined by a multiplier family.
* `translations_eq_ker`: translations are the kernel of the exponent projection.
* `orderOf_multiplier`: the distinguished multiplier has order `q`.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

/-- A family of units indexed by `ZMod q` that sends addition of indices to multiplication of
units. -/
structure MultFamily (p q : ℕ) where
  m : ZMod q → (ZMod p)ˣ
  map_add : ∀ s u, m (s + u) = m s * m u

namespace MultFamily

variable {p q : ℕ} (M : MultFamily p q)

/-- A multiplier family takes the zero exponent to the identity unit. -/
@[simp] theorem m_zero : M.m 0 = 1 := by
  have h : M.m 0 = M.m 0 * M.m 0 := by simpa using M.map_add 0 0
  have h2 : M.m 0 * 1 = M.m 0 * M.m 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

/-- A multiplier family takes the negative of an exponent to the inverse unit. -/
theorem m_neg (s : ZMod q) : M.m (-s) = (M.m s)⁻¹ := by
  have h := M.map_add s (-s)
  rw [add_neg_cancel, m_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The multiplier family sending a residue `s` modulo nonzero `q` to `a^s.val`, given `a^q =
1`. -/
def ofUnit (p q : ℕ) [NeZero q] (a : (ZMod p)ˣ) (ha : a ^ q = 1) :
    MultFamily p q where
  m s := a ^ s.val
  map_add s u := by
    have hq : orderOf a ∣ q := orderOf_dvd_iff_pow_eq_one.mpr ha
    have hm : (s.val + u.val) % q ≡ s.val + u.val [MOD orderOf a] :=
      Nat.ModEq.of_dvd hq (Nat.mod_modEq (s.val + u.val) q)
    rw [ZMod.val_add, pow_eq_pow_iff_modEq.mpr hm, pow_add]

/-- The family constructed from `a` takes exponent one to `a`. -/
theorem ofUnit_m_one (p q : ℕ) [NeZero q] (a : (ZMod p)ˣ) (ha : a ^ q = 1) :
    (ofUnit p q a ha).m 1 = a := by
  change a ^ (1 : ZMod q).val = a
  by_cases hq1 : q = 1
  · subst hq1
    rw [ZMod.val_one_eq_one_mod, Nat.mod_one, pow_zero]
    rw [pow_one] at ha
    exact ha.symm
  · rw [ZMod.val_one'' hq1, pow_one]

end MultFamily

/-- The pair of translation and exponent coordinates underlying the semidirect product
determined by `M`. -/
structure QHG {p q : ℕ} (M : MultFamily p q) where

  x : ZMod p

  s : ZMod q

namespace QHG

variable {p q : ℕ} (M : MultFamily p q)

/-- Two elements of `QHG M` are equal if both coordinates agree. -/
@[ext] theorem ext {a b : QHG M} (hx : a.x = b.x) (hs : a.s = b.s) : a = b := by
  cases a; cases b; simp_all

instance instGroup : Group (QHG M) where
  mul a b := ⟨a.x + (M.m a.s : ZMod p) * b.x, a.s + b.s⟩
  one := ⟨0, 0⟩
  inv a := ⟨-(((M.m a.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * a.x, -a.s⟩
  mul_assoc := by
    intro x y z
    ext
    · show (x.x + (M.m x.s : ZMod p) * y.x)
          + (M.m (x.s + y.s) : ZMod p) * z.x
          = x.x + (M.m x.s : ZMod p) * (y.x + (M.m y.s : ZMod p) * z.x)
      rw [M.map_add, Units.val_mul]
      ring
    · show x.s + y.s + z.s = x.s + (y.s + z.s)
      ring
  one_mul := by
    intro x
    ext
    · show (0 : ZMod p) + (M.m 0 : ZMod p) * x.x = x.x
      rw [M.m_zero, Units.val_one]
      ring
    · show (0 : ZMod q) + x.s = x.s
      ring
  mul_one := by
    intro x
    ext
    · show x.x + (M.m x.s : ZMod p) * 0 = x.x
      ring
    · show x.s + 0 = x.s
      ring
  inv_mul_cancel := by
    intro x
    ext
    · show -(((M.m x.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * x.x
          + (M.m (-x.s) : ZMod p) * x.x = 0
      rw [M.m_neg]
      ring
    · show -x.s + x.s = 0
      ring

/-- The translation coordinate of a product is `a.x + M.m a.s * b.x`. -/
@[simp] theorem mul_x (a b : QHG M) :
    (a * b).x = a.x + (M.m a.s : ZMod p) * b.x := rfl

/-- The exponent coordinate of a product is the sum of the exponent coordinates. -/
@[simp] theorem mul_s (a b : QHG M) : (a * b).s = a.s + b.s := rfl

/-- The translation coordinate of the group identity is zero. -/
@[simp] theorem one_x : (1 : QHG M).x = 0 := rfl

/-- The exponent coordinate of the group identity is zero. -/
@[simp] theorem one_s : (1 : QHG M).s = 0 := rfl

/-- The translation coordinate of an inverse is the negative of the original translation
multiplied by the inverse multiplier. -/
@[simp] theorem inv_x (a : QHG M) :
    a⁻¹.x = -(((M.m a.s)⁻¹ : (ZMod p)ˣ) : ZMod p) * a.x := rfl

/-- The exponent coordinate of an inverse is the negative of the original exponent. -/
@[simp] theorem inv_s (a : QHG M) : a⁻¹.s = -a.s := rfl

/-- The equivalence between `QHG M` and the product of its two residue-coordinate types. -/
def equivProd : QHG M ≃ ZMod p × ZMod q where
  toFun a := (a.x, a.s)
  invFun y := ⟨y.1, y.2⟩
  left_inv a := by cases a; rfl
  right_inv y := rfl

instance instFintype [NeZero p] [NeZero q] : Fintype (QHG M) :=
  Fintype.ofEquiv (ZMod p × ZMod q) (equivProd M).symm

/-- For nonzero `p` and `q`, the group `QHG M` has cardinality `p * q`. -/
theorem card [NeZero p] [NeZero q] : Fintype.card (QHG M) = p * q := by
  rw [Fintype.card_congr (equivProd M), Fintype.card_prod, ZMod.card, ZMod.card]

/-- The group homomorphism projecting onto the exponent coordinate, viewed multiplicatively. -/
def proj : QHG M →* Multiplicative (ZMod q) where
  toFun a := Multiplicative.ofAdd a.s
  map_one' := rfl
  map_mul' := by intro x y; rfl

/-- An element is in the kernel of the exponent projection exactly when its exponent coordinate
is zero. -/
theorem mem_ker_proj_iff (a : QHG M) :
    a ∈ (proj M).ker ↔ a.s = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd a.s = 1 ↔ a.s = 0
  rw [ofAdd_eq_one]

/-- The subgroup consisting of elements with zero exponent coordinate. -/
def translations : Subgroup (QHG M) where
  carrier := {a | a.s = 0}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    have ha' : a.s = 0 := ha
    have hb' : b.s = 0 := hb
    show a.s + b.s = 0
    rw [ha', hb', add_zero]
  inv_mem' := by
    intro a ha
    have ha' : a.s = 0 := ha
    show -a.s = 0
    rw [ha', neg_zero]

/-- The translation subgroup equals the kernel of the exponent projection. -/
theorem translations_eq_ker : translations M = (proj M).ker := by
  ext a
  rw [mem_ker_proj_iff]
  rfl

/-- The translation subgroup of `QHG M` is normal. -/
theorem translations_normal : (translations M).Normal := by
  rw [translations_eq_ker]
  infer_instance

/-- The equivalence between the translation subgroup and `ZMod p` given by the translation
coordinate. -/
def translationsEquiv [NeZero p] [NeZero q] : translations M ≃ ZMod p where
  toFun a := a.1.x
  invFun z := ⟨⟨z, 0⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    ext
    · rfl
    · show (0 : ZMod q) = a.1.s
      exact a.2.symm
  right_inv z := rfl

instance instFintypeTranslations [NeZero p] [NeZero q] : Fintype (translations M) :=
  Fintype.ofEquiv (ZMod p) (translationsEquiv M).symm

/-- For nonzero `p` and `q`, the translation subgroup has cardinality `p`. -/
theorem card_translations [NeZero p] [NeZero q] :
    Fintype.card (translations M) = p := by
  rw [Fintype.card_congr (translationsEquiv M), ZMod.card]

/-- The `k`th natural power of the distinguished multiplier has translation zero and exponent
`k` modulo `q`. -/
theorem pow_multiplier (k : ℕ) :
    ((⟨0, 1⟩ : QHG M)) ^ k = ⟨0, (k : ZMod q)⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp [Nat.cast_add, Nat.cast_one]

/-- For nonzero `q`, the distinguished multiplier has order `q`. -/
theorem orderOf_multiplier [NeZero q] :
    orderOf ((⟨0, 1⟩ : QHG M)) = q := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_multiplier]
    ext <;> simp
  · rw [← ZMod.natCast_eq_zero_iff]
    have h := pow_orderOf_eq_one ((⟨0, 1⟩ : QHG M))
    rw [pow_multiplier] at h
    have h2 := congrArg QHG.s h
    simpa using h2

end QHG

end Qatlib.Papers.AffineHSP02.MainResults
