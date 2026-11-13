/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Characters and orthogonal subgroups of the Boolean cube

This module constructs the additive characters of `BooleanVec n` from the bilinear form
`booleanDot`. The equivalence `booleanCharacterEquiv` identifies vectors with characters, and
`booleanOrthogonal` corresponds to a subgroup's character annihilator. This specializes finite
abelian character duality [Lomont2004]. Binary linear algebra in stabilizer theory gives context
for these constructions in [DehaeneDeMoor2003].

## Main statements

* `booleanCharacterHom_injective` shows that a vector is determined by its character.
* `booleanCharacterEquiv` identifies the Boolean cube with its complex character group.
* `booleanCharacter_mem_characterAnnihilator_iff` characterizes triviality on a subgroup by
  vanishing Boolean dot products.

## References

* [Lomont, 2004][Lomont2004]
* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.PauliClifford.ExactRank

open scoped Classical

/-- The vector space of `n` coordinates over `ZMod 2`, represented by functions from `Fin n`. -/
abbrev BooleanVec (n : ℕ) := Fin n → ZMod 2

/-- Defines the Boolean dot product as the sum of coordinatewise products in `ZMod 2`. -/
def booleanDot {n : ℕ} (a x : BooleanVec n) : ZMod 2 :=
  ∑ i, a i * x i

/-- Packages the Boolean dot product with a fixed vector `a` as an additive homomorphism to
`ZMod 2`. -/
def booleanDotHom {n : ℕ} (a : BooleanVec n) : BooleanVec n →+ ZMod 2 where
  toFun := booleanDot a
  map_zero' := by simp [booleanDot]
  map_add' x y := by
    simp only [booleanDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Defines the complex additive character obtained by composing `booleanDotHom a` with the
standard additive character of `ZMod 2`. -/
noncomputable def booleanCharacter {n : ℕ} (a : BooleanVec n) : AddChar (BooleanVec n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (booleanDotHom a)

/-- Evaluating `booleanCharacter a` at `x` gives the standard additive character of `booleanDot
a x`. -/
@[simp] theorem booleanCharacter_apply {n : ℕ} (a x : BooleanVec n) :
    booleanCharacter a x = ZMod.stdAddChar (booleanDot a x) := rfl

/-- Packages the assignment of a Boolean vector to its complex character as an additive
homomorphism into the character group. -/
noncomputable def booleanCharacterHom (n : ℕ) : BooleanVec n →+ AddChar (BooleanVec n) ℂ where
  toFun := booleanCharacter
  map_zero' := by
    ext x
    simp [booleanCharacter_apply, booleanDot]
  map_add' a b := by
    ext x
    simp only [booleanCharacter_apply, booleanDot, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, AddChar.add_apply]
    rw [ZMod.stdAddChar.map_add_eq_mul]

/-- Distinct Boolean vectors define distinct complex additive characters. -/
theorem booleanCharacterHom_injective (n : ℕ) :
    Function.Injective (booleanCharacterHom n) := by
  intro a b hab
  funext i
  have hi := DFunLike.congr_fun hab (Pi.single i (1 : ZMod 2))
  have hz : booleanDot a (Pi.single i (1 : ZMod 2)) =
      booleanDot b (Pi.single i (1 : ZMod 2)) :=
    ZMod.injective_stdAddChar (by simpa [booleanCharacterHom] using hi)
  have ha_single : booleanDot a (Pi.single i (1 : ZMod 2)) = a i := by
    rw [booleanDot, Fintype.sum_eq_single i (fun j hji => by
      rw [Pi.single_eq_of_ne hji, mul_zero]), Pi.single_eq_same, mul_one]
  have hb_single : booleanDot b (Pi.single i (1 : ZMod 2)) = b i := by
    rw [booleanDot, Fintype.sum_eq_single i (fun j hji => by
      rw [Pi.single_eq_of_ne hji, mul_zero]), Pi.single_eq_same, mul_one]
  rwa [ha_single, hb_single] at hz

/-- Identifies the additive group of Boolean vectors with its group of complex additive
characters via the Boolean dot product. This is the Boolean-vector instance of finite
abelian character duality [Lomont, Theorem 3.7][Lomont2004]. -/
noncomputable def booleanCharacterEquiv (n : ℕ) :
    BooleanVec n ≃+ AddChar (BooleanVec n) ℂ := by
  refine AddEquiv.ofBijective (booleanCharacterHom n) ?_
  rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
  exact ⟨booleanCharacterHom_injective n, rfl⟩

/-- The character equivalence sends `a` to the explicitly defined character `booleanCharacter
a`. -/
@[simp] theorem booleanCharacterEquiv_apply {n : ℕ} (a : BooleanVec n) :
    booleanCharacterEquiv n a = booleanCharacter a := rfl

/-- Defines the subgroup of Boolean vectors whose dot product vanishes on every element of `H`. -/
def booleanOrthogonal {n : ℕ} (H : AddSubgroup (BooleanVec n)) :
    AddSubgroup (BooleanVec n) where
  carrier := {a | ∀ h : H, booleanDot a h = 0}
  zero_mem' := by simp [booleanDot]
  add_mem' := by
    intro a b ha hb h
    change booleanDot (a + b) h = 0
    rw [show booleanDot (a + b) h = booleanDot a h + booleanDot b h by
      simp [booleanDot, add_mul, Finset.sum_add_distrib]]
    rw [ha h, hb h, add_zero]
  neg_mem' := by
    intro a ha h
    change booleanDot (-a) h = 0
    rw [show booleanDot (-a) h = -booleanDot a h by
      simp [booleanDot]]
    rw [ha h, neg_zero]

/-- Membership in `booleanOrthogonal H` means that the Boolean dot product vanishes against
every element of `H`. -/
@[simp] theorem mem_booleanOrthogonal {n : ℕ} (H : AddSubgroup (BooleanVec n))
    (a : BooleanVec n) :
    a ∈ booleanOrthogonal H ↔ ∀ h : H, booleanDot a h = 0 :=
  Iff.rfl

/-- The character associated with `a` is trivial on `H` exactly when `a` lies in the Boolean
orthogonal subgroup of `H`. -/
theorem booleanCharacter_mem_characterAnnihilator_iff {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) (a : BooleanVec n) :
    booleanCharacter a ∈ characterAnnihilator H ↔ a ∈ booleanOrthogonal H := by
  rw [mem_characterAnnihilator, mem_booleanOrthogonal]
  constructor
  · intro ha h
    apply ZMod.injective_stdAddChar
    simpa [booleanCharacter_apply] using ha h
  · intro ha h
    rw [booleanCharacter_apply, ha h, AddChar.map_zero_eq_one]

/-- Under `booleanCharacterEquiv`, membership in the character annihilator of `H` corresponds
exactly to membership in `booleanOrthogonal H`. -/
theorem booleanCharacterEquiv_mem_characterAnnihilator_iff {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) (a : BooleanVec n) :
    booleanCharacterEquiv n a ∈ characterAnnihilator H ↔
      a ∈ booleanOrthogonal H := by
  rw [booleanCharacterEquiv_apply, booleanCharacter_mem_characterAnnihilator_iff]

end Qatlib.Concepts.PauliClifford.ExactRank
