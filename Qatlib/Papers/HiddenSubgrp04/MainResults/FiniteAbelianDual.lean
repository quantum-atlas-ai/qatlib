/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.DirectSum.AddChar
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Tactic
public import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
public import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality

@[expose] public section

/-!
# Duality and annihilators of finite abelian groups

This module constructs duality equivalences for direct sums and finite products of cyclic
groups, yielding the finite abelian self-duality statement `theorem3_7`. It also identifies
characters of a quotient with the subgroup annihilator via `quotientCharEquiv`, and proves the
double-annihilator identity `theorem3_10_double`.

The development follows [Lomont2004].

## Main statements

* `theorem3_7`: Every finite abelian group possesses an additive equivalence with its complex
  character group.
* `quotientCharEquiv`: The additive equivalence between characters of `G ⧸ H` and the character
  annihilator of `H`.
* `theorem3_10_double`: The double character annihilator of a subgroup of a finite abelian group
  equals that subgroup.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

open scoped BigOperators DirectSum

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.HspRecovery.BackendAudit

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

variable {ι : Type*}

/-- The additive homomorphism restricting a character of a direct sum to each summand. -/
def restrictCharHom (A : ι → Type*) [∀ i, AddCommGroup (A i)] [DecidableEq ι] :
    AddChar (⨁ i, A i) ℂ →+ (∀ i, AddChar (A i) ℂ) where
  toFun χ i := χ.compAddMonoidHom (DirectSum.of A i)
  map_zero' := by
    ext i x
    simp
  map_add' χ ψ := by
    ext i x
    simp

/-- Reconstructing a direct-sum character from its restrictions to the summands returns the
original character. -/
theorem directSum_restrictCharHom (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    [DecidableEq ι] (χ : AddChar (⨁ i, A i) ℂ) :
    AddChar.directSum (fun i => χ.compAddMonoidHom (DirectSum.of A i)) = χ := by
  apply AddChar.toAddMonoidHomEquiv.injective
  apply DirectSum.addHom_ext
  intro i x
  simp [AddChar.directSum]

/-- Restriction to the summands is a bijection between direct-sum characters and families of
characters. -/
theorem restrictCharHom_bijective (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    [DecidableEq ι] : Function.Bijective (restrictCharHom A) := by
  constructor
  · intro χ ψ h
    have hh := congrArg (fun F => AddChar.directSum F) h
    simpa [restrictCharHom, directSum_restrictCharHom] using hh
  · intro F
    refine ⟨AddChar.directSum F, ?_⟩
    ext i x
    simp [restrictCharHom, AddChar.directSum]

/-- The additive equivalence between characters of a direct sum and the family of character
groups of its summands. -/
def dualDirectSumEquiv (A : ι → Type*) [∀ i, AddCommGroup (A i)] [DecidableEq ι] :
    AddChar (⨁ i, A i) ℂ ≃+ (∀ i, AddChar (A i) ℂ) :=
  AddEquiv.ofBijective (restrictCharHom A) (restrictCharHom_bijective A)

/-- The additive self-duality equivalence for a finite direct sum of residue groups with nonzero
moduli. -/
def zmodDirectSumDualEquiv [Fintype ι] [DecidableEq ι] (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) ≃+ AddChar (⨁ i, ZMod (n i)) ℂ :=
  (DirectSum.addEquivProd (fun i => ZMod (n i))).trans
    ((AddEquiv.piCongrRight (fun _i => AddChar.zmodAddEquiv)).trans
      (dualDirectSumEquiv (fun i => ZMod (n i))).symm)

/-- The additive equivalence on character groups induced contravariantly by an additive
equivalence of groups. -/
def pullbackCharEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) :
    AddChar H ℂ ≃+ AddChar G ℂ where
  toFun χ := χ.compAddMonoidHom (e : G →+ H)
  invFun χ := χ.compAddMonoidHom (e.symm : H →+ G)
  left_inv χ := by
    ext x
    simp
  right_inv χ := by
    ext x
    simp
  map_add' χ ψ := by
    ext x
    simp

/-- Every finite abelian group possesses an additive equivalence with its complex character
group ([Theorem 3.7][Lomont2004]). -/
theorem theorem3_7 (G : Type*) [AddCommGroup G] [Fintype G] :
    Nonempty (G ≃+ AddChar G ℂ) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let := hι
  have : DecidableEq ι := Classical.decEq ι
  have : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  exact ⟨e.trans ((zmodDirectSumDualEquiv n).trans (pullbackCharEquiv e))⟩

/-- A complex-valued additive character viewed as an additive homomorphism into the additive
type tag of the multiplicative monoid of complex numbers. -/
def charToAddHom {G : Type*} [AddCommGroup G] (ψ : AddChar G ℂ) : G →+ Additive ℂ where
  toFun g := Additive.ofMul (ψ g)
  map_zero' := by rw [AddChar.map_zero_eq_one]; rfl
  map_add' a b := by rw [AddChar.map_add_eq_mul]; rfl

/-- The additive homomorphism pulling quotient characters back to characters of `G` that are
trivial on `H`. -/
def restrictAnnHom {G : Type*} [AddCommGroup G] (H : AddSubgroup G) :
    AddChar (G ⧸ H) ℂ →+ characterAnnihilator H where
  toFun χ :=
    ⟨χ.compAddMonoidHom (QuotientAddGroup.mk' H), by
      rw [mem_characterAnnihilator]
      intro h
      change χ (QuotientAddGroup.mk' H (h : G)) = 1
      rw [QuotientAddGroup.mk'_apply,
        (QuotientAddGroup.eq_zero_iff (N := H) (h : G)).mpr h.property,
        AddChar.map_zero_eq_one]⟩
  map_zero' := by ext x; simp [AddChar.compAddMonoidHom]
  map_add' a b := by ext x; simp [AddChar.compAddMonoidHom]

/-- The character of `G ⧸ H` induced by a character of `G` belonging to the annihilator of `H`. -/
def liftChar {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (ψ : characterAnnihilator H) : AddChar (G ⧸ H) ℂ :=
  let L := QuotientAddGroup.lift H (charToAddHom ψ.val) (by
    intro h hh
    show charToAddHom ψ.val h = 0
    exact ofMul_eq_zero.mpr
      ((mem_characterAnnihilator H ψ.val).mp ψ.property ⟨h, hh⟩))
  { toFun := fun q => (L q).toMul
    map_zero_eq_one' := by simp only [map_zero, toMul_zero]
    map_add_eq_mul' := by intro a b; simp only [map_add, toMul_add] }

/-- Evaluating a lifted annihilator character on the quotient class of `g` returns its original
value at `g`. -/
@[simp] theorem liftChar_apply {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (ψ : characterAnnihilator H) (g : G) :
    liftChar H ψ (g : G ⧸ H) = ψ.val g := by
  change ((QuotientAddGroup.lift H (charToAddHom ψ.val) _) (g : G ⧸ H)).toMul = ψ.val g
  rw [QuotientAddGroup.lift_mk']
  rfl

/-- The additive homomorphism descending annihilator characters to the quotient group. -/
def liftAnnHom {G : Type*} [AddCommGroup G] (H : AddSubgroup G) :
    characterAnnihilator H →+ AddChar (G ⧸ H) ℂ where
  toFun := liftChar H
  map_zero' := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    simp [liftChar_apply]
  map_add' a b := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    simp [liftChar_apply]

/-- Descending a quotient character after pulling it back returns the original quotient
character. -/
theorem lift_restrict {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (χ : AddChar (G ⧸ H) ℂ) :
    liftAnnHom H (restrictAnnHom H χ) = χ := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective H q
  simp [liftAnnHom, liftChar_apply, restrictAnnHom, AddChar.compAddMonoidHom]

/-- Pulling back a descended annihilator character returns the original annihilator character. -/
theorem restrict_lift {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (ψ : characterAnnihilator H) :
    restrictAnnHom H (liftAnnHom H ψ) = ψ := by
  ext g
  simp [liftAnnHom, liftChar_apply, restrictAnnHom, AddChar.compAddMonoidHom]

/-- Pullback from quotient characters to the subgroup annihilator is bijective. -/
theorem restrictAnnHom_bijective {G : Type*} [AddCommGroup G] (H : AddSubgroup G) :
    Function.Bijective (restrictAnnHom H) :=
  ⟨fun a b hab => by
      have h := congrArg (liftAnnHom H) hab
      rwa [lift_restrict, lift_restrict] at h,
    fun ψ => ⟨liftAnnHom H ψ, restrict_lift H ψ⟩⟩

/-- The additive equivalence between characters of `G ⧸ H` and the character annihilator of `H`. -/
noncomputable def quotientCharEquiv {G : Type*} [AddCommGroup G] (H : AddSubgroup G) :
    AddChar (G ⧸ H) ℂ ≃+ characterAnnihilator H :=
  AddEquiv.ofBijective (restrictAnnHom H) (restrictAnnHom_bijective H)

/-- For a finite abelian group, the quotient by `H` possesses an additive equivalence with the
character annihilator of `H` ([Theorem 3.10][Lomont2004]). -/
theorem theorem3_10_quotient (G : Type*) [AddCommGroup G] [Fintype G]
    (H : AddSubgroup G) :
    Nonempty ((G ⧸ H) ≃+ characterAnnihilator H) := by
  classical
  have : Fintype (G ⧸ H) :=
    Fintype.ofSurjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  obtain ⟨e⟩ := theorem3_7 (G ⧸ H)
  exact ⟨e.trans (quotientCharEquiv H)⟩

/-- The double character annihilator of a subgroup of a finite abelian group equals that
subgroup ([Theorem 3.10][Lomont2004]). -/
theorem theorem3_10_double (G : Type*) [AddCommGroup G] [Fintype G]
    (H : AddSubgroup G) :
    doubleCharacterAnnihilator H = H :=
  doubleCharacterAnnihilator_eq H

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
