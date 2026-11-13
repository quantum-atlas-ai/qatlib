/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Double annihilators in finite abelian groups

This module identifies a subgroup of a finite abelian group with its double character
annihilator, transported back along the canonical double dual embedding. The equivalence
`doubleCharacterAnnihilatorEquiv` and the cardinality identity yield
`doubleCharacterAnnihilator_eq`, which supports separation of elements outside the subgroup by
characters. [Lomont2004]

## Main statements

* `doubleCharacterAnnihilator_eq`: identifies the transported double annihilator with the
  original subgroup.
* `doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff`: characterizes double
  annihilator membership through the canonical embedding.

## References

* [Lomont, 2004][Lomont2004]
-/

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open scoped Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The double character annihilator of `H` transported to `G` by taking its preimage under the
canonical double dual embedding. -/
noncomputable def doubleCharacterAnnihilator (H : AddSubgroup G) : AddSubgroup G :=
  (characterAnnihilator (characterAnnihilator H)).comap AddChar.doubleDualEmb

/-- Every subgroup is contained in its transported double character annihilator. -/
theorem le_doubleCharacterAnnihilator (H : AddSubgroup G) :
    H ≤ doubleCharacterAnnihilator H := by
  intro x hx
  change AddChar.doubleDualEmb x ∈ characterAnnihilator (characterAnnihilator H)
  rw [mem_characterAnnihilator]
  intro χ
  change (χ : AddChar G ℂ) x = 1
  exact (mem_characterAnnihilator H (χ : AddChar G ℂ)).1 χ.property ⟨x, hx⟩

/-- The additive equivalence from the transported double annihilator to the double character
annihilator, induced by the canonical double dual equivalence. -/
noncomputable def doubleCharacterAnnihilatorEquiv (H : AddSubgroup G) :
    doubleCharacterAnnihilator H ≃+
      characterAnnihilator (characterAnnihilator H) where
  toFun x := ⟨AddChar.doubleDualEquiv x, by
    change AddChar.doubleDualEmb (x : G) ∈ characterAnnihilator (characterAnnihilator H)
    exact x.property⟩
  invFun χ := ⟨AddChar.doubleDualEquiv.symm χ, by
    change AddChar.doubleDualEmb (AddChar.doubleDualEquiv.symm χ) ∈
      characterAnnihilator (characterAnnihilator H)
    simpa using χ.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (AddChar.doubleDualEquiv : G ≃+ AddChar (AddChar G ℂ) ℂ).symm_apply_apply (x : G)
  right_inv χ := by
    apply Subtype.ext
    exact (AddChar.doubleDualEquiv : G ≃+ AddChar (AddChar G ℂ) ℂ).apply_symm_apply
      (χ : AddChar (AddChar G ℂ) ℂ)
  map_add' x y := by ext; simp

/-- The transported double character annihilator of a subgroup of a finite abelian group has the
same cardinality as the subgroup. -/
theorem card_doubleCharacterAnnihilator (H : AddSubgroup G) :
    Fintype.card (doubleCharacterAnnihilator H) = Fintype.card H := by
  have htransport : Fintype.card (doubleCharacterAnnihilator H) =
      Fintype.card (characterAnnihilator (characterAnnihilator H)) :=
    Fintype.card_congr (doubleCharacterAnnihilatorEquiv H).toEquiv
  have hfirst := card_characterAnnihilator H
  have hsecond := card_characterAnnihilator (characterAnnihilator H)
  have hmul :
      Fintype.card (characterAnnihilator (characterAnnihilator H)) *
          Fintype.card (characterAnnihilator H) =
        Fintype.card H * Fintype.card (characterAnnihilator H) := by
    calc
      _ = Fintype.card (AddChar G ℂ) := hsecond
      _ = Fintype.card G := AddChar.card_eq
      _ = Fintype.card (characterAnnihilator H) * Fintype.card H := hfirst.symm
      _ = _ := Nat.mul_comm _ _
  have hcard : Fintype.card (characterAnnihilator (characterAnnihilator H)) =
      Fintype.card H :=
    Nat.mul_right_cancel (Fintype.card_pos) hmul
  exact htransport.trans hcard

/-- For a subgroup of a finite abelian group, the double character annihilator transported along
the canonical double dual embedding equals the original subgroup [Lomont2004]. -/
theorem doubleCharacterAnnihilator_eq (H : AddSubgroup G) :
    doubleCharacterAnnihilator H = H := by
  symm
  apply AddSubgroup.eq_of_le_of_card_ge (le_doubleCharacterAnnihilator H)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    card_doubleCharacterAnnihilator]

/-- The double dual embedding of `x` belongs to the double character annihilator of `H` exactly
when `x` belongs to `H`. -/
theorem doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff
    (H : AddSubgroup G) (x : G) :
    AddChar.doubleDualEmb x ∈ characterAnnihilator (characterAnnihilator H) ↔ x ∈ H := by
  change x ∈ doubleCharacterAnnihilator H ↔ x ∈ H
  rw [doubleCharacterAnnihilator_eq]

end Qatlib.Concepts.HspRecovery.BackendAudit
