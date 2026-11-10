/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
set_option warningAsError false

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open scoped Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def doubleCharacterAnnihilator (H : AddSubgroup G) : AddSubgroup G :=
  (characterAnnihilator (characterAnnihilator H)).comap AddChar.doubleDualEmb

theorem le_doubleCharacterAnnihilator (H : AddSubgroup G) :
    H ≤ doubleCharacterAnnihilator H := by
  intro x hx
  change AddChar.doubleDualEmb x ∈ characterAnnihilator (characterAnnihilator H)
  rw [mem_characterAnnihilator]
  intro χ
  change (χ : AddChar G ℂ) x = 1
  exact (mem_characterAnnihilator H (χ : AddChar G ℂ)).1 χ.property ⟨x, hx⟩

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

theorem doubleCharacterAnnihilator_eq (H : AddSubgroup G) :
    doubleCharacterAnnihilator H = H := by
  symm
  apply AddSubgroup.eq_of_le_of_card_ge (le_doubleCharacterAnnihilator H)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    card_doubleCharacterAnnihilator]

theorem doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff
    (H : AddSubgroup G) (x : G) :
    AddChar.doubleDualEmb x ∈ characterAnnihilator (characterAnnihilator H) ↔ x ∈ H := by
  change x ∈ doubleCharacterAnnihilator H ↔ x ∈ H
  rw [doubleCharacterAnnihilator_eq]

end Qatlib.Concepts.HspRecovery.BackendAudit
