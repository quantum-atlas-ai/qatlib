/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitCharacterCoordsSubgoalStat
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open scoped Classical BigOperators

variable (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in

private theorem addChar_eq_zero_of_generator_eq_one {k : ℕ} {V : Fin k → E}
    (hV : AddSubgroup.closure (Set.range V) = ⊤) {ψ : AddChar E ℂ}
    (hψ : ∀ j, ψ (V j) = 1) : ψ = 0 := by
  have htriv : ∀ g : E, g ∈ AddSubgroup.closure (Set.range V) → ψ g = 1 := by
    intro g hg
    induction hg using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact hψ j
    | zero => exact AddChar.map_zero_eq_one ψ
    | add x y _ _ ihx ihy =>
        rw [AddChar.map_add_eq_mul, ihx, ihy, one_mul]
    | neg x _ ihx =>
        have hinv : ψ (-x) = (ψ x)⁻¹ := eq_inv_of_mul_eq_one_left (by
          rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one])
        rw [hinv, ihx, inv_one]
  have hall : ∀ g : E, ψ g = 1 := fun g => htriv g (by rw [hV]; trivial)
  exact AddChar.eq_zero_iff.mpr hall

omit [DecidableEq E] in

private theorem addChar_apply_pow_card (χ : AddChar E ℂ) (x : E) :
    (χ x) ^ (Fintype.card E) = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

theorem orbitCharacterCoordsSubgoal : OrbitCharacterCoordsSubgoal := by
  intro E _ _ _ k V hV
  constructor
  · intro χ η h
    have hψ : ∀ j, (χ * η⁻¹) (V j) = 1 := by
      intro j
      rw [AddChar.mul_apply, AddChar.inv_apply, h j, ← AddChar.map_add_eq_mul,
        add_neg_cancel, AddChar.map_zero_eq_one]
    have := addChar_eq_zero_of_generator_eq_one E hV hψ
    rw [← AddChar.one_eq_zero] at this
    exact mul_inv_eq_one.mp this
  · intro χ j
    have hq : Fintype.card E ≠ 0 := Fintype.card_ne_zero
    haveI : NeZero (Fintype.card E) := ⟨hq⟩
    obtain ⟨i, hi, hpi⟩ :=
      (isPrimitiveRoot_primRoot hq).eq_pow_of_pow_eq_one (addChar_apply_pow_card E χ (V j))
    refine ⟨⟨i, hi⟩, ?_⟩
    show (χ (V j)) = primRoot (Fintype.card E) ^ ((i : ℕ) : ℤ)
    rw [zpow_natCast]
    exact hpi.symm

end Qatlib.Concepts.HspRecovery.AbelianSampling
