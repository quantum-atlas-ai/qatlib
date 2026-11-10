/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Density.Proposition3
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Corollary

open Definitions

def mirrorString {n : ℕ} (s : Fin (n + 1) → Bool) : Fin (n + 1) → Bool := fun i => s (Fin.rev i)

theorem mirrorString_involutive {n : ℕ} (s : Fin (n + 1) → Bool) :
    mirrorString (mirrorString s) = s := by
  funext i
  simp [mirrorString]

theorem noAdj_mirrorString {n : ℕ} {s : Fin (n + 1) → Bool} (h : NoAdj s) :
    NoAdj (mirrorString s) := by
  intro i j hij
  have hval : (Fin.rev i).val = (Fin.rev j).val + 1 := by
    rw [Fin.val_rev, Fin.val_rev]
    omega
  have h' : ¬(s (Fin.rev i) = true ∧ s (Fin.rev j) = true) := by
    have hh := h (Fin.rev j) (Fin.rev i) hval
    tauto
  simpa [mirrorString] using h'

def spToPs {n : ℕ} (s : SPBasis n) : PSBasis n :=
  ⟨mirrorString s.1, by
    obtain ⟨f, h0, hn, hno⟩ := s
    refine ⟨?_, ?_, ?_⟩
    · show f ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)).rev) = false
      rw [show (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 from rfl, Fin.rev_zero]
      exact hn
    · show f ((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).rev) = true
      rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, Fin.rev_last]
      exact h0
    · exact noAdj_mirrorString hno⟩

def psToSp {n : ℕ} (s : PSBasis n) : SPBasis n :=
  ⟨mirrorString s.1, by
    obtain ⟨f, h0, hn, hno⟩ := s
    refine ⟨?_, ?_, ?_⟩
    · show f ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)).rev) = true
      rw [show (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 from rfl, Fin.rev_zero]
      exact hn
    · show f ((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).rev) = false
      rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, Fin.rev_last]
      exact h0
    · exact noAdj_mirrorString hno⟩

def spBasisEquivPsBasis (n : ℕ) : SPBasis n ≃ PSBasis n where
  toFun := spToPs
  invFun := psToSp
  left_inv s := Subtype.ext (mirrorString_involutive s.1)
  right_inv s := Subtype.ext (mirrorString_involutive s.1)

theorem card_spBasis_eq_card_psBasis (n : ℕ) :
    Fintype.card (SPBasis n) = Fintype.card (PSBasis n) :=
  Fintype.card_congr (spBasisEquivPsBasis n)

end Qatlib.Papers.JonesPolyShor07.MainResults.Corollary
