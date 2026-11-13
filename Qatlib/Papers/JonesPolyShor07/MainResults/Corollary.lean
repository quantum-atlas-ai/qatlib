/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Density.Proposition3

/-!
# Reversal equivalence for Fibonacci endpoint sectors

`mirrorString` reverses a Boolean string and preserves the condition `NoAdj`. Restricting
reversal to the endpoint sectors gives `spBasisEquivPsBasis` and hence equality of the
cardinalities of `SPBasis` and `PSBasis`. See [ShorJordan2008].

## Main statements

* `spBasisEquivPsBasis`: The equivalence between the SP and PS basis sectors induced by string
  reversal.
* `card_spBasis_eq_card_psBasis`: The SP and PS basis sectors have equal finite cardinality.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Corollary

open Definitions

/-- The Boolean string obtained by reversing the finite index order. -/
def mirrorString {n : ℕ} (s : Fin (n + 1) → Bool) : Fin (n + 1) → Bool := fun i => s (Fin.rev i)

/-- Reversing a Boolean string twice returns the original string. -/
theorem mirrorString_involutive {n : ℕ} (s : Fin (n + 1) → Bool) :
    mirrorString (mirrorString s) = s := by
  funext i
  simp [mirrorString]

/-- Reversal preserves the property that adjacent entries are never both true; see
[ShorJordan2008]. -/
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

/-- Reversal maps the SP endpoint sector to the PS endpoint sector. -/
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

/-- Reversal maps the PS endpoint sector to the SP endpoint sector. -/
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

/-- The equivalence between the SP and PS basis sectors induced by string reversal; see
[ShorJordan2008]. -/
def spBasisEquivPsBasis (n : ℕ) : SPBasis n ≃ PSBasis n where
  toFun := spToPs
  invFun := psToSp
  left_inv s := Subtype.ext (mirrorString_involutive s.1)
  right_inv s := Subtype.ext (mirrorString_involutive s.1)

/-- The SP and PS basis sectors have equal finite cardinality; see [ShorJordan2008]. -/
theorem card_spBasis_eq_card_psBasis (n : ℕ) :
    Fintype.card (SPBasis n) = Fintype.card (PSBasis n) :=
  Fintype.card_congr (spBasisEquivPsBasis n)

end Qatlib.Papers.JonesPolyShor07.MainResults.Corollary
