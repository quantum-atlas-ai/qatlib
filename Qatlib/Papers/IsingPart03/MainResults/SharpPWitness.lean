/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPart03.MainResults.SpinGlass
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

abbrev Colour (m : ℕ) (b : E → ZMod 2) : Type _ := {e : E // b e ≠ 0} → Fin m

omit [DecidableEq E] in

lemma card_colourDomain (b : E → ZMod 2) :
    Fintype.card {e : E // b e ≠ 0} = suppCard b := by
  classical
  rw [suppCard, Fintype.card_subtype, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  rcases eq_zero_or_one (b e) with h | h <;> simp [h]

lemma colour_card_eq_pow (m : ℕ) (b : E → ZMod 2) :
    ((Fintype.card (Colour (E := E) m b) : ℕ) : ℂ) = (m : ℂ) ^ suppCard b := by
  rw [Fintype.card_fun, card_colourDomain]
  push_cast
  simp

def witnessCount (ends : E → V × V) (w : E → ZMod 2) (m : ℕ) (s : ZMod 2) : ℕ :=
  ∑ b : E → ZMod 2,
    if parity ends b = 0 ∧ bDotW b w = s then Fintype.card (Colour (E := E) m b) else 0

theorem source_corollary1_signed_witness_count (ends : E → V × V) (w : E → ZMod 2)
    (m : ℕ) :
    qwgt (incidence ends) (dg w) (m : ℂ) 1
      = (witnessCount ends w m 0 : ℂ) - (witnessCount ends w m 1 : ℂ) := by
  classical
  rw [qwgt_incidence_dg]
  have hstep : ∀ b : E → ZMod 2,
      (if parity ends b = 0 then sgn (bDotW b w) * (m : ℂ) ^ suppCard b else 0)
        = (if parity ends b = 0 ∧ bDotW b w = 0 then ((Fintype.card (Colour (E := E) m b) : ℕ) : ℂ) else 0)
          - (if parity ends b = 0 ∧ bDotW b w = 1 then ((Fintype.card (Colour (E := E) m b) : ℕ) : ℂ) else 0) := by
    intro b
    rw [colour_card_eq_pow]
    rcases eq_zero_or_one (bDotW b w) with h | h <;>
      by_cases hp : parity ends b = 0 <;> simp [h, hp, sgn]
  rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_sub_distrib, witnessCount,
    witnessCount]
  push_cast
  ring

end Qatlib.Papers.IsingPart03.MainResults
