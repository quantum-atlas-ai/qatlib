/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCellAutomata96.MainResults

def fockSector (N n : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard n

theorem fockSector_card (N n : ℕ) : (fockSector N n).card = N.choose n := by
  rw [fockSector, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem fock_total_dim (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (fockSector N n).card) = 2 ^ N := by
  simp_rw [fockSector_card]
  exact Nat.sum_range_choose N

theorem fock_one_particle_dim (N : ℕ) : (fockSector N 1).card = N := by
  rw [fockSector_card, Nat.choose_one_right]

theorem fock_two_particle_dim (N : ℕ) :
    (fockSector N 2).card = N * (N - 1) / 2 := by
  rw [fockSector_card, Nat.choose_two_right]

end Qatlib.Papers.QCellAutomata96.MainResults
