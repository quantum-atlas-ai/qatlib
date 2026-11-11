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

/-!
# Dimensions of finite fermionic sectors

This module represents a fixed-particle sector by subsets of a finite site set with prescribed
cardinality. It counts these sectors by binomial coefficients and sums them to obtain the full
occupation-space dimension. See [Meyer1996a].

## Main statements

* `fockSector_card`: The fixed-`n` occupation sector on `N` sites has cardinality `N.choose n`.
* `fock_total_dim`: The sum of the sector dimensions for particle counts from zero through `N`
  is `2^N`.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The finite set of all `n`-element subsets of `N` sites. -/
def fockSector (N n : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard n

/-- The fixed-`n` occupation sector on `N` sites has cardinality `N.choose n`. See [Meyer1996a]. -/
theorem fockSector_card (N n : ℕ) : (fockSector N n).card = N.choose n := by
  rw [fockSector, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The sum of the sector dimensions for particle counts from zero through `N` is `2^N`. See
[Meyer1996a]. -/
theorem fock_total_dim (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (fockSector N n).card) = 2 ^ N := by
  simp_rw [fockSector_card]
  exact Nat.sum_range_choose N

/-- The one-particle occupation sector on `N` sites has dimension `N`. See [Meyer1996a]. -/
theorem fock_one_particle_dim (N : ℕ) : (fockSector N 1).card = N := by
  rw [fockSector_card, Nat.choose_one_right]

/-- The two-particle occupation sector on `N` sites has dimension `N * (N - 1) / 2`. See
[Meyer1996a]. -/
theorem fock_two_particle_dim (N : ℕ) :
    (fockSector N 2).card = N * (N - 1) / 2 := by
  rw [fockSector_card, Nat.choose_two_right]

end Qatlib.Papers.QCellAutomata96.MainResults
