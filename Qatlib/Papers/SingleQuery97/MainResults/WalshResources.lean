/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit
import Qatlib.Papers.SingleQuery97.MainResults.WalshProgram

/-!
# Walsh row weights and sparse encoding counts

This module counts the nonzero entries in complete Walsh label families. It proves that sparse
encoding contains `q * 2^(q-1)` components and that encoding followed by its negated pass uses
`N*q` gates, supplying exact implementation counts for Walsh search in [TerhalSmolin1998].

## Main statements

* `sparse_walsh_length`: The sparse generator list for a complete Walsh label family has length
  `q * 2^(q-1)`.
* `two_pass_walsh_count`: The sparse addition pass and its negated pass together have gate count
  `N*q` for a complete Walsh label family.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.WalshResources

open Qatlib.Foundations.QueryWordCore.Circuit
open EncoderCircuit WalshProgram

variable {N q : ℕ}

/-- Exactly `2^(q-1)` binary vectors have value `1` at any specified coordinate. -/
theorem cube_row_weight (i : Fin q) :
    (Finset.univ.filter (fun s : Fin q → ZMod 2 => s i = 1)).card = 2^(q-1) := by
  have h := Fintype.card_filter_piFinset_const_eq_of_mem
    (Finset.univ : Finset (ZMod 2)) i (Finset.mem_univ (1:ZMod 2))
  simpa using h

/-- Each row of the generator matrix for a bijective binary label family has exactly `2^(q-1)`
nonzero entries. -/
theorem walsh_row_weight (label : Fin N ≃ (Fin q → ZMod 2)) (i : Fin q) :
    (Finset.univ.filter (fun j => generators label i j ≠ 0)).card = 2^(q-1) := by
  classical
  have hb (b : ZMod 2) : b ≠ 0 ↔ b = 1 := by revert b; decide
  have he : {j : Fin N // generators label i j ≠ 0} ≃
      {s : Fin q → ZMod 2 // s i = 1} :=
    label.subtypeEquiv (fun j => hb (label j i))
  have hc := Fintype.card_congr he
  simpa only [Fintype.card_subtype, cube_row_weight] using hc

/-- The sparse generator list for a complete Walsh label family has length `q * 2^(q-1)`. -/
theorem sparse_walsh_length (label : Fin N ≃ (Fin q → ZMod 2)) :
    (sparseComponents (generators label)).length = q * 2^(q-1) := by
  simp only [sparseComponents, List.length_map, Finset.length_toList, support_card,
    walsh_row_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The sparse addition pass and its negated pass together have gate count `N*q` for a complete
Walsh label family. -/
theorem two_pass_walsh_count (label : Fin N ≃ (Fin q → ZMod 2)) :
    GateCount (additions (sparseComponents (generators label))) +
      GateCount (additions ((sparseComponents (generators label)).map Neg.neg)) = N*q := by
  rw [(additions_resources _).2, (additions_resources _).2, List.length_map, sparse_walsh_length]
  have hN : N=2^q := by simpa using Fintype.card_congr label
  rw [hN]
  by_cases hq : q=0
  · simp [hq]
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simp only [Nat.succ_sub_one, pow_succ]
    ring

end Qatlib.Papers.SingleQuery97.MainResults.WalshResources
