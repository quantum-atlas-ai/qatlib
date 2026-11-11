/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Representation.EquivUpToPhase

/-!
# Phase equivalence and label arithmetic for Theorem 3.2

This module packages the equivalence-relation properties of `RepEquivalentUpToPhase` and
elementary two-row label identities associated with Theorem 3.2 of [FreedmanLarsenWang2000].

The arithmetic results recover the sum and difference of the Jones row lengths, compute three
small labels, and handle the odd boundary-one case.

## Main statements

* `theorem3_2_equivalence_relation`: Unitary equivalence up to phase is an equivalence relation.
* `theorem3_2_part_one_label`: The Jones label has the prescribed sum and difference.
* `theorem3_2_part_two_label`: An odd boundary-one label has total size `n` and row difference
  one.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Matrix

/-- For matrix-valued maps on a group, `RepEquivalentUpToPhase` is an equivalence relation; see
[FreedmanLarsenWang2000]. -/
theorem theorem3_2_equivalence_relation (G : Type*) [Group G] (d : ℕ) :
    Equivalence (fun (ρ ρ' : G → CM d) => RepEquivalentUpToPhase ρ ρ') :=
  ⟨fun ρ => repEquivUpToPhase_refl ρ,
   fun h => repEquivUpToPhase_symm h,
   fun h1 h2 => repEquivUpToPhase_trans h1 h2⟩

/-- If `n ≤ m` and `m + n` is even, the row lengths of `jonesLabel m n` have sum `m` and
difference `n`; see [FreedmanLarsenWang2000]. -/
theorem theorem3_2_part_one_label (m n : ℕ) (hmn : (m + n) % 2 = 0) (hnm : n ≤ m) :
    (jonesLabel m n).1 + (jonesLabel m n).2 = m ∧
      (jonesLabel m n).1 - (jonesLabel m n).2 = n :=
  ⟨jonesLabel_sum hnm hmn, jonesLabel_diff hnm hmn⟩

/-- The label `jonesLabel 6 0` equals `(3, 3)`; see [FreedmanLarsenWang2000]. -/
theorem theorem3_2_part_one_six_zero : jonesLabel 6 0 = (3, 3) :=
  jonesLabel_six_zero

/-- The label `jonesLabel 6 2` equals `(4, 2)`; see [FreedmanLarsenWang2000]. -/
theorem theorem3_2_part_one_six_two : jonesLabel 6 2 = (4, 2) :=
  jonesLabel_six_two

/-- The label `jonesLabel 3 1` equals `(2, 1)`; see [FreedmanLarsenWang2000]. -/
theorem theorem3_2_part_one_three_one : jonesLabel 3 1 = (2, 1) :=
  jonesLabel_three_one

/-- For odd `n`, the row lengths `(n + 1) / 2` and `(n - 1) / 2` have sum `n` and difference
one; see [FreedmanLarsenWang2000]. -/
theorem theorem3_2_part_two_label (n : ℕ) (hn : n % 2 = 1) :
    ((n + 1) / 2) + ((n - 1) / 2) = n ∧
      ((n + 1) / 2) - ((n - 1) / 2) = 1 :=
  ⟨boundary_one_label_boxes n hn, boundary_one_label_diff n hn⟩

end Qatlib.Papers.ModularFunct00.MainResults.Representation
