/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Representation.EquivUpToPhase
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Matrix

theorem theorem3_2_equivalence_relation (G : Type*) [Group G] (d : ℕ) :
    Equivalence (fun (ρ ρ' : G → CM d) => RepEquivalentUpToPhase ρ ρ') :=
  ⟨fun ρ => repEquivUpToPhase_refl ρ,
   fun h => repEquivUpToPhase_symm h,
   fun h1 h2 => repEquivUpToPhase_trans h1 h2⟩

theorem theorem3_2_part_one_label (m n : ℕ) (hmn : (m + n) % 2 = 0) (hnm : n ≤ m) :
    (jonesLabel m n).1 + (jonesLabel m n).2 = m ∧
      (jonesLabel m n).1 - (jonesLabel m n).2 = n :=
  ⟨jonesLabel_sum hnm hmn, jonesLabel_diff hnm hmn⟩

theorem theorem3_2_part_one_six_zero : jonesLabel 6 0 = (3, 3) :=
  jonesLabel_six_zero

theorem theorem3_2_part_one_six_two : jonesLabel 6 2 = (4, 2) :=
  jonesLabel_six_two

theorem theorem3_2_part_one_three_one : jonesLabel 3 1 = (2, 1) :=
  jonesLabel_three_one

theorem theorem3_2_part_two_label (n : ℕ) (hn : n % 2 = 1) :
    ((n + 1) / 2) + ((n - 1) / 2) = n ∧
      ((n + 1) / 2) - ((n - 1) / 2) = 1 :=
  ⟨boundary_one_label_boxes n hn, boundary_one_label_diff n hn⟩

end Qatlib.Papers.ModularFunct00.MainResults.Representation
