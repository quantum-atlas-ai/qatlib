/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

variable {G : Type*} [Group G]

theorem subset_normalClosure_iff {N : Subgroup G} [N.Normal] {s : Set G} :
    s ⊆ N ↔ Subgroup.normalClosure s ≤ N :=
  Subgroup.normalClosure_subset_iff

theorem eq_of_le_of_index_eq {H K : Subgroup G} (hle : H ≤ K)
    (hK : K.index ≠ 0) (hidx : H.index = K.index) : H = K := by
  refine le_antisymm hle ?_
  have hmul : H.relIndex K * K.index = K.index := by
    rw [Subgroup.relIndex_mul_index hle, hidx]
  have hrel : H.relIndex K = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK) (by simpa using hmul)
  exact (Subgroup.relIndex_eq_one).1 hrel

theorem normalClosure_eq_of_index_eq {N : Subgroup G} [N.Normal] {s : Set G}
    (hle : Subgroup.normalClosure s ≤ N) (hN : N.index ≠ 0)
    (hidx : (Subgroup.normalClosure s).index = N.index) :
    Subgroup.normalClosure s = N :=
  eq_of_le_of_index_eq hle hN hidx

theorem hidden_normal_eq_stabilizer {X : Type*} (I : HiddenSubgroupInstance G X) :
    I.H = {a : G | I.f a = I.f 1} := by
  ext a
  exact I.mem_iff_f_eq_one a

end Qatlib.Papers.NonAbelianHSP01.MainResults
