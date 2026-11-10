/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem2Stat
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem theorem2 : Theorem2 := by
  intro I _ _ w k l
  have hn : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨w⟩))
  funext i
  rw [applyGate_diffusion, sum_markedVector]
  simp only [Finset.card_singleton, Nat.cast_one]
  simp only [distinguishedAfterC, ordinaryAfterC, MarkedVector]
  split_ifs <;> field_simp <;> ring

end Qatlib.Concepts.SearchStopping.KnownCount
