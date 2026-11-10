/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.LinearSystem
set_option warningAsError false

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

def CostRestrictedSubgoal : Prop :=
  ∀ (κ ε : ℝ), 1 ≤ κ → 0 < ε →
    ∀ (M : ℕ), (M : ℝ) ≥ κ / ε →
      0 < 1 / κ ^ 2 ∧ (M : ℝ)⁻¹ ≤ ε / κ

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
