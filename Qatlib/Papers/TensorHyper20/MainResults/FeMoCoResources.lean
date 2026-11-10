/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.FeMoCoResources

def spacetime (qubits toffolis : ℕ) : ℕ := qubits * toffolis

theorem reiher_spacetime_reduction :
    (3 : ℚ) ≤ (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ∧
      (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ≤ 7 / 2 := by
  norm_num [spacetime]

theorem li_spacetime_reduction :
    (29 / 5 : ℚ) ≤ (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) ∧
      (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) ≤ 6 := by
  norm_num [spacetime]

theorem feMoCo_spacetime_reduction :
    (3 : ℚ) ≤ (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ∧
      (29 / 5 : ℚ) ≤
        (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) :=
  ⟨reiher_spacetime_reduction.1, li_spacetime_reduction.1⟩

end Qatlib.Papers.TensorHyper20.MainResults.FeMoCoResources
