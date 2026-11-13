/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Element distinctness walk estimates

This module specializes the unique collision walk bounds to pairs of marked indices, following
the element distinctness application in [Ambainis2005]. The constants `edQueryConstant` and
`edThreshold` make the N^(2/3) query estimate and its size requirement explicit.

## Main statements

* `theorem42_element_distinctness`: Provides a walk iteration count with the stated query and
  marked amplitude bounds.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.WalkFind.UniqueCollision

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- The explicit real prefactor in the N^(2/3) query estimate for the pair collision walk. -/
noncomputable def edQueryConstant : ℝ :=
  1 + 16 * (Real.sqrt 2 * Real.pi / 6 + 1) * 3 * Real.pi * Real.sqrt (2 : ℝ) /
    ((Real.pi - 1) * Real.pi - 3) * (2 : ℝ) ^ (2 : ℝ)

/-- The explicit input size threshold used to specialize the unique collision estimate to two
marked indices. -/
noncomputable def edThreshold : ℝ :=
  (32 * Real.pi ^ 2 * ((2 : ℝ) ^ 3) * ((2 : ℕ) ^ (2 + 4)) *
    ((2 : ℝ) + 1) * (2 : ℝ)) ^ (2 + 1)

/-- Above the specified size threshold, every pair of marked indices possesses a walk iteration
count with query cost at most `edQueryConstant` times N^(2/3) and marked amplitude at least
`jwEpsArc 2 r ^ 3 / 1000`, where r = ⌊N^(2/3)⌋. See [Ambainis2005]. -/
theorem theorem42_element_distinctness :
    ∀ N : ℕ, edThreshold ≤ (N : ℝ) → ∀ I : Finset (Fin N), I.card = 2 →
      let r : ℕ := Nat.floor ((N : ℝ) ^ ((2 : ℝ) / 3))
      ∃ t1 : ℕ,
        ((r + 2 * t1 * jwT2 2 r : ℕ) : ℝ) ≤
          edQueryConstant * (N : ℝ) ^ ((2 : ℝ) / 3) ∧
        jwEpsArc 2 r ^ 3 / 1000 ≤ ‖jwMarkedAmplitude 2 N r t1 (jwT2 2 r) I‖ := by
  intro N hN I hI
  have h :=
    Qatlib.Concepts.WalkFind.UniqueCollision.queryComplexity 2 N
      (by norm_num) (by simpa [edThreshold] using hN) I hI
  have hexp : (2 : ℝ) / (2 + 1) = 2 / 3 := by norm_num
  simpa [edQueryConstant, hexp] using h

end Qatlib.Papers.QSearchSurvey05.MainResults
