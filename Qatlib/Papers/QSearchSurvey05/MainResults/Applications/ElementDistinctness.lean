/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.WalkFind.UniqueCollision

namespace Qatlib.Papers.QSearchSurvey05.MainResults

noncomputable def edQueryConstant : ℝ :=
  1 + 16 * (Real.sqrt 2 * Real.pi / 6 + 1) * 3 * Real.pi * Real.sqrt (2 : ℝ) /
    ((Real.pi - 1) * Real.pi - 3) * (2 : ℝ) ^ (2 : ℝ)

noncomputable def edThreshold : ℝ :=
  (32 * Real.pi ^ 2 * ((2 : ℝ) ^ 3) * ((2 : ℕ) ^ (2 + 4)) *
    ((2 : ℝ) + 1) * (2 : ℝ)) ^ (2 + 1)

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
