/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Reduction.DCPToTwoPoint
import Qatlib.Papers.QLattice03.MainResults.Lemma312
import Qatlib.Papers.QLattice03.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

theorem dcp_implies_uniqueSVP (f : ℝ) (_hf : 0 < f)
    (h312 : twoPoint_recovers_coefficient f) (h : HasDCPSolver f) :
    ∃ B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ), ThetaUniqueSVP (svpExponent f) B := by
  obtain ⟨A, hA⟩ := h
  have htp : HasTwoPointSolver f :=
    ⟨Reduction.dcpToTwoPoint A, Reduction.dcpToTwoPoint_correct A hA⟩
  obtain ⟨B, hB⟩ := h312 1 (by norm_num) htp
  exact ⟨B, 1, by norm_num, by simpa using hB⟩

end Qatlib.Papers.QLattice03.MainResults
