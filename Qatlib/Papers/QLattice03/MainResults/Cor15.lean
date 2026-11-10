/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Theorem13
import Qatlib.Papers.QLattice03.MainResults.Theorem11
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

theorem subsetSum_implies_uniqueSVP25 (h13 : subsetSum_implies_dcp)
    (h312 : twoPoint_recovers_coefficient 1) (S : SubsetSumRoutine) (hS : SolvesSubsetSum S) :
    ∃ B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ), ThetaUniqueSVP (5 / 2) B := by
  have hdcp : HasDCPSolver 1 := h13 S hS
  obtain ⟨B, hB⟩ := dcp_implies_uniqueSVP 1 (by norm_num) h312 hdcp
  have h : svpExponent 1 = 5 / 2 := by
    unfold svpExponent
    norm_num
  exact ⟨B, by simpa [h] using hB⟩

end Qatlib.Papers.QLattice03.MainResults
