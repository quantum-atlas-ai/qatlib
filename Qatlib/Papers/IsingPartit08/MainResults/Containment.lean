/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

theorem normalizerOf_pos (lam : ℝ) (edges : ℕ) : 0 < normalizerOf lam edges := by
  unfold normalizerOf
  apply Real.sqrt_pos.mpr
  have hbase : 0 < lam ^ 2 + 1 := by nlinarith [sq_nonneg lam]
  exact pow_pos hbase edges

theorem normalizerOf_sq (lam : ℝ) (edges : ℕ) :
    normalizerOf lam edges ^ 2 = (lam ^ 2 + 1) ^ edges := by
  unfold normalizerOf
  rw [Real.sq_sqrt (by positivity)]

theorem containment_additive {q normalizer s p m : ℝ}
    (hN : 0 < normalizer) (hmaster : MasterCorrespondence q normalizer s)
    (hm : HadamardTestEstimate q p m) :
    |normalizer * m - s| ≤ normalizer * p := by
  unfold MasterCorrespondence at hmaster
  unfold HadamardTestEstimate at hm
  have hrw : normalizer * m - s = normalizer * (m - q) := by
    rw [← hmaster]; ring
  rw [hrw, abs_mul, abs_of_pos hN]
  exact mul_le_mul_of_nonneg_left hm (le_of_lt hN)

theorem containment_additive_normalizer {q s p m : ℝ} (lam : ℝ) (edges : ℕ)
    (hmaster : MasterCorrespondence q (normalizerOf lam edges) s)
    (hm : HadamardTestEstimate q p m) :
    |normalizerOf lam edges * m - s| ≤ normalizerOf lam edges * p :=
  containment_additive (normalizerOf_pos lam edges) hmaster hm

end Qatlib.Papers.IsingPartit08.MainResults
