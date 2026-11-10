/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Qatlib.Papers.GraphConnect03.MainResults.UpperBounds.DFSSpanningTree
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.UpperBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs

theorem rpow_three_halves (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h3 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [h3, Real.rpow_add hnpos, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem dfsMatrixCost_le (n : ℕ) (visited : Finset (Vertex n)) (hn : 2 ≤ n) :
    dfsMatrixCost visited ≤ 2 * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log (n : ℝ)) := by
  unfold dfsMatrixCost matrixGroverCharge
  have hcount : (dfsSearchCount visited : ℝ) ≤ 2 * (n : ℝ) := by
    have := dfsSearchCount_le visited
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hcharge : 0 ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hsqrt hlog
  calc (dfsSearchCount visited : ℝ) * (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
      ≤ (2 * (n : ℝ)) * (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount hcharge
    _ = 2 * ((n : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by ring
    _ = 2 * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log (n : ℝ)) := by
        rw [rpow_three_halves n (by omega)]

theorem dfsListCost_le (n k : ℕ) (visited : Finset (Vertex n)) (hn : 2 ≤ n) :
    dfsListCost n k visited ≤ 2 * ((n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) := by
  unfold dfsListCost listGroverCharge
  have hcount : (dfsSearchCount visited : ℝ) ≤ 2 * (n : ℝ) := by
    have := dfsSearchCount_le visited
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsqrt : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hcharge : 0 ≤ Real.sqrt (k : ℝ) * Real.log (n : ℝ) := mul_nonneg hsqrt hlog
  calc (dfsSearchCount visited : ℝ) * (Real.sqrt (k : ℝ) * Real.log (n : ℝ))
      ≤ (2 * (n : ℝ)) * (Real.sqrt (k : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount hcharge
    _ = 2 * ((n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) := by ring

theorem dfsMatrixCost_bigO :
    IsBigOFrom (fun n : ℕ => dfsMatrixCost (Finset.univ : Finset (Vertex n)))
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.log (n : ℝ)) 2 :=
  ⟨2, by norm_num, fun n hn => dfsMatrixCost_le n Finset.univ hn⟩

theorem dfsListCost_bigO (k : ℕ) :
    IsBigOFrom (fun n : ℕ => dfsListCost n k (Finset.univ : Finset (Vertex n)))
      (fun n : ℕ => (n : ℝ) * Real.sqrt (k : ℝ) * Real.log (n : ℝ)) 2 :=
  ⟨2, by norm_num, fun n hn => dfsListCost_le n k Finset.univ hn⟩

end Qatlib.Papers.GraphConnect03.MainResults.UpperBounds
