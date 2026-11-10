/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath.ProjectionGap
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath

open Qatlib.Papers.AdiabStateGen03.MainResults

theorem gap_half_eq {r : ℝ} (hr0 : 0 ≤ r) :
    Real.sqrt (1 - 4 * (1 - 1 / 2) * (1 / 2) * (1 - r ^ 2)) = r := by
  have h : 1 - 4 * (1 - 1 / 2) * (1 / 2) * (1 - r ^ 2) = r ^ 2 := by ring
  rw [h, Real.sqrt_sq hr0]

theorem gap_completed_square (η r : ℝ) :
    1 - 4 * (1 - η) * η * (1 - r ^ 2) = r ^ 2 + (1 - 2 * η) ^ 2 * (1 - r ^ 2) := by
  ring

theorem gap_ge_half {η r : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ≤ Real.sqrt (1 - 4 * (1 - η) * η * (1 - r ^ 2)) :=
  overlap_le_sqrt_gap hη0 hη1 hr0 hr1

theorem slowlyVarying_overlap_nonneg {n T : ℕ} (π : Fin (T + 1) → Dim n → ℝ)
    (t : Fin T) :
    0 ≤ ∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i) :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

end Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath
