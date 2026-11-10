/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.TensorHyper20.MainResults.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.QubitizationCost

open Qatlib.Papers.TensorHyper20.MainResults

theorem eq44_decomposition (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) :
    selectCost M N i kr1 kr2 + prepareCost M br ℵ d ks1 ks2 + reflectionCost M ℵ
      = stepCost M N br ℵ i d ks1 ks2 kr1 kr2 := by
  unfold selectCost prepareCost reflectionCost stepCost
  ring

theorem eq45_qpeIterations_def (lam eps : ℝ) :
    qpeIterations lam eps = ⌈Real.pi * lam / (2 * eps)⌉₊ := rfl

theorem eq45_iterations_lt (lam eps : ℝ) (h : 0 ≤ Real.pi * lam / (2 * eps)) :
    (qpeIterations lam eps : ℝ) < Real.pi * lam / (2 * eps) + 1 :=
  Nat.ceil_lt_add_one h

theorem eq45_iterations_ge (lam eps : ℝ) :
    Real.pi * lam / (2 * eps) ≤ (qpeIterations lam eps : ℝ) :=
  Nat.le_ceil _

theorem eq45_total_cost (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) (lam eps : ℝ) :
    totalToffoli M N br ℵ i d ks1 ks2 kr1 kr2 lam eps
      = (qpeIterations lam eps : ℤ) * stepCost M N br ℵ i d ks1 ks2 kr1 kr2 := rfl

end Qatlib.Papers.TensorHyper20.MainResults.QubitizationCost
