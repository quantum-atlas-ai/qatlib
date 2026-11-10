/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoGlobalSym14.ParamFacts
import Qatlib.Papers.NoGlobalSym14.ScalarModels.Perturbation
import Mathlib.Combinatorics.SimpleGraph.Maps
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.ScalarModels

open SimpleGraph

open Qatlib.Papers.NoGlobalSym14.ParamFacts

theorem source_main_result
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) (hk : 1 ≤ k) (hμ : 1 ≤ μ) (C : ℝ) :
    (k * (k - ℓ - 1) = (n - k - 1) * μ) ∧
    (Real.sqrt (n : ℝ) < (k : ℝ) + 1) ∧
    (-(gammaC1 ((k : ℝ))) * (k : ℝ) = -1) ∧
    (∀ t : ℝ,
      ‖twoLevelAmplitude 1 (case1Eplus (n : ℝ)) (case1Eminus (n : ℝ)) t‖ ^ 2
        = Real.sin (t / Real.sqrt (n : ℝ)) ^ 2) ∧
    (‖twoLevelAmplitude 1 (case1Eplus (n : ℝ)) (case1Eminus (n : ℝ))
        (Real.pi * Real.sqrt (n : ℝ) / 2)‖ ^ 2 = 1) ∧
    (Real.pi / (case1Eplus (n : ℝ) - case1Eminus (n : ℝ))
        = Real.pi * Real.sqrt (n : ℝ) / 2) ∧
    (gammaC2 (k : ℝ) (n : ℝ) (μ : ℝ) = 1 / (k : ℝ) + 1 / (((n : ℝ) - 1) * (μ : ℝ))) ∧
    (∀ (o t : ℝ),
      ‖twoLevelAmplitude o
          (case2Eplus (gammaC2 (k : ℝ) (n : ℝ) (μ : ℝ)) C (n : ℝ) (k : ℝ) (μ : ℝ))
          (case2Eminus (gammaC2 (k : ℝ) (n : ℝ) (μ : ℝ)) C (n : ℝ) (k : ℝ) (μ : ℝ)) t‖ ^ 2
        = o ^ 2 * Real.sin
            (case2HalfGap (gammaC2 (k : ℝ) (n : ℝ) (μ : ℝ)) C (n : ℝ) (k : ℝ) (μ : ℝ) * t) ^ 2) := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkr : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact source_param_identity G h hn
  · exact source_degree_lower_bound G h hn hk hμ
  · exact case1_critical_gamma_degenerate (k : ℝ) hkr
  · intro t
    exact case1_successProbability (n : ℝ) t hnr
  · exact case1_success_one (n : ℝ) hnr
  · exact case1_optimal_time (n : ℝ) hnr
  · rfl
  · intro o t
    exact case2_successProbability _ _ _ _ _ _ _

end Qatlib.Papers.NoGlobalSym14.ScalarModels
