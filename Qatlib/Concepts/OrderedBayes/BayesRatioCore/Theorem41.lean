/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem oracleDecay_endpoint_half :
    1 - 2 * Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = queryInfo (1 / 2) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [queryInfo, binEntropy, Real.log_div, hl, hs]

theorem oracleDecay_endpoint_one :
    1 - 2 * Real.sqrt ((1 : ℝ) * (1 - 1)) = queryInfo 1 := by
  norm_num [queryInfo, binEntropy]

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
