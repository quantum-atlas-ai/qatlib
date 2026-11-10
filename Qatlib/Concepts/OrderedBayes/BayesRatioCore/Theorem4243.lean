/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.Linarith
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem theorem4_2_4_3_obstruction : ¬ Theorem4_2_4_3Contract := by
  intro h
  have ht := h 2 0 (by decide) (by norm_num) (by norm_num)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  norm_num [binEntropy, hl.ne'] at ht
  have ht' : 1 / Real.pi ≤ Real.log 2 / Real.pi := by
    simpa only [one_div] using ht
  have hb := (div_le_div_iff_of_pos_right hpi).mp ht'
  have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at hlog
  linarith

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
