/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem theorem1_1_obstruction : ¬ Theorem1_1Contract := by
  intro h
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ht := h.2 2 (1 / 2) (by decide) (by norm_num) (by norm_num)
  norm_num [hl] at ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
