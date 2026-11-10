/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem equalCutBayesTransport_obstruction : ¬ EqualCutBayesTransportContract := by
  intro h
  have ht := h.1 1 (fun _ => 1) 0 0 (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp)
  norm_num [bayesTrueNorm, bayesTrueLikelihood] at ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
