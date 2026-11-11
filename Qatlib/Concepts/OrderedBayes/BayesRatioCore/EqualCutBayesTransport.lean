/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum

/-!
# Obstruction to unconditional Bayesian normalization

This module proves `equalCutBayesTransport_obstruction` for a transport contract motivated by
ordered Bayesian search [BenOrHassidim2007]. At a one-cell prior with noise parameter zero, the
true-answer normalizer vanishes, contradicting the contract's requirement that both normalizers
be positive throughout the closed parameter interval.

## Main statements

* `equalCutBayesTransport_obstruction`: `EqualCutBayesTransportContract` is false.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition `EqualCutBayesTransportContract` is false because a one-cell prior at p = 0
has a zero true-answer normalizer. -/
theorem equalCutBayesTransport_obstruction : ¬ EqualCutBayesTransportContract := by
  intro h
  have ht := h.1 1 (fun _ => 1) 0 0 (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp)
  norm_num [bayesTrueNorm, bayesTrueLikelihood] at ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
