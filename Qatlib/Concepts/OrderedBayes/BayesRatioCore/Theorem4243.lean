/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.Linarith

/-!
# An obstruction to a logarithmic coefficient comparison

This module disproves `Theorem4_2_4_3Contract`, a local coefficient-comparison contract in the
ordered-search development associated with [BenOrHassidim2007]. The contract bounds an
entropy-adjusted expression scaled by `Real.log (Real.exp 1) / Real.pi` by the same expression
scaled by `Real.log 2 / Real.pi`.

`theorem4_2_4_3_obstruction` takes alphabet size two and zero error. The contract then implies
`1 ≤ Real.log 2`, which contradicts the strict logarithm bound.

## Main statements

* `theorem4_2_4_3_obstruction`: negation of the local coefficient-comparison contract.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The local Theorems 4.2 and 4.3 coefficient-comparison contract is false. Alphabet size two
and zero error would force `1 ≤ Real.log 2`, contradicting the strict logarithm bound. -/
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
