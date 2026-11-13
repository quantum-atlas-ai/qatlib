/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum

/-!
# An obstruction to the local Theorem 1.1 contract

This module disproves `Theorem1_1Contract`, the local conjunction associated with Theorem 1.1 in
the ordered-search development [BenOrHassidim2007]. Its second component forbids the error
parameter from being strictly below the cube of the base-two logarithm of the list size.

`theorem1_1_obstruction` uses list size two and error parameter `1 / 2`: the logarithmic cube is
one, so these parameters contradict that component. The declaration concerns this precise local
contract.

## Main statements

* `theorem1_1_obstruction`: negation of `Theorem1_1Contract`.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The local Theorem 1.1 contract is false because its second conjunct fails at list size two
and error parameter `1 / 2`. -/
theorem theorem1_1_obstruction : ¬ Theorem1_1Contract := by
  intro h
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ht := h.2 2 (1 / 2) (by decide) (by norm_num) (by norm_num)
  norm_num [hl] at ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
