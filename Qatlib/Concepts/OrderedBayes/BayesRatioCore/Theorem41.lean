/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.NormNum

/-!
# Endpoint identities for oracle decay and information

This module compares the expression `1 - 2 * Real.sqrt (p * (1 - p))` with the binary query
information `queryInfo p` at two endpoint reliabilities. These quantities arise in the noisy
ordered-search setting of [BenOrHassidim2007].

`oracleDecay_endpoint_half` identifies their common zero value at reliability `1 / 2`, and
`oracleDecay_endpoint_one` identifies their common value one at reliability one. The
declarations establish these endpoint equalities.

## Main statements

* `oracleDecay_endpoint_half`: equality of oracle decay and query information at `1 / 2`.
* `oracleDecay_endpoint_one`: equality of oracle decay and query information at one.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- At reliability `1 / 2`, the oracle-decay expression equals the query information, both of
which are zero. -/
theorem oracleDecay_endpoint_half :
    1 - 2 * Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = queryInfo (1 / 2) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [queryInfo, binEntropy, Real.log_div, hl, hs]

/-- At reliability one, the oracle-decay expression equals the query information, both of which
are one. -/
theorem oracleDecay_endpoint_one :
    1 - 2 * Real.sqrt ((1 : ℝ) * (1 - 1)) = queryInfo 1 := by
  norm_num [queryInfo, binEntropy]

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
