/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — Theorem V (independent query model)

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).
Theorem V, Section I p. 6 (line 269); proof Section V p. 13.

Statement: in the independent query model (each use of `f`/`g` is a fresh
independent random pair), the randomized classical query complexity of
`U`-circuit checking is `2^{Θ(C(U))}`.

The upper bound is the Section V estimator with `N = ⌈4·2^{C(U)} log(1/ε)⌉`
independent realisations; the lower bound is the postselected bound of
Theorem I.  This file proves the quantitative comparison of the two sides
(for `log(1/ε) ≥ 1`).
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace TheoremV

open Model

/-- Theorem V (Section I p. 6, proof Section V p. 13): the lower bound
`2^{C(U)/7}` is dominated by the explicit upper-bound query budget
`2^{C(U)+2} log(1/ε)` whenever `log(1/ε) ≥ 1`. -/
theorem theorem_V_independent_query_model
    (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ)
    (hC0 : 0 ≤ sourceC U) (hlog : 1 ≤ Real.log (1 / ε)) :
    sourceIndependentQueryLowerBound U ≤ sourceIndependentQueryUpperBound U ε := by
  unfold sourceIndependentQueryLowerBound sourceIndependentQueryUpperBound
  set C := sourceC U with hCdef
  have hbase : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hle : (2 : ℝ) ^ (C / 7) ≤ (2 : ℝ) ^ (C + 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (C + 2) := Real.rpow_nonneg hbase _
  exact le_trans hle (le_mul_of_one_le_right hnonneg hlog)

end TheoremV
end Qatlib.Papers.ExpSpeedup10.MainResults
