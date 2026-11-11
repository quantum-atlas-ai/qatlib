/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — implementing the quantum walk (Lemmas 12, 13)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

* **Lemma 12** (§4.2, p.25) — `U(A,B)` is implementable by a gate-efficient procedure
  making `O(d)` uses of `P_v, P_e, P_i` (perfect implementation).
* **Lemma 13** (§4.2, p.26) — `U(A,B)` is implementable to precision `δ > 0` by a
  gate-efficient procedure making `O(√(c/λ)·poly log(d/δ))` uses of `P_v, P_e, P_i`.

The circuit constructions (`Ref(A) = Q₁R₁Q₁†`, `Ref(B) = Q₂R₂Q₂†`) are **not built**;
the leading cost functions and their positivity are recorded.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Walk

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- **Lemma 12 (arXiv:1311.1851v10, §4.2, p.25).**  The walk `U(A,B)` uses `O(d)` oracle
calls: `costLemma12 d = d`.  Built: the cost function and positivity.  Not built: the
gate-efficient circuit implementing `Ref(A)`, `Ref(B)`. -/
theorem lemma12_walk_implementation_cost (d : ℝ) (hd : 0 < d) : 0 < costLemma12 d := by
  unfold costLemma12
  exact hd

/-- **Lemma 13 (arXiv:1311.1851v10, §4.2, p.26).**  The `δ`-precision implementation of
`U(A,B)` costs `O(√(c/λ)·poly log(d/δ))`; with the polylog recorded as the factor `pl`,
`costLemma13 c λ pl = √(c/λ)·pl`, positive for positive inputs.  Built: the cost function and
positivity.  Not built: the approximate block-encoding circuit. -/
theorem lemma13_walk_implementation_cost (c lam pl : ℝ) (hc : 0 < c) (hlam : 0 < lam)
    (hpl : 0 < pl) :
    0 < costLemma13 c lam pl := by
  unfold costLemma13
  have h : 0 < c / lam := div_pos hc hlam
  have hsqrt : 0 < Real.sqrt (c / lam) := Real.sqrt_pos.mpr h
  exact mul_pos hsqrt hpl

end Qatlib.Papers.SparseNetwork13.MainResults.Walk
