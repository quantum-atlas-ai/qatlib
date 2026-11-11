/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — quantum linear-system estimation (Lemmas 3, 4, 5)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

The three lemmas of §3.1 (p.10) state the query complexity of variants of the HHL/CKS
solver used later in §3.2:

* **Lemma 3** — `ε`-multiplicative estimate of `‖x̃‖`, cost `O(dκ²/ε·poly log(dκ/ε))`;
* **Lemma 4** — `ε`-additive estimate of `|x_i|`, cost `O(dq²κ³/ε²·poly log(dqκ/ε))`;
* **Lemma 5** — `ε`-additive estimate of `|x_i − x_j|`, same cost.

The algorithm existence and the query-count / success-probability analysis are **not built**
here; recorded are the paper's leading cost functions (from `Model.CostModel`) and their
elementary resource properties.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.QLS

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- **Lemma 3 (arXiv:1311.1851v10, §3.1, p.10).**  Query-cost ledger for the `ε`-multiplicative
estimate of `‖x̃‖`: its leading term is `costLemma3 d κ ε = d·κ²/ε`, which is positive for
positive parameters and increasing in the sparsity `d`.

Built: the cost function and its positivity/monotonicity.  Not built: the gate-efficient
quantum algorithm that achieves it with probability ≥ 2/3 (HHL/CKS + amplitude estimation). -/
theorem lemma3_query_cost (d kappa eps : ℝ) (hd : 0 < d) (hk : 0 < kappa) (he : 0 < eps) :
    0 < costLemma3 d kappa eps := by
  unfold costLemma3
  positivity

/-- **Lemma 3**, monotonicity of the leading cost in the sparsity `d` (p.10). -/
theorem lemma3_query_cost_mono (d d' kappa eps : ℝ) (hd : d ≤ d') (hk : 0 ≤ kappa)
    (he : 0 < eps) :
    costLemma3 d kappa eps ≤ costLemma3 d' kappa eps := by
  unfold costLemma3
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hd (sq_nonneg kappa)) (le_of_lt he)

/-- **Lemma 4 (arXiv:1311.1851v10, §3.1, p.10).**  Query-cost ledger for the `ε`-additive
estimate of `|x_i|`: leading term `costLemma45 d q κ ε = d·q²·κ³/ε²`, positive for positive
parameters.

Built: the cost function and positivity.  Not built: the quantum algorithm and its
probability-≥-2/3 guarantee. -/
theorem lemma4_query_cost (d q kappa eps : ℝ) (hd : 0 < d) (hq : 0 < q) (hk : 0 < kappa)
    (he : 0 < eps) :
    0 < costLemma45 d q kappa eps := by
  unfold costLemma45
  positivity

/-- **Lemma 5 (arXiv:1311.1851v10, §3.1, p.10).**  Query-cost ledger for the `ε`-additive
estimate of `|x_i − x_j|`; it is the same cost function `costLemma45` as Lemma 4 (the
difference-of-entries task has identical complexity, p.10).

Built: the cost function and positivity.  Not built: the quantum algorithm. -/
theorem lemma5_query_cost (d q kappa eps : ℝ) (hd : 0 < d) (hq : 0 < q) (hk : 0 < kappa)
    (he : 0 < eps) :
    0 < costLemma45 d q kappa eps :=
  lemma4_query_cost d q kappa eps hd hq hk he

end Qatlib.Papers.SparseNetwork13.MainResults.QLS
