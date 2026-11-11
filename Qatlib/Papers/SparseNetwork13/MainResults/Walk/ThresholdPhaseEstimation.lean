/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.CostModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — threshold phase estimation (Lemma 14)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

**Lemma 14** (§4.3, p.28): for a unitary `U` with eigenvectors `|ψ_j⟩` of eigenphase `θ_j`,
and given `θ, Δ, δ ∈ (0,1)`, there is a unitary `P` using `O((1/Δ)·log(1/δ))` calls to `U`
and `poly(log(1/(Δδ)))` extra gates that distinguishes `θ_j = θ` from `|θ_j − θ| ≥ Δ` with
failure probability ≤ δ.

The unitary procedure `P` (boosted phase estimation, median-of-`O(log(1/δ))` repetitions) is
**not built**; recorded are its leading query cost `costLemma14 Δ δ = log(1/δ)/Δ`, its
scaling identity `Δ·costLemma14 = log(1/δ)`, and positivity.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Walk

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- **Lemma 14 (arXiv:1311.1851v10, §4.3, p.28).**  Leading query cost `log(1/δ)/Δ` of the
threshold phase-estimation procedure.  Built: the cost function and the scaling identity.
Not built: the unitary procedure and its probability-≥-`1−δ` guarantee. -/
theorem lemma14_cost_scaling (Delta delta : ℝ) (hDelta : Delta ≠ 0) :
    Delta * costLemma14 Delta delta = Real.log (1 / delta) := by
  unfold costLemma14
  field_simp

/-- **Lemma 14**, positivity of the query cost for `Δ > 0`, `0 < δ < 1` (p.28). -/
theorem lemma14_cost_pos (Delta delta : ℝ) (hDelta : 0 < Delta) (hdelta : 0 < delta)
    (hlt : delta < 1) :
    0 < costLemma14 Delta delta := by
  unfold costLemma14
  have hx : 1 < 1 / delta := by
    rw [one_div, one_lt_inv_iff₀]
    exact ⟨hdelta, hlt⟩
  exact div_pos (Real.log_pos hx) hDelta

end Qatlib.Papers.SparseNetwork13.MainResults.Walk
