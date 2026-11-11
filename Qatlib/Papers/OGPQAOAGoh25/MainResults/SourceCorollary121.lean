/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1.2.1 — no quantum advantage from QAOA under limit swapping

Fixed source: arXiv:2404.06087v6, Corollary 1.2.1 (p. 2, lines 165–167),
re-deriving Theorem 1.2 of [4] with the OGP/limit-swapping argument.

> Optimising the QAOA using the algorithm in [4, 5] only allows it to perform
> equal in performance to local classical algorithms, thus providing no quantum
> advantage.

The content is the equality of the two limiting performances: Theorems 4.1–4.2
show that the optimised QAOA cannot beat the `ηOGP` threshold that also bounds
the local classical algorithms. Formally, if the optimal QAOA performance is
both bounded by and bounds the best local classical performance, the two
coincide and no strict quantum advantage exists.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

/-- **Corollary 1.2.1** (arXiv:2404.06087v6, p. 2, lines 165–167).

If the optimised QAOA performance is bounded by the best local classical
performance and conversely (both saturate the same `ηOGP` threshold coming from
Theorems 4.1 and 4.2), then the two are equal and there is no strict quantum
advantage. -/
theorem corollary121
    (qaoaPerf localClassicalPerf : ℝ)
    (hQAOA : qaoaPerf ≤ localClassicalPerf)
    (hLocal : localClassicalPerf ≤ qaoaPerf) :
    qaoaPerf = localClassicalPerf ∧ ¬ (qaoaPerf > localClassicalPerf) := by
  refine ⟨le_antisymm hQAOA hLocal, ?_⟩
  intro h
  exact absurd hQAOA (not_le.mpr h)

end Qatlib.Papers.OGPQAOAGoh25.MainResults
