/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonJointOriginalContract

/-!
# Dyson truncation with split error budgets

`lemma5DysonTruncation` combines the joint Dyson grid error estimate with separate
discretization and truncation budgets. Each contribution is bounded by ε/2 for a continuously
differentiable, bounded Hermitian Hamiltonian on a short interval. These estimates support the
interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `lemma5DysonTruncation`: the total error bound obtained from two half-error bounds.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Proves `Lemma5DysonTruncation`, combining discretization error at most ε/2 and factorial
tail error at most ε/2 into total error at most ε; see [Low and Wiebe, Lemma
5][LowWiebe2018]. -/
theorem lemma5DysonTruncation : Lemma5DysonTruncation := by
  intro I _ _ H Hd t Λ ε K M hH hHd hderiv ht hM hε hbound hlog hdisc htail
  have hΛ : 0 ≤ Λ := (norm_nonneg (H 0)).trans (hbound 0 ⟨le_rfl, ht.le⟩).2
  have he := dyson_truncated_grid_joint_error I H Hd t Λ M K hH ht.le hΛ hM hbound hHd hderiv hlog
  have hsame : truncatedDysonGridSum H t M K = dysonGridTruncatedSum H t M K := rfl
  rw [hsame]
  linarith

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
