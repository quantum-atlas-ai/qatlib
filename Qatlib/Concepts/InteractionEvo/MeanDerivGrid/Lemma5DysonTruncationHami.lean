/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonJointOriginalContract
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open scoped Matrix.Norms.L2Operator ComplexOrder

theorem lemma5DysonTruncation : Lemma5DysonTruncation := by
  intro I _ _ H Hd t Λ ε K M hH hHd hderiv ht hM hε hbound hlog hdisc htail
  have hΛ : 0 ≤ Λ := (norm_nonneg (H 0)).trans (hbound 0 ⟨le_rfl, ht.le⟩).2
  have he := dyson_truncated_grid_joint_error I H Hd t Λ M K hH ht.le hΛ hM hbound hHd hderiv hlog
  have hsame : truncatedDysonGridSum H t M K = dysonGridTruncatedSum H t M K := rfl
  rw [hsame]
  linarith

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
