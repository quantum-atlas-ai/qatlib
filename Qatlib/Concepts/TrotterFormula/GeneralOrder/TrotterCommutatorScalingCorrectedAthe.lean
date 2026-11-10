/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrectedStat
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical Matrix.Norms.L2Operator

theorem trotterCommutatorScalingCorrected : TrotterCommutatorScalingCorrected := by
  intro I _ _ xs H p r hp hr hxs hH hc t
  (try dsimp only)
  refine ⟨?_,?_,?_⟩
  · rw [pf_segment_word_prod]
    exact (Matrix.unitaryGroup I ℂ).pow_mem (pf_word_unitary xs (t/r) hxs) r
  · simp [List.length_flatten]
  · rw [pf_segment_word_prod]
    exact pf_matched_word_segmented_skew xs H p r t hp hr hc hxs hH
end Qatlib.Concepts.TrotterFormula.GeneralOrder
