/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterGeneralOperatorScalingStat
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical Matrix.Norms.L2Operator

theorem trotterGeneralOperatorScalingCorrected : TrotterGeneralOperatorScalingCorrected := by
  intro I _ _ xs H p r hp hr hc t
  (try dsimp only)
  rw [pf_segment_word_prod]
  exact pf_matched_word_segmented_general xs H p r t hp hr hc
end Qatlib.Concepts.TrotterFormula.GeneralOrder
