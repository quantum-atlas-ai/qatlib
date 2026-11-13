/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterGeneralOperatorScalingStat
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments

/-!
# Corrected general-operator commutator scaling

This module proves `TrotterGeneralOperatorScalingCorrected`, the corrected general-matrix
version of the segmented commutator-scaling bound associated with Theorem 11 of
[ChildsEtAl2021Trotter]. The estimate includes the numerator factor `p!` and exponential
inflation `exp (4 * |t| * (suzukiMass xs + ‖H‖))` for words matching coefficients through
positive order `p`.

## Main statements

* `trotterGeneralOperatorScalingCorrected`: proves the corrected bound for general matrix words.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical Matrix.Norms.L2Operator

/-- The corrected commutator-scaling bound holds for general segmented matched-order matrix
words with the stated exponential norm inflation. This is the corrected formulation
associated with [Childs et al., Theorem 11][ChildsEtAl2021Trotter]. -/
theorem trotterGeneralOperatorScalingCorrected : TrotterGeneralOperatorScalingCorrected := by
  intro I _ _ xs H p r hp hr hc t
  (try dsimp only)
  rw [pf_segment_word_prod]
  exact pf_matched_word_segmented_general xs H p r t hp hr hc
end Qatlib.Concepts.TrotterFormula.GeneralOrder
