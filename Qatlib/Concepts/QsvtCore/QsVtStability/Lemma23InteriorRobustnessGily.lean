/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23InteriorRobustnessStat
open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Matrix.Norms.L2Operator

theorem lemma23InteriorRobustness : Lemma23InteriorRobustness := by
  intro I O _ _ _ _ A B base zs hb hz hA hB hbudget
  by_cases hm : ‖(2 : ℂ)⁻¹ • (A+B)‖ < 1
  · exact interior_complex_singular_response_stability I O A B base zs hb hz hA hB hm hbudget
  · have hm' : 1 ≤ ‖(2 : ℂ)⁻¹ • (A+B)‖ := le_of_not_gt hm
    have hδ : ‖A-B‖ = 0 := by nlinarith [norm_nonneg (A-B)]
    have hAB : A=B := sub_eq_zero.mp (norm_eq_zero.mp hδ)
    subst B
    constructor <;> intro _ <;>
      simpa only [sub_self, norm_zero] using interiorRate_nonneg A A zs.length

end Qatlib.Concepts.QsvtCore.QsVtStability
