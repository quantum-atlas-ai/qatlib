/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SVTransformSubgoalStat
import Qatlib.Concepts.SignalPrimitive.LCUConsumers.SingularValueTransformation
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Concepts.SignalPrimitive.LCUConsumers

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib
open Matrix

theorem svTransformSubgoal : SVTransformSubgoal := by
  intro J I _ _ _ _ U j₀ A hU c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃
  refine ⟨qsvtWord_unitary U j₀ c₀ c₁ c₂ c₃ hU.1 hc₀ hc₁ hc₂ hc₃,
    qsvt_projected_corner hU c₀ c₁ c₂ c₃, ?_⟩
  intro v w σ _ _ hv hw
  exact qsvt_singularValue_action c₀ c₁ c₂ c₃ hv hw

end Qatlib.Concepts.QsvtCore.PhaseExistence
