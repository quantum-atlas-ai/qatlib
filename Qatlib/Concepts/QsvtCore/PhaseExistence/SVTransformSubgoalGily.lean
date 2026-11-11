/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SVTransformSubgoalStat
import Qatlib.Concepts.SignalPrimitive.LCUConsumers.SingularValueTransformation

/-!
# A cubic singular value transformation identity

`svTransformSubgoal` proves the specification `SVTransformSubgoal` for a four-phase QSVT word.
It combines unitarity, an explicit projected matrix polynomial, and the action of that
polynomial on normalized left and right singular vectors. See [GilyenSuLowWiebe2019].

## Main statements

* `svTransformSubgoal`: verify the word, compression, and singular-vector identities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Concepts.SignalPrimitive.LCUConsumers

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib
open Matrix

/-- A projected unitary encoding and four unit-modulus phase scalars yield a unitary QSVT word
with the specified cubic compression and corresponding scalar action on normalized
singular-vector pairs. See [GilyenSuLowWiebe2019]. -/
theorem svTransformSubgoal : SVTransformSubgoal := by
  intro J I _ _ _ _ U j₀ A hU c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃
  refine ⟨qsvtWord_unitary U j₀ c₀ c₁ c₂ c₃ hU.1 hc₀ hc₁ hc₂ hc₃,
    qsvt_projected_corner hU c₀ c₁ c₂ c₃, ?_⟩
  intro v w σ _ _ hv hw
  exact qsvt_singularValue_action c₀ c₁ c₂ c₃ hv hw

end Qatlib.Concepts.QsvtCore.PhaseExistence
