/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

def ErrorStreamGeometricSumZero : Prop :=
  ∀ (N y : ℕ), 0 < N → y % N ≠ 0 →
    ∑ z ∈ Finset.range N, aqPhase N z y = 0
end Qatlib.Concepts.AmpTransform.ErrorStream
