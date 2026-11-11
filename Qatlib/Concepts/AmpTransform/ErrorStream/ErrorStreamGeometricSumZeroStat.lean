/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

/-!
# Statement of complete Fourier phase cancellation

`ErrorStreamGeometricSumZero` states that the Fourier phase sum over the entire register
vanishes at every frequency nonzero modulo the positive register size. This is the finite
geometric-sum identity used in the error-stream probability calculations.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `ErrorStreamGeometricSumZero`: the cancellation statement corresponding to [Cornwell, Lemma
  15][Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- The statement that the sum of `aqPhase N z y` over all `z < N` is zero whenever `N` is
positive and `y` is nonzero modulo `N`. -/
def ErrorStreamGeometricSumZero : Prop :=
  ∀ (N y : ℕ), 0 < N → y % N ≠ 0 →
    ∑ z ∈ Finset.range N, aqPhase N z y = 0
end Qatlib.Concepts.AmpTransform.ErrorStream
