/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum

/-!
# Source sign flip for spectral symmetry

The map `paperSourceFlip` fixes the first component of a direct sum state and negates the
second. It is the source transformation used to exchange opposite eigenvalues of the bipartite
discriminant. The quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `paperSourceFlip`: The transformation `(a, b) ↦ (a, −b)`.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The direct sum state transformation that preserves the left component and negates the right
component. -/
def paperSourceFlip {I J : Type} (v : QState (I ⊕ J)) : QState (I ⊕ J) :=
  Sum.elim (fun i => v (Sum.inl i)) (fun j => -(v (Sum.inr j)))
end Qatlib.Concepts.WalkSearch.FrameSpectral
