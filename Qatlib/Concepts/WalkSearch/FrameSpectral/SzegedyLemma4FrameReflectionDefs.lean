/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Finite frame projection matrices

The matrix `paperFrameProjection` is the finite sum of the outer products of a family of complex
states. It provides the matrix used in the projection and reflection formulation of Szegedy's
frame lemma; the definition itself places no orthonormality condition on the family. The quantum
walk spectral framework is developed in [Szegedy2004].

## Main statements

* `paperFrameProjection`: The sum of the frame vector outer products.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The matrix whose `(x, y)` entry is the sum of `v i x * conj (v i y)` over the finite frame
index set. -/
noncomputable def paperFrameProjection {H ι : Type} [Fintype H] [DecidableEq H]
    [Fintype ι] [DecidableEq ι] (v : ι → QState H) : Matrix H H ℂ :=
  Matrix.of fun x y => ∑ i, v i x * (starRingEnd ℂ) (v i y)
end Qatlib.Concepts.WalkSearch.FrameSpectral
