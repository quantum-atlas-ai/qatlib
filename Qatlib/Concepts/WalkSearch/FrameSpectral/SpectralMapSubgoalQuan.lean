/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralMapSubgoalStat

/-!
# Szegedy spectral rotation planes

The theorem `spectralMapSubgoal` proves the discriminant-to-walk rotation correspondence. A
normalized real discriminant eigenvector with eigenvalue `cos θ` and nonzero `sin θ` yields two
orthonormal walk states with the stated angle-doubling action. The quantum walk spectral
framework is developed in [Szegedy2004].

## Main statements

* `spectralMapSubgoal`: The two-state walk rotation associated with a discriminant eigenvector.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib

/-- A normalized real discriminant eigenvector of eigenvalue `cos θ`, with `sin θ ≠ 0`, yields
orthonormal states on which the Szegedy walk has the stated rotation action at angle `2 * θ`
[Szegedy2004]. -/
theorem spectralMapSubgoal : SpectralMapSubgoal :=
  fun I _ _ P hP v hv θ hs hvD => Qatlib.Concepts.WalkSearch.Spectral.szegedy_spectral_map P hP v hv θ hs hvD

end Qatlib.Concepts.WalkSearch.FrameSpectral
