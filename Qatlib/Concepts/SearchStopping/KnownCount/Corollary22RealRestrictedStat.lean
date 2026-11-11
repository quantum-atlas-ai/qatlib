/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic

/-!
# Real two-amplitude diffusion formulas

`distinguishedAfter` and `ordinaryAfter` define the updated real amplitudes for one
distinguished coordinate. `twoAmplitudeMass` records their weighted squared mass, and
`Corollary2_2RealRestricted` states its preservation in positive dimension.

For the mathematical background, see [Grover1997].

## Main statements

* `Corollary2_2RealRestricted`: The proposition that the real two-amplitude diffusion update
  preserves `twoAmplitudeMass` whenever N > 0.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The updated distinguished real amplitude (2/N − 1)k + 2(N − 1)l/N. -/
noncomputable def distinguishedAfter (N : ℕ) (k l : ℝ) : ℝ :=
  (2 / (N : ℝ) - 1) * k + (2 * ((N : ℝ) - 1) / N) * l

/-- The updated ordinary real amplitude 2k/N + (1 − 2/N)l. -/
noncomputable def ordinaryAfter (N : ℕ) (k l : ℝ) : ℝ :=
  (2 / (N : ℝ)) * k + (1 - 2 / (N : ℝ)) * l

/-- The weighted squared real amplitude mass k² + (N − 1)l². -/
noncomputable def twoAmplitudeMass (N : ℕ) (k l : ℝ) : ℝ :=
  k ^ 2 + ((N : ℝ) - 1) * l ^ 2

/-- The proposition that the real two-amplitude diffusion update preserves `twoAmplitudeMass`
whenever N > 0. -/
def Corollary2_2RealRestricted : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (k l : ℝ),
    twoAmplitudeMass N (distinguishedAfter N k l) (ordinaryAfter N k l) =
      twoAmplitudeMass N k l

end Qatlib.Concepts.SearchStopping.KnownCount
