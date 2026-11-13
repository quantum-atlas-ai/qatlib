/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# One-sided derivatives from derivative limits

This module recovers a one-sided derivative from a nonzero one-sided limit of the ordinary
derivative and continuity at the endpoint. The right and left versions supply endpoint tangent
data for the contour estimates supporting [WangEtAl2026].

## Main statements

* `hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero`: the right-hand derivative criterion.
* `hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero`: the left-hand derivative criterion.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero right-hand limit of the ordinary derivative is the right derivative at an endpoint
where the function is right-continuous. -/
theorem hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Ici t₀) t₀) (hL_ne : L ≠ 0)
    (hL : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ :=
  hasDerivWithinAt_Ioi_iff_Ici.mpr <|
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := {t | deriv γ t ≠ 0} ∩ Ioi t₀)
      (fun _ ht => (differentiableAt_of_deriv_ne_zero ht.1).differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Ioi_subset_Ici_self))
      (inter_mem (hL.eventually_ne hL_ne) self_mem_nhdsWithin) hL

/-- A nonzero left-hand limit of the ordinary derivative is the left derivative at an endpoint
where the function is left-continuous. -/
theorem hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Iic t₀) t₀) (hL_ne : L ≠ 0)
    (hL : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ :=
  hasDerivWithinAt_Iio_iff_Iic.mpr <|
    hasDerivWithinAt_Iic_of_tendsto_deriv (s := {t | deriv γ t ≠ 0} ∩ Iio t₀)
      (fun _ ht => (differentiableAt_of_deriv_ne_zero ht.1).differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Iio_subset_Iic_self))
      (inter_mem (hL.eventually_ne hL_ne) self_mem_nhdsWithin) hL

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
