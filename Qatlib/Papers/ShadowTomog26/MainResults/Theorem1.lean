/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Duality

/-!
# Global graph bounds for the shadow parameter

This module formulates the graph-body bounds corresponding to Theorem 1 of [XuEtAl2026]. The
lower bound follows from fractional covering, the upper bound uses an explicitly supplied
identity for `thetaMin`, and `IsHPerfect` yields equality at the fractional-chromatic endpoint.

## Main statements

* `source_theorem1_lower` bounds `delta` below by the reciprocal fractional chromatic number.
* `source_theorem1_upper` and `source_theorem1_bounds` use the supplied theta-minimum identity.
* `source_theorem1_hperfect` proves equality for an hbar-perfect graph-body system.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The beta simplex infimum `delta B` is at least the reciprocal fractional chromatic number of
`B.G`. -/
theorem source_theorem1_lower (B : GraphBodies V) :
    1 / fractionalChromatic B.G ≤ delta B :=
  le_trans (one_div_fracChromatic_le_alphaMin B) (alphaMin_le_delta B)

/-- If the theta simplex infimum equals the reciprocal stored complementary Lovasz parameter,
then `delta B` is at most that reciprocal. -/
theorem source_theorem1_upper (B : GraphBodies V)
    (h38 : thetaMin B = 1 / B.lovaszComplement) :
    delta B ≤ 1 / B.lovaszComplement := by
  rw [← h38]
  exact delta_le_thetaMin B

/-- Assuming `thetaMin B = 1 / B.lovaszComplement`, the parameter `delta B` lies in the closed
interval from the reciprocal fractional chromatic number to the reciprocal complementary
Lovasz parameter. -/
theorem source_theorem1_bounds (B : GraphBodies V)
    (h38 : thetaMin B = 1 / B.lovaszComplement) :
    delta B ∈ Set.Icc (1 / fractionalChromatic B.G) (1 / B.lovaszComplement) :=
  ⟨source_theorem1_lower B, source_theorem1_upper B h38⟩

/-- For an hbar-perfect graph-body system, `delta B` equals the reciprocal fractional chromatic
number of its graph [XuEtAl2026]. -/
theorem source_theorem1_hperfect (B : GraphBodies V) (h : IsHPerfect B) :
    delta B = 1 / fractionalChromatic B.G := by
  rw [delta_eq_alphaMin_of_hperfect B h, LP.alphaMin_eq_inverse_fractionalChromatic B]

end Qatlib.Papers.ShadowTomog26.MainResults
