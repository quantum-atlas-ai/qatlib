/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Duality
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem source_theorem1_lower (B : GraphBodies V) :
    1 / fractionalChromatic B.G ≤ delta B :=
  le_trans (one_div_fracChromatic_le_alphaMin B) (alphaMin_le_delta B)

theorem source_theorem1_upper (B : GraphBodies V)
    (h38 : thetaMin B = 1 / B.lovaszComplement) :
    delta B ≤ 1 / B.lovaszComplement := by
  rw [← h38]
  exact delta_le_thetaMin B

theorem source_theorem1_bounds (B : GraphBodies V)
    (h38 : thetaMin B = 1 / B.lovaszComplement) :
    delta B ∈ Set.Icc (1 / fractionalChromatic B.G) (1 / B.lovaszComplement) :=
  ⟨source_theorem1_lower B, source_theorem1_upper B h38⟩

theorem source_theorem1_hperfect (B : GraphBodies V) (h : IsHPerfect B) :
    delta B = 1 / fractionalChromatic B.G := by
  rw [delta_eq_alphaMin_of_hperfect B h, LP.alphaMin_eq_inverse_fractionalChromatic B]

end Qatlib.Papers.ShadowTomog26.MainResults
