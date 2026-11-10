/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.AffineSpectrum
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformSecular
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
variable {I : Type} [Fintype I] [DecidableEq I]

theorem actual_spectralGap_rankOne (E : I → ℝ) (hL : 2 ≤ Fintype.card I)
    (s : ℝ) (hs : 0 < s) :
    spectralGap E hL s = s *
      ((rankOneOperator_hermitian E ((1-s)/s)).eigenvalues₀
          ⟨Fintype.card I - 2, by omega⟩ -
        (rankOneOperator_hermitian E ((1-s)/s)).eigenvalues₀
          ⟨Fintype.card I - 1, by omega⟩) := by
  have hg := Qatlib.Foundations.MatrixAlgebra.RankOneSecular.native_gap_positive_affine
    (rankOneOperator_hermitian E ((1-s)/s)) hL (1-s) s hs
  unfold spectralGap
  simp only [hamiltonian_rankOne E s (ne_of_gt hs)]
  exact hg

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
