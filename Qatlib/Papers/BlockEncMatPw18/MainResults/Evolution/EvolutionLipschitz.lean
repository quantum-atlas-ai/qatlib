/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QsvtCore.HamiltonianSim.HermitianEvolutionLipschitzGily

set_option backward.isDefEq.respectTransparency false

/-!
# BlockEncMatPw18.Evolution — Hermitian evolution Lipschitz bound (Lemma 50)

Fixed source: Chakraborty--Gilyén--Jeffery, arXiv:1804.01973v2 (3 Sep 2018),
Lemma 50, printed p. 55 (Appendix A), attributed to Chakraborty--Gilyén--Jeffery.

`c033` Lemma 50: for Hermitian `H, H'` and any real `t`,
`‖e^{itH} - e^{itH'}‖ ≤ |t| · ‖H - H'‖` in the L2 operator norm.

The library proves exactly this as
`Qatlib.Papers.QSingValue19.HamiltonianSim.hermitianEvolutionLipschitz_answer`
(full proof by the Duhamel integral) in the convention
`HamiltonianEvolution H t = e^{-iHt}`; the printed `e^{itH}` is obtained with
`t ↦ -t`.  The bridge below only fixes the sign convention.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Evolution

/-- The paper's forward-time evolution `e^{itH}`, in the library convention
`HamiltonianEvolution H t = e^{-iHt}`: `paperEvo H t = HamiltonianEvolution H (-t)`. -/
def paperEvo {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution H (-t)

/-- **Lemma 50.** arXiv:1804.01973v2, p. 55.  For Hermitian `H, H'` and real `t`,
`‖e^{itH} - e^{itH'}‖ ≤ |t| · ‖H - H'‖`.

The corresponding library theorem is
`Qatlib.Papers.QSingValue19.HamiltonianSim.hermitianEvolutionLipschitz_answer`,
which proves the library contract `HermitianEvolutionLipschitz` by the Duhamel
integral (both evolution factors unitary, C*-identity, integrate `[0, t]`). -/
theorem lemma50_evolution_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (H H' : Matrix I I ℂ) (hH : H.IsHermitian) (hH' : H'.IsHermitian) (t : ℝ) :
    ‖paperEvo H t - paperEvo H' t‖ ≤ |t| * ‖H - H'‖ := by
  have h := Qatlib.Concepts.QsvtCore.HamiltonianSim.hermitianEvolutionLipschitz_answer
    I H H' hH hH' (-t)
  simpa [paperEvo, abs_neg] using h

end Qatlib.Papers.BlockEncMatPw18.MainResults.Evolution
