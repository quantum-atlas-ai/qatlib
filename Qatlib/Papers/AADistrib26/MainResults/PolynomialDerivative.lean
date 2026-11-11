/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers

set_option backward.isDefEq.respectTransparency false

/-!
# Derivative bound for polynomials on `[0,1]` (arXiv:2609.35327v1, Corollary 2.9)

Corollary 2.9 of Girish--Mittal--Nehoran--Raz, fixed at arXiv:2609.35327v1,
states `sup_{[0,1]} |g'| ≤ 2 d² sup_{[0,1]} |g|` for a real polynomial of degree
at most `d`. The frozen Markov route proves the same statement with constant
`4 d²`; the factor two is the library's recorded constant adaptation. This file
records that weakened but faithful form and does not claim the sharp constant.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

/-- Corollary 2.9 at the frozen constant: a degree-`d` polynomial bounded by `C`
on `[0,1]` has derivative bounded by `4d²C` there. The paper's constant is
`2d²`; this declaration is the partial-coverage form. -/
theorem corollary29_unit_deriv_le_four {d : ℕ} {g : Polynomial ℝ} (hd : g.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g.eval x| ≤ C) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |g.derivative.eval x| ≤ 4 * (d : ℝ) ^ 2 * C :=
  markov_brothers_unit_deriv_le hd hC hb

end Qatlib.Papers.AADistrib26.MainResults
