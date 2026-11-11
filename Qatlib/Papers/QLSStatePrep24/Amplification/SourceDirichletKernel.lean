/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.TightDirichletBoundsLows

set_option backward.isDefEq.respectTransparency false

/-!
# SourceDirichletKernel — tight bounds for the Dirichlet kernel

Low--Su, fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

Proposition 16 (p.45, Eqs. (267)–(268)) gives the two-sided bound
`1 - ρ² sin²θ/6 ≤ sin(ρθ)/(ρ sin θ) ≤ 1 - ((4π-8)/π³) ρ² sin²θ` for
`ρ ≥ 3`, `0 ≤ ρθ ≤ π/2`, proves that the constants `1/6` and
`(4π-8)/π³` are optimal, and records the explicit form `gainLoss 3 a =
1 - (4/3)a²`. This is the frozen contract `Clause7TightDirichletBounds`, proved by
`Clause7TightDirichletBounds_answer`.

Boundary: analytic inequalities only; no query-complexity conclusion.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.QLSStatePrep24.Amplification

/-- Fixed arXiv:2410.18178v2, Proposition 16 (p.45): the Dirichlet-kernel
bounds with sharp constants, and the `ρ = 3` value of the amplification gain
`gainLoss 3 a = 1 - (4/3) a²`. The four conjuncts are exactly the frozen
`Clause7TightDirichletBounds`. -/
theorem prop16_tight_dirichlet_bounds : Clause7TightDirichletBounds :=
  Clause7TightDirichletBounds_answer

/-- Fixed arXiv:2410.18178v2, Eq. (267): the lower bound of the Dirichlet
kernel, extracted from `Clause7TightDirichletBounds_answer`. -/
theorem prop16_dirichlet_lower_bound (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 ≤ θ)
    (hρθ : (ρ : ℝ)*θ ≤ Real.pi/2) :
    1 - (ρ : ℝ)^2*(Real.sin θ)^2/6 ≤
      (if θ = 0 then 1 else Real.sin (ρ*θ)/(ρ*Real.sin θ)) :=
  (Clause7TightDirichletBounds_answer).1 ρ θ hρ hθ hρθ |>.1

/-- Fixed arXiv:2410.18178v2, Eq. (267): the upper bound of the Dirichlet
kernel, extracted from `Clause7TightDirichletBounds_answer`. -/
theorem prop16_dirichlet_upper_bound (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 ≤ θ)
    (hρθ : (ρ : ℝ)*θ ≤ Real.pi/2) :
    (if θ = 0 then 1 else Real.sin (ρ*θ)/(ρ*Real.sin θ)) ≤
      1 - ((4*Real.pi-8)/Real.pi^3)*(ρ : ℝ)^2*(Real.sin θ)^2 :=
  (Clause7TightDirichletBounds_answer).1 ρ θ hρ hθ hρθ |>.2

/-- Fixed arXiv:2410.18178v2, Proposition 16 (p.45), in particular clause:
`gainLoss 3 a = 1 - (4/3) a²` for `0 ≤ a ≤ 1`. -/
theorem prop16_gain_loss_three (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    gainLoss 3 a = 1 - (4/3)*a^2 :=
  (Clause7TightDirichletBounds_answer).2.2.2 a h0 h1

end Qatlib.Papers.QLSStatePrep24.Amplification
