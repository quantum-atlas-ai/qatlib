/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.3 — weighted second-order estimate

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Lemma 4.3, p.11.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

For `0 < ε ≤ 1` and `τ ≤ T − 4ε`, there is `C` depending on `n`,
`‖Du_ε(T)‖_{L∞_x}` and `T`, and there are `t₁ ∈ [τ+ε,τ+2ε]`,
`t₂ ∈ [T−2ε,T−ε]`, such that
`∫_{t₁}^{t₂}∫_{T^n}(t−τ)(T−t)|D²u_ε|²ρ dx dt ≤ C(1+|log ε|)`,
where `ρ` solves (6) with drift `−D_pH(Du_ε)`.

The constant is quantified before `ε,τ,x,ρ` but after the solution family, so it is
uniform in the viscosity and in the chosen point, while retaining the dependence on
`‖Du_ε(T)‖_{L∞}` and `T` stated in the paper.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.WeightedSecondOrder

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.WeightedSecondOrder
