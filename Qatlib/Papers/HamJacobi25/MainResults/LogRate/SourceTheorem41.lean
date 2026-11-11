/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.ConvergenceRate.SourceTheorem31

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.1 — the `ε|log ε|` sup-norm rate

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Theorem 4.1, p.9.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

Under (H), for every `ε ∈ (0,1)` and `τ ∈ [0,T)`,
`‖(u_ε − u)(τ)‖_{L∞(T^n)} ≤ C(T−τ)^{-1/2} ε|log ε|`, where `C` depends on `n`,
`‖Du_T‖_{L∞_x}`, `T`, `‖(Δf)^+‖_{L∞_{x,t}}`, `θ`, `Θ`.

This is the improvement of the left-hand side from Section 3 to the critical
`O(ε|log ε|)` rate under Lipschitz (not semiconcave) terminal data.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.LogRate

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.LogRate
