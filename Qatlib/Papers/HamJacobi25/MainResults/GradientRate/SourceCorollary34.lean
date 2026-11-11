/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.ConvergenceRate.SourceTheorem31

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 3.4 — gradient convergence rate in `L^∞_t L²_x`

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Corollary 3.4, p.8.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

Under the assumptions of Theorem 3.1, for every `β ∈ (1/2,1)` there is `C = C(β) > 0`
such that `‖Du_ε − Du‖_{L∞(0,T;L²(T^n))} ≤ C ε^{β/2}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.GradientRate

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.GradientRate
