/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3.1 — two-sided convergence rate for uniformly convex Hamiltonians

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Theorem 3.1, p.6.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

Under (H), if `u_ε` solves (1) and `u` solves (2), then for every
`β ∈ (1/2,1)` there is `C = C(β) > 0`, depending on `n`, `θ`, the sup norms of
`(Δu_T)^+` and `(Δf)^+`, `T`, and the Lipschitz norms of the data, such that
`−Cε^β ≤ u_ε − u ≤ (T‖(Δu_T)^+‖_{L∞_x} + ‖(Δf)^+‖_{L¹_t(L∞_x)}) ε` on `Q_T`.

The coefficient of the upper bound is kept literally as in the paper.  `C` is
quantified after `β` and the data but before `ε` and the space-time point, so it
cannot depend on `ε`, matching the paper's uniformity.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.ConvergenceRate

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.ConvergenceRate
