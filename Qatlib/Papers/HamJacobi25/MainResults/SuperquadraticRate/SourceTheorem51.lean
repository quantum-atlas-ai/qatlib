/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.ConvergenceRate.SourceTheorem31

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5.1 — rates for superquadratic strictly convex Hamiltonians

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Theorem 5.1, p.14.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

Under (H_γ), if `u_ε` solves (1) and `u` solves (2), there is
`β_γ ∈ (1/2,1)`, depending on `γ`, such that for every `β < β_γ`
`−C ε^β ≤ u_ε − u ≤ (T‖(Δu_T)^+‖_{L∞_x} + ‖(Δf)^+‖_{L¹_t(L∞_x)}) ε`,
with `C` depending on `n`, `θ`, `γ`, `β` and the data norms.

The upper bound is the same `O(ε)` estimate as Theorem 3.1; the lower bound
deteriorates to `O(ε^{β_γ})` with the explicit `β_γ` of equation (23).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.SuperquadraticRate

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.SuperquadraticRate
