/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.GradientRate.SourceCorollary34

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 3.5 — convergence of the conservation-law system

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Corollary 3.5, p.9, equations (13)-(14).
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

If `H` is uniformly convex and `p₀ = Du₀` with `p₀ ∈ C¹(T^n)`, then for every
`β ∈ (1/2,1)` there is `C = C(β) > 0` such that the solution `p^ε` of the
quasilinear parabolic system (13) converges to the solution `p` of the hyperbolic
system (14) at rate `‖p^ε_i − p_i‖_{L²(Q_T)} ≤ C ε^{β/2}`.

The two systems are encoded by `SolvesParabolicConservation` and
`SolvesHyperbolicConservation`; the hypothesis `p₀ = Du₀` is kept explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.ConservationLawRate

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.ConservationLawRate
