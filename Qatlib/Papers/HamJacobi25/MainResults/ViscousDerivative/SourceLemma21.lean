/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2.1 — the ε-derivative of the viscous solution

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Lemma 2.1, p.5, equation (9).
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

The paper assumes that `H` satisfies (H) or (H_γ), that `u_ε` solves (1) for every
`ε > 0`, and proves that `v^ε = ∂_ε u_ε` is well defined, belongs to
`C^{2+α,1+α/2}(T^n × [0,T])`, solves the linearized equation (9) in the classical
sense, and has zero terminal datum.  The statement below keeps every one of those
clauses; it is a conjunction, not a weakened corollary.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.ViscousDerivative

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.ViscousDerivative
