/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2.3 — the weighted gradient/second-order bound

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Lemma 2.3, p.6.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

The lemma is stated under (H) or (H_γ) (only local Lipschitz continuity of `H` is
really used).  For every `(x,τ) ∈ T^n × [0,T]` and every adjoint density `ρ` solving
(6) issued from `δ_x`, it bounds `|Du_ε(x,τ)| + ε∫_τ^T∫_{T^n}|D²u_ε|²ρ` by a constant
`C_L` depending on `‖Du_T‖_{L∞_x}`, `‖Df‖_{L∞_{x,t}}` and `T`.

The adjoint equation (6) carries the drift `−div(D_pH(Du_ε)ρ)`; since
`SolvesAdjoint` writes the drift as `+div(bρ)`, the statement instantiates
`b = −D_pH(Du_ε)`, exactly as the paper does in the proof of Lemma 4.3 (p.11).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.GradientBound

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.GradientBound
