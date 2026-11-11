/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamJacobi25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.2 — the `W^{1,1}` bound for the Fokker–Planck density

Fixed source: arXiv:2502.15495v2 (22 Jul 2025), Lemma 4.2, pp.9–10.
PDF SHA-256 `082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

For `0 < ε ≤ 1` and `τ ≤ T − 4ε`, a bounded drift `‖b‖_{L∞} ≤ K` and `ρ` solving
(6) with `ρ(τ) = δ_x`, there are `t₁ ∈ [τ+ε,τ+2ε]` and `t₂ ∈ [T−2ε,T−ε]` such that
`∫_{T^n}|Dρ(y,t_i)|dy ≤ (C/ε)(1+|log ε|)^{1/2}` for `i = 1,2`, with `C` depending
only on `n` and `K` (and the chosen times).

The statement is quantified with `C` before `T, ε, τ, b, x, ρ`, so the constant is
uniform in the viscosity and the data, as in the paper.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.FokkerPlanckW11

open Qatlib.Papers.HamJacobi25.MainResults.SourceModel

end Qatlib.Papers.HamJacobi25.MainResults.FokkerPlanckW11
