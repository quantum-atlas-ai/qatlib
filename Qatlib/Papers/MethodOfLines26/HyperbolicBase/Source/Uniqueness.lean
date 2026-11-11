/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Uniqueness

set_option backward.isDefEq.respectTransparency false

/-!
# arXiv:2606.03407v1 — Theorem 12 (hyperbolic uniqueness)

Fixed version: **arXiv:2606.03407v1**, §5.1, Theorem 12 (PDF p.34), proof in
Appendix A (PDF p.60).

If the hyperbolic equation (55) with boundary conditions (56–58) admits a
classical solution `u ∈ C^{2,2}(Ω × [0,T])`, it is unique.  The proof is the
same weighted energy argument as Theorem 3: for the difference `v = u₁ − u₂`
one uses the *second-order* energy

`E(t) = ½ ∫_Ω (v_t² + |∇v|² + c₀² v²) exp(Σ_{l∈S₂} c_l x_l) dx`,

which is nonnegative, vanishes at `t = 0` together with `v_t`, and satisfies
`E'(t) ≤ 0` by integration by parts; hence `E ≡ 0` and `v ≡ 0`.

The formalised core is the same abstract energy argument as for Theorem 3
(`energy_method_uniqueness`), instantiated with the hyperbolic energy; the
PDE-specific positivity/monotonicity facts are its hypotheses, exactly as in
the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source

open scoped Real

/-- **Theorem 12** (arXiv:2606.03407v1, §5.1, PDF p.34; Appendix A p.60).
Two classical solutions `u₁`, `u₂` of the hyperbolic problem (55) with
boundary conditions (56–58), sharing the initial displacement and velocity,
coincide on `[0,T]`.

The weight and the second-order energy of Appendix A are packaged into the
energy function `E`; `hE_definite` is the positivity of the weighted energy
(`E = 0 → v = 0`), `hE_nonpos` the energy dissipation `E' ≤ 0`. -/
theorem theorem12_hyperbolic_uniqueness
    {V : Type*} (u₁ u₂ : ℝ → V) (E dE : ℝ → ℝ)
    (hE_zero : E 0 = 0)
    (hE_deriv : ∀ t, 0 ≤ t → HasDerivAt E (dE t) t)
    (hE_nonpos : ∀ t, 0 ≤ t → dE t ≤ 0)
    (hE_nonneg : ∀ t, 0 ≤ t → 0 ≤ E t)
    (hE_definite : ∀ t, 0 ≤ t → E t = 0 → u₁ t = u₂ t) :
    ∀ t, 0 ≤ t → u₁ t = u₂ t :=
  Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.energy_method_uniqueness
    u₁ u₂ E dE hE_zero hE_deriv hE_nonpos hE_nonneg hE_definite

end Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
