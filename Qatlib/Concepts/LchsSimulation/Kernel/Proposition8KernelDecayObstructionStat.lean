/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel

/-!
# Kernel decay obstruction specification

`Proposition8KernelDecayObstruction` states that exponential real-axis decay is incompatible
with a nonzero bounded analytic kernel on the lower half-plane. The statement includes
continuity on the closed half-plane and positive constants in the exponential bound. See
[AnChildsLin2026] for the mathematical setting.

## Main statements

* `Proposition8KernelDecayObstruction`: The vanishing specification for a bounded analytic
  lower-half-plane function whose real-axis norm is bounded by `c₀ * Real.exp (-c * |k|)` with
  positive `c` and `c₀`, corresponding to [An, Childs, and Lin, Proposition 8][AnChildsLin2026].

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.Kernel

/-- The vanishing specification for a bounded analytic lower-half-plane function whose real-axis
norm is bounded by `c₀ * Real.exp (-c * |k|)` with positive `c` and `c₀`, corresponding to
[An, Childs, and Lin, Proposition 8][AnChildsLin2026]. -/
def Proposition8KernelDecayObstruction : Prop :=
  ∀ (f : ℂ → ℂ),
    AnalyticOnNhd ℂ f {z : ℂ | z.im < 0} →
    ContinuousOn f {z : ℂ | z.im ≤ 0} →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ≤ 0 → ‖f z‖ ≤ C) →
    (∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ ∀ k : ℝ, ‖f (k : ℂ)‖ ≤ c₀ * Real.exp (-c * |k|)) →
    ∀ z : ℂ, z.im ≤ 0 → f z = 0

end Qatlib.Concepts.LchsSimulation.Kernel
