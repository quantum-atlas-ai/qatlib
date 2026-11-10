/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.Kernel

def Proposition8KernelDecayObstruction : Prop :=
  ∀ (f : ℂ → ℂ),
    AnalyticOnNhd ℂ f {z : ℂ | z.im < 0} →
    ContinuousOn f {z : ℂ | z.im ≤ 0} →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ≤ 0 → ‖f z‖ ≤ C) →
    (∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ ∀ k : ℝ, ‖f (k : ℂ)‖ ≤ c₀ * Real.exp (-c * |k|)) →
    ∀ z : ℂ, z.im ≤ 0 → f z = 0

end Qatlib.Concepts.LchsSimulation.Kernel
