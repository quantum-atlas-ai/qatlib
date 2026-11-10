/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeLchs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.LchsRep

open MeasureTheory
open scoped ComplexOrder Matrix.Norms.L2Operator

def GeneralAnalyticKernelLchs : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (f : ℂ → ℂ) (L H : ℝ → Matrix I I ℂ)
    (s t : ℝ),
    DifferentiableOn ℂ f {z : ℂ | z.im ≤ 0} →
    (∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧ ∀ z : ℂ, z.im ≤ 0 → ‖z‖ ^ α * ‖f z‖ ≤ C) →
    (∫ k : ℝ, f (k : ℂ) / (1 - Complex.I * (k : ℂ))) = 1 →
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t →
      (∀ i j : I, Integrable (fun k : ℝ =>
          (f (k : ℂ) / (1 - Complex.I * (k : ℂ))) *
            (orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) i j)) ∧
      (∫ k : ℝ, (f (k : ℂ) / (1 - Complex.I * (k : ℂ))) •
          orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) =
        orderedEvolution (fun u => L u + Complex.I • H u) s t

end Qatlib.Concepts.LchsSimulation.LchsRep
