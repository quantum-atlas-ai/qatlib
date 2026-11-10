/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.Kernel

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.Quadrature

open MeasureTheory
open scoped Matrix.Norms.L2Operator

def Lemma12CoefficientMass : Prop :=
  ∀ (β : ℝ) (K Q M : ℕ) (node weight : Fin Q → ℝ),
    0 < β → β < 1 → 1 ≤ K → 1 ≤ Q → 1 ≤ M →
    (∀ q, 0 < weight q) →
    (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) →
    let h : ℝ := (2 * K : ℝ) / M
    let nodeAt : Fin M → Fin Q → ℝ :=
      fun m q => (-K : ℝ) + h * ((m : ℝ) + (node q + 1) / 2)
    (∑ m : Fin M, ∑ q : Fin Q,
        ‖(h / 2) * weight q * highKernelG β (nodeAt m q)‖) ≤
      (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * (1 - β))) +
        (2 * (K : ℝ)) / (3 * highKernelC β) * (16 * h) ^ (2 * Q)

end Qatlib.Concepts.LchsSimulation.Quadrature
