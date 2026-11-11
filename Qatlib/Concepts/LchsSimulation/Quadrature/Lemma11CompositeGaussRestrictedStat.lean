/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Qatlib.Concepts.LchsSimulation.TimeLchs

/-!
# Restricted composite Gauss specification

`Lemma11CompositeGaussRestrictedCorrected` states a conditional global quadrature bound for the
near-exponential LCHS integrand. Its premise supplies cellwise derivative-norm witnesses and
remainder estimates, so polynomial exactness of an arbitrary supplied rule is not asserted by
this proposition. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `Lemma11CompositeGaussRestrictedCorrected`: The conditional composite Gauss specification
  bounding the cutoff-interval error from the stated cellwise derivative-norm witnesses and
  remainder inequalities, corresponding to a restricted form of [An, Childs, and Lin, Lemma
  11][AnChildsLin2026].

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.Quadrature

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

/-- The conditional composite Gauss specification bounding the cutoff-interval error from the
stated cellwise derivative-norm witnesses and remainder inequalities, corresponding to a
restricted form of [An, Childs, and Lin, Lemma 11][AnChildsLin2026]. -/
def Lemma11CompositeGaussRestrictedCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (T β Λ : ℝ)
    (K Q M : ℕ) (node weight : Fin Q → ℝ),
    Continuous L → Continuous H →
    (∀ u, (L u).IsHermitian) → (∀ u, (H u).IsHermitian) →
    0 ≤ T → 0 < Λ → 32 ≤ Real.exp 1 * T * Λ → 0 < β → β < 1 → 0 < K → 0 < Q → 0 < M →
    (∀ u ∈ Icc 0 T, ‖L u‖ ≤ Λ) →
    let h : ℝ := (2 * K : ℝ) / M
    let U : ℝ → Matrix I I ℂ := fun k =>
      orderedEvolution (fun u => Complex.I • (H u + k • L u)) 0 T
    let nodeAt : Fin M → Fin Q → ℝ :=
      fun m q => (-K : ℝ) + h * ((m : ℝ) + (node q + 1) / 2)
    let cellSum : Fin M → Matrix I I ℂ := fun m =>
      ∑ q : Fin Q, ((h / 2) * weight q * highKernelG β (nodeAt m q)) • U (nodeAt m q)
    (∃ s : Fin M → ℝ,
        (∀ m : Fin M, ∃ k ∈ Icc ((-K : ℝ) + h * (m : ℝ)) ((-K : ℝ) + h * ((m : ℝ) + 1)),
          ‖iteratedDeriv (2 * Q) (fun k : ℝ => highKernelG β k • U k) k‖ = s m) ∧
        (∀ m : Fin M,
          ‖(∫ k in ((-K : ℝ) + h * (m : ℝ))..((-K : ℝ) + h * ((m : ℝ) + 1)),
              highKernelG β k • U k) - cellSum m‖ ≤
            ((Q.factorial : ℝ) ^ 4 * h ^ (((2 : ℝ) * Q) + 1)) /
                (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
              s m)) →
      ‖(∑ m : Fin M, cellSum m) -
          ∫ k in (-K : ℝ)..(K : ℝ), highKernelG β k • U k‖ ≤
        (8 / (3 * highKernelC β)) * K * h ^ ((2 : ℝ) * Q) *
          (Real.exp 1 * T * Λ / 2) ^ ((2 : ℝ) * Q)

end Qatlib.Concepts.LchsSimulation.Quadrature
