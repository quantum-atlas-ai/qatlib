/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionStat

/-!
# Specification of forced LCHS window success and budgets

`InhomogeneousTrapezoidWindowSuccessAndBudget` records the finite-window guarantee for a unified
forced-solution approximation. Its assumptions include unitary preparations, vector error at
most `ε ≤ τ / 2`, and forced output norm at least `τ`; its conclusion gives normalized iteration
weights, a window bound, constant success, and access budgets.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `InhomogeneousTrapezoidWindowSuccessAndBudget`: specifies the window distribution, success,
  and resource bounds.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the unified trapezoidal window has weights summing to one, size at most
`2 * α / τ + 1`, success at least `1 / 8`, and per-word input and selection access counts at
most `2 * m + 1` under the stated approximation hypotheses. -/
def InhomogeneousTrapezoidWindowSuccessAndBudget : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t ε τ : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (i₀ : I),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t → B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhTrapNode Mt s t l)) →
    0 < K → 0 < N → 0 < Mt → 0 < ε → 0 < τ → ε ≤ τ / 2 →
    let A := fun u => L u + Complex.I • H u
    let γ := inhTrapUnifiedCoeff b s t K N Mt
    let V := inhTrapUnifiedUnitary L H s t K N Mt B P
    let uT := orderedForcedSolution A b s (B *ᵥ Ket i₀) t
    τ ≤ ‖toEuclidean_fromVec uT‖ →
    ‖toEuclidean_fromVec ((∑ x, γ x • V x) *ᵥ (B *ᵥ Ket i₀) - uT)‖ ≤ ε →
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass γ
    let m := staticLchsWindow α τ
    (∑ j : Fin m, staticLchsIterationWeight m j) = 1 ∧ (m : ℝ) ≤ 2*α/τ + 1 ∧
    ∀ j₀ : Fin (N + N * (Mt + 1)),
    let S := Finset.univ.filter (fun x : Fin (N + N * (Mt + 1)) × I => x.1 = j₀)
    (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile γ V B j₀ i₀ j.val)
        (Ket (j₀, i₀))) S ∧
    (∀ j : Fin m,
      (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤
        2*m+1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤
        2*m+1)

end Qatlib.Concepts.LchsSimulation.TrapPrepared
