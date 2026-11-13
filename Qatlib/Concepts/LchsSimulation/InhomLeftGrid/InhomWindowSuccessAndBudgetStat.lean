/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionStat

/-!
# Statement of inhomogeneous LCHS window guarantees

`InhomogeneousWindowSuccessAndBudget` specifies the iteration distribution, marked success, and
word budgets for a compiled inhomogeneous LCHS approximation. It assumes a positive
solution-norm lower bound τ, approximation error ε at most τ/2, and the stated unitary
preparation and generator conditions. This gives a concrete finite-grid preparation estimate
related to [AnLiuLin2023].

## Main statements

* `InhomogeneousWindowSuccessAndBudget`: normalized iteration weights, success at least 1/8, and
  explicit finite word bounds.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the inhomogeneous LCHS window has normalized iteration weights, length
at most `2*α/τ + 1`, average marked success at least 1/8, and separate input and selection
word-count bounds of `2*m + 1` under the stated approximation hypotheses. -/
def InhomogeneousWindowSuccessAndBudget : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t ε τ : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ)
    (i₀ : I),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t → B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin Mt, b (inhNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhNode Mt s t l)) →
    0 < K → 0 < N → 0 < Mt → 0 < ε → 0 < τ → ε ≤ τ / 2 →
    let A := fun u => L u + Complex.I • H u
    let γ := inhUnifiedCoeff b s t K N Mt
    let V := inhUnifiedUnitary L H s t K N Mt B P
    let uT := orderedForcedSolution A b s (B *ᵥ Ket i₀) t
    τ ≤ ‖toEuclidean_fromVec uT‖ →
    ‖toEuclidean_fromVec ((∑ x, γ x • V x) *ᵥ (B *ᵥ Ket i₀) - uT)‖ ≤ ε →
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass γ
    let m := staticLchsWindow α τ
    (∑ j : Fin m, staticLchsIterationWeight m j) = 1 ∧ (m : ℝ) ≤ 2*α/τ + 1 ∧
    ∀ j₀ : Fin (N + N * Mt),
    let S := Finset.univ.filter (fun x : Fin (N + N * Mt) × I => x.1 = j₀)
    (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile γ V B j₀ i₀ j.val)
        (Ket (j₀, i₀))) S ∧
    (∀ j : Fin m,
      (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤
        2*m+1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤
        2*m+1)

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
