module

import Qatlib.Papers.QCryptanal15.MainResults.OperatorSearch

set_option autoImplicit false
set_option warningAsError true

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
open Qatlib.Papers.QCryptanal15.MainResults
open scoped Matrix.Norms.L2Operator

namespace QatlibTests.QCryptanal15OperatorConsumer

example (A : Finset (Fin 4)) :
    groverStep A ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  grover_step_unitary A (by decide)

example (A : Finset (Fin 4)) :
    ‖groverStep A‖ = 1 :=
  grover_step_l2Operator_norm A (by decide)

example (A : Finset (Fin 4)) (ψ : EuclideanSpace ℂ (Fin 4)) :
    ‖(WithLp.toLp 2 (groverStep A *ᵥ ψ.ofLp) : EuclideanSpace ℂ (Fin 4))‖ = ‖ψ‖ :=
  grover_step_euclidean_norm A (by decide) ψ

example :
    ∃ C : ℝ, 0 < C ∧
      ∀ {J : Type*} [Fintype J] [DecidableEq J]
        (A : Finset J) (eps : ℝ),
        0 < eps → eps < 1 →
        (A.card : ℝ) / (Fintype.card J : ℝ) = eps →
        ∃ k : ℕ,
          0 < Fintype.card J ∧
          (k : ℝ) ≤ C / Real.sqrt eps + 1 ∧
            1 / 2 ≤ MeasureProb (GroverState A k) A :=
  grover_half_success_uniform_constant

end QatlibTests.QCryptanal15OperatorConsumer
