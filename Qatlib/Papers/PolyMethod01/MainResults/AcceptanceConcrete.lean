/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

@[expose] public section

/-!
# A concrete one-query acceptance polynomial

This module instantiates the polynomial method on a one-bit oracle query.  Starting from the
answer-zero basis state, the event that the answer bit is one has acceptance polynomial `X 0`.
The example is finite, non-empty, and has a genuine nonzero query count, so it witnesses the
Born-probability and degree claims without an empty-event or zero-query degeneration.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PolyMethod01.MainResults

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

abbrev oneWorkspace := PolynomialWorkspace (Fin 1) (Fin 1)

def oneQueryCircuit : Circuit oneWorkspace := [Step.query]

def oneQueryInput : QState oneWorkspace := Ket ((0, false), 0)

def oneQueryAccepted : Finset oneWorkspace := {((0, true), 0)}

/-- The one-query circuit has exactly one oracle query. -/
theorem oneQueryCircuit_queryCount : QueryCount oneQueryCircuit = 1 := by
  rfl

/-- The one-query circuit's accepted event has the Born probability of the queried bit. -/
theorem oneQuery_measure_probability (f : Fin 1 → Bool) :
    MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          oneQueryCircuit oneQueryInput)
        oneQueryAccepted =
      if f 0 then (1 : ℝ) else 0 := by
  classical
  simp [oneQueryCircuit, oneQueryInput, oneQueryAccepted, Run, Ket, TensorGate,
    ApplyGate, BitOracleOn, BitFlip, permMatrix, Matrix.mulVec, dotProduct,
    BornProb, MeasureProb]
  by_cases h : f 0 = true <;> simp [h]

def oneQueryAcceptedVector (f : Fin 1 → Bool) : EuclideanSpace ℂ (Fin 1) :=
  WithLp.toLp 2 (fun i =>
    Run (TensorGate (BitOracleOn f) (1 : Matrix (Fin 1) (Fin 1) ℂ))
      oneQueryCircuit oneQueryInput ((i, true), 0))

/-- On the concrete accepted slice, Born probability is the squared Euclidean ℓ₂ norm. -/
theorem oneQuery_probability_eq_euclidean_norm_sq (f : Fin 1 → Bool) :
    MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          oneQueryCircuit oneQueryInput)
        oneQueryAccepted = ‖oneQueryAcceptedVector f‖ ^ 2 := by
  rw [oneQuery_measure_probability]
  by_cases h : f 0 = true <;>
    simp [oneQueryAcceptedVector, oneQueryCircuit, oneQueryInput, Run, Ket, TensorGate,
      ApplyGate, BitOracleOn, BitFlip, permMatrix, Matrix.mulVec, dotProduct,
      EuclideanSpace.norm_sq_eq, h]

/-- The concrete acceptance polynomial is multilinear, has degree at most twice the query count,
and evaluates to the nontrivial queried-bit probability. -/
theorem oneQuery_acceptance_spec :
    (booleanAcceptancePolynomial oneQueryCircuit oneQueryInput oneQueryAccepted).totalDegree ≤
        2 * QueryCount oneQueryCircuit ∧
      (∀ d : Fin 1 →₀ ℕ,
        (booleanAcceptancePolynomial oneQueryCircuit oneQueryInput oneQueryAccepted).coeff d ≠ 0 →
          ∀ i, d i ≤ 1) ∧
      ∀ f : Fin 1 → Bool,
        MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0)
            (booleanAcceptancePolynomial oneQueryCircuit oneQueryInput oneQueryAccepted) =
          if f 0 then (1 : ℝ) else 0 := by
  obtain ⟨hdegree, hmulti, heval⟩ :=
    acceptance_boolean_multilinearization_preserves_run
      oneQueryCircuit oneQueryInput oneQueryAccepted
  refine ⟨hdegree, hmulti, ?_⟩
  intro f
  rw [heval, oneQuery_measure_probability]

end Qatlib.Papers.PolyMethod01.MainResults
