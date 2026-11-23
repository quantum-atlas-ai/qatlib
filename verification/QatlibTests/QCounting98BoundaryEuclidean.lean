module

public import Qatlib.Papers.QCounting98.MainResults.BoundaryEuclidean

@[expose] public section

/-!
# Concrete consumer for the QCounting98 Euclidean boundary

The fixed two-qubit ancilla is normalized and supported on both basis states of the
first-register-zero subspace. The examples use the unit rank-one phase `Complex.I` and the
common sign phase `-1` from the first-register-zero reflection.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.QCounting98BoundaryEuclidean

open Qatlib.Papers.QCounting98.MainResults.Boundary
open Qatlib.Papers.QCounting98.MainResults.BoundaryEuclidean
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.QueryWordCore.Circuit

/-- Instantiate the uniform bound at the rank-one phase `Complex.I` on the fixed ancilla. -/
example :
    ∃ C > 0,
      C ≤ ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
          literalRankOne Complex.I ancillaInput)‖ := by
  obtain ⟨C, hC, hbound⟩ := firstZero_literal_Euclidean_separation
  exact ⟨C, hC, hbound Complex.I⟩

/-- Apply the explicit lower bound to the original comparison at the shared phase `-1`. -/
example :
    Real.sqrt 2 ≤
      ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
          literalRankOne (-1) ancillaInput)‖ :=
  firstZero_literal_Euclidean_separation_sqrt_two (-1)

/-- The consumer input is normalized, excluding the vacuous zero-state branch. -/
example : Normalized ancillaInput := ancillaInput_normalized

/-- The concrete phase has unit modulus, matching the phase-oracle premise. -/
example : ‖(Complex.I : ℂ)‖ = 1 := by
  exact Complex.norm_I

#print axioms firstZero_literal_Euclidean_separation_sqrt_two
#print axioms firstZero_literal_Euclidean_separation

end QatlibTests.QCounting98BoundaryEuclidean
