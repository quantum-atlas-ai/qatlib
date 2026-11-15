/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.HamiltonianQuery
public import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
public import Qatlib.Concepts.TrotterFormula.LieStrang.HermitianEvolutionStability

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Foundations.QueryWordCore.HamiltonianQuery Qatlib.Concepts.ReferenceError.MixturePaths

set_option autoImplicit false
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost
open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Running a Hamiltonian query program preserves subtraction of input states. -/
theorem hamiltonianQueryRun_sub (H : Matrix I I ℂ) (p : List (HamiltonianQueryStep I))
    (ψ φ : QState I) :
    HamiltonianQueryRun H p (ψ - φ) = HamiltonianQueryRun H p ψ - HamiltonianQueryRun H p φ := by
  induction p generalizing ψ φ with
  | nil => rfl
  | cons step p ih =>
    cases step <;> simp only [HamiltonianQueryRun, ApplyGate, Matrix.mulVec_sub] <;> apply ih

/-- A valid query program for a Hermitian Hamiltonian preserves the Euclidean norm of every
input state. -/
theorem norm_hamiltonianQueryRun (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (p : List (HamiltonianQueryStep I)) (hp : HamiltonianQueryValid p) (ψ : QState I) :
    ‖toEuclidean_fromVec (HamiltonianQueryRun H p ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  induction p generalizing ψ with
  | nil => rfl
  | cons step p ih =>
    have hp' : HamiltonianQueryValid p := fun U hU => hp U (List.mem_cons_of_mem _ hU)
    cases step with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup I ℂ := hp U List.mem_cons_self
      simp only [HamiltonianQueryRun, ih hp', norm_applyGate_of_mem_unitaryGroup hU]
    | evolve t =>
      simp only [HamiltonianQueryRun, ih hp',
        norm_applyGate_of_mem_unitaryGroup (hamiltonianEvolution_unitary hH t)]

/-- The output distance between valid runs with two Hermitian Hamiltonians is bounded by total
evolution time times their operator norm distance times the input norm. -/
theorem norm_hamiltonianQueryRun_sub_le
    (H K : Matrix I I ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (p : List (HamiltonianQueryStep I)) (hp : HamiltonianQueryValid p) (ψ : QState I) :
    ‖toEuclidean_fromVec (HamiltonianQueryRun H p ψ - HamiltonianQueryRun K p ψ)‖
      ≤ HamiltonianEvolutionTime p * ‖H - K‖ * ‖toEuclidean_fromVec ψ‖ := by
  induction p generalizing ψ with
  | nil => simp [HamiltonianQueryRun, HamiltonianEvolutionTime, toEuclidean_fromVec]
  | cons step p ih =>
    have hp' : HamiltonianQueryValid p := fun U hU => hp U (List.mem_cons_of_mem _ hU)
    cases step with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup I ℂ := hp U List.mem_cons_self
      have h := ih hp' (ApplyGate U ψ)
      rw [norm_applyGate_of_mem_unitaryGroup hU] at h
      exact h
    | evolve t =>
      let U := HamiltonianEvolution H t
      let V := HamiltonianEvolution K t
      have hs : HamiltonianQueryRun H (.evolve t :: p) ψ -
          HamiltonianQueryRun K (.evolve t :: p) ψ =
          HamiltonianQueryRun H p (ApplyGate U ψ - ApplyGate V ψ) +
            (HamiltonianQueryRun H p (ApplyGate V ψ) - HamiltonianQueryRun K p (ApplyGate V ψ)) := by
        simp only [HamiltonianQueryRun, hamiltonianQueryRun_sub]
        module
      have hstep : ‖toEuclidean_fromVec (ApplyGate U ψ - ApplyGate V ψ)‖ ≤
          |t| * ‖H - K‖ * ‖toEuclidean_fromVec ψ‖ := by
        have he : ApplyGate U ψ - ApplyGate V ψ = ApplyGate (U - V) ψ := by
          simp only [ApplyGate, Matrix.sub_mulVec]
        rw [he]
        exact (norm_applyGate_le _ _).trans
          (mul_le_mul_of_nonneg_right (hermitian_evolution_noncommuting_stability_fintype H K t hH hK) (norm_nonneg _))
      have htail := ih hp' (ApplyGate V ψ)
      rw [norm_applyGate_of_mem_unitaryGroup (hamiltonianEvolution_unitary hK t)] at htail
      rw [hs]
      calc
        _ ≤ ‖toEuclidean_fromVec (HamiltonianQueryRun H p (ApplyGate U ψ - ApplyGate V ψ))‖ +
            ‖toEuclidean_fromVec (HamiltonianQueryRun H p (ApplyGate V ψ) -
              HamiltonianQueryRun K p (ApplyGate V ψ))‖ := norm_add_le _ _
        _ ≤ |t| * ‖H - K‖ * ‖toEuclidean_fromVec ψ‖ +
            HamiltonianEvolutionTime p * ‖H - K‖ * ‖toEuclidean_fromVec ψ‖ := by
          rw [norm_hamiltonianQueryRun H hH p hp']
          exact add_le_add hstep htail
        _ = _ := by simp only [HamiltonianEvolutionTime]; ring

end Qatlib.Concepts.QuantumGibbs.SamplingCost
