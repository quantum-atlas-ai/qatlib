/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.CountedParityAlgorithm
import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.PhysicalReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.ParityLimit98.MainResults.OptimalAlgorithm

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

set_option autoImplicit false

def zeroErrorDecidesParity (N : ℕ)
    (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
    (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
    (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))) : Prop :=
  ∀ f : Fin N → Bool,
    MeasureProb (Run (TensorGate (BitOracleOn f)
        (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)) C ψ) E =
      if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then 1 else 0

theorem parity_optimal_construction (N : ℕ) (hN : 0 < N) :
    ∃ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = (N + 1) / 2 ∧
        zeroErrorDecidesParity N C ψ E := by
  obtain ⟨hU, hNrm, hQ, _hG, hAcc⟩ := parity_actual_pairwise_query_upper_consumer N hN
  exact ⟨countedParityCircuit N, countedParityInitial N hN, countedParityAccept N,
    hU, hNrm, hQ, hAcc⟩

theorem parity_optimal_even_half (N : ℕ) (hN : 0 < N) (hEven : N % 2 = 0) :
    ∃ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = N / 2 ∧
        zeroErrorDecidesParity N C ψ E := by
  obtain ⟨C, ψ, E, hU, hNrm, hQ, hAcc⟩ := parity_optimal_construction N hN
  refine ⟨C, ψ, E, hU, hNrm, ?_, hAcc⟩
  rw [hQ]
  omega

theorem parity_optimal_odd_half (N : ℕ) (hN : 0 < N) (_hOdd : N % 2 = 1) :
    ∃ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = (N + 1) / 2 ∧
        zeroErrorDecidesParity N C ψ E :=
  parity_optimal_construction N hN

theorem parity_optimal_tight (N : ℕ) (hN : 0 < N) :
    (∃ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = (N + 1) / 2 ∧
        zeroErrorDecidesParity N C ψ E) ∧
    (∀ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C → Normalized ψ →
      (∀ f : Fin N → Bool,
        |MeasureProb (Run (TensorGate (BitOracleOn f)
            (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)) C ψ) E
          - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1
            then (1 : ℝ) else 0)| ≤ 1 / 3) →
      (N + 1) / 2 ≤ QueryCount C) := by
  refine ⟨parity_optimal_construction N hN, ?_⟩
  exact (parity_query_complexity_tight N hN).2.2.2

open Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

theorem parity_sharp_query_complexity (N : ℕ) (hN : 0 < N) :
    (∃ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = (N + 1) / 2 ∧
        zeroErrorDecidesParity N C ψ E) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W]
      (C : Circuit (PolynomialWorkspace (Fin N) W)) (_hC : IsUnitaryCircuit C)
      (ψ : QState (PolynomialWorkspace (Fin N) W)) (_hn : Normalized ψ)
      (P : Matrix (PolynomialWorkspace (Fin N) W) (PolynomialWorkspace (Fin N) W) ℂ)
      (_hP : IsOrthogonalProjector P) (ε : ℝ) (_hε : 0 < ε),
      (∀ f, 1 / 2 + ε ≤ projectorCorrectness C ψ P f) → (N + 1) / 2 ≤ QueryCount C) := by
  refine ⟨parity_optimal_construction N hN, ?_⟩
  intro W _ _ C hC ψ hn P hP ε hε hs
  have h := physical_positive_bias_query_bound C hC ψ hn P hP ε hε hs
  omega

end Qatlib.Papers.ParityLimit98.MainResults.OptimalAlgorithm
