/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Concepts.SearchStopping.KnownCount
open scoped BigOperators

noncomputable abbrev SearchCircuit (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :=
  GroverCircuit I j

noncomputable abbrev SearchState {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (j : ℕ) := GroverState A j

noncomputable abbrev WithMinus {I : Type*} (ψ : QState I) := TensorState ψ Minus

alias search_grover_success := Qatlib.Concepts.SearchStopping.KnownCount.measureProb_groverState
alias search_grover_state := Qatlib.Concepts.SearchStopping.KnownCount.groverState_eq

theorem search_circuit_laws {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (j : ℕ) :
    QueryCount (SearchCircuit I j) = j ∧ Normalized (SearchState A j) ∧
      MeasureProb (SearchState A j) ∅ = 0 ∧
      MeasureProb (SearchState A j) Finset.univ = 1 := by
  refine ⟨queryCount_groverCircuit j, normalized_groverState hN A j, ?_,
    measureProb_univ (normalized_groverState hN A j)⟩
  simp [MeasureProb]

theorem search_principal_angle {I : Type*} [Fintype I] (A : Finset I)
    (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) ∧
      0 < Real.sin (2 * θ) := by
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast (lt_trans hA hproper)
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hpr : (A.card : ℝ) < Fintype.card I := by exact_mod_cast hproper
  have hp : (0 : ℝ) < (A.card : ℝ) / Fintype.card I := div_pos hAr hN
  have hp1 : (A.card : ℝ) / Fintype.card I < 1 := (div_lt_one hN).2 hpr
  have hsqrt : 0 < Real.sqrt ((A.card : ℝ) / Fintype.card I) := Real.sqrt_pos.mpr hp
  have hsqrt1 : Real.sqrt ((A.card : ℝ) / Fintype.card I) < 1 := by
    nlinarith [Real.sq_sqrt hp.le]
  let θ := Real.arcsin (Real.sqrt ((A.card : ℝ) / Fintype.card I))
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr hsqrt
  have hθp : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hsqrt1
  refine ⟨θ, hθ0, hθp, ?_, ?_⟩
  · rw [Real.sin_arcsin (by linarith : -1 ≤ Real.sqrt ((A.card : ℝ) / Fintype.card I)) hsqrt1.le,
      Real.sq_sqrt hp.le]
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem search_bit_oracle_compile_phase {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool) (C : Circuit I) (ψ : QState I) :
    QueryCount (LiftCircuit C) = QueryCount C ∧
    Run (BitOracleOn f) (LiftCircuit C) (WithMinus ψ) =
      WithMinus (Run (PhaseOracle f) C ψ) ∧
    ∀ S : Finset I,
      MeasureProb (Run (BitOracleOn f) (LiftCircuit C) (WithMinus ψ)) (S ×ˢ Finset.univ) =
        MeasureProb (Run (PhaseOracle f) C ψ) S :=
  ⟨queryCount_liftCircuit C, run_liftCircuit_bitOracleOn f C ψ,
    measureProb_run_liftCircuit_bitOracleOn f C ψ⟩

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
