/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPSolvers17.MainResults.Model.SdpInstance
public import Qatlib.Papers.QSDPSolvers17.MainResults.Costs

@[expose] public section


/-! # Closed predicate and scalar-budget facts from arXiv:1710.02581.
No quantum search, state preparation, or tomography implementation is asserted. -/
set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.QuantumInput

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QSDPSolvers17.MainResults.Model
open Qatlib.Papers.QSDPSolvers17.MainResults
open scoped ComplexOrder MatrixOrder BigOperators

variable {m D : ℕ}

/-- The input state violates constraint `j` by `ε`: `Tr(A_j ρ) ≥ a_j + ε` (App. D). -/
def Violates (P : SdpInstance m D) (ρ : Operator D) (ε : ℝ) : Prop :=
  ∃ j, P.a j + ε ≤ (Matrix.trace (P.A j * ρ)).re

/-- The input state is exactly feasible: `Tr(A_j ρ) ≤ a_j` for every `j` (App. D). -/
def ExactlyFeasible (P : SdpInstance m D) (ρ : Operator D) : Prop :=
  ∀ j, (Matrix.trace (P.A j * ρ)).re ≤ P.a j

/-- Unfolding the violation predicate supplies a witnessing constraint index. -/
theorem oracle_A1_finds_violation (P : SdpInstance m D) (ρ : Operator D) {ε : ℝ}
    (h : Violates P ρ ε) :
    ∃ j, P.a j + ε ≤ (Matrix.trace (P.A j * ρ)).re :=
  h

/-- An exactly feasible state has no positive-slack violated constraint. -/
theorem oracle_A1_feasible (P : SdpInstance m D) (ρ : Operator D) {ε : ℝ}
    (hε : 0 < ε) (h : ExactlyFeasible P ρ) :
    ¬ Violates P ρ ε := by
  rintro ⟨j, hj⟩
  have := h j
  -- Feasibility gives `Tr ≤ a_j`, the violation gives `a_j + ε ≤ Tr`, and `ε > 0`.
  linarith

/-- The exponential of minus the inverse-probability logarithm equals that probability. -/
theorem oracle_A1_amplification {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-(Real.log (1 / δ))) = δ := by
  rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
  field_simp

/-- Sample budget of Lemma 3: `log(1/δ)·Õ(S_Tr(B,ε))` copies of `ρ`, with the polylog
overhead `log m + 1` made explicit. -/
noncomputable def a1SampleBudget (δ STr : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 / δ) * ((STr + 1) * (Real.log m + 1))

/-- Gate budget of Lemma 3: `log(1/δ)·Õ(√m·T_Tr(B,ε))` gates and oracle queries, with
the binary search's `poly(log m)` overhead and the `+1` for the feasible case. -/
noncomputable def a1GateBudget (δ TTr : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 / δ) * ((Real.sqrt m * (TTr + 1) + 1) * (Real.log m + 1))

/-- The violation predicate, feasibility exclusion, exponential identity and defined budgets hold together; no search is constructed. -/
theorem oracle_A1_lemma (P : SdpInstance m D) (ρ : Operator D) {ε δ : ℝ}
    (hε0 : 0 < ε) (hδ0 : 0 < δ) (STr TTr : ℝ) :
    (Violates P ρ ε → ∃ j, P.a j + ε ≤ (Matrix.trace (P.A j * ρ)).re) ∧
      (ExactlyFeasible P ρ → ¬ Violates P ρ ε) ∧
      Real.exp (-(Real.log (1 / δ))) = δ ∧
      a1SampleBudget δ STr m =
        Real.log (1 / δ) * ((STr + 1) * (Real.log m + 1)) ∧
      a1GateBudget δ TTr m =
        Real.log (1 / δ) * ((Real.sqrt m * (TTr + 1) + 1) * (Real.log m + 1)) :=
  ⟨fun h => oracle_A1_finds_violation P ρ h,
    fun h => oracle_A1_feasible P ρ hε0 h,
    oracle_A1_amplification hδ0,
    rfl, rfl⟩


end Qatlib.Papers.QSDPSolvers17.MainResults.QuantumInput
