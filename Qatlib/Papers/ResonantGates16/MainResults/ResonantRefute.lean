/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ResonantGates16.MainResults.Forward
public import Mathlib.Tactic

@[expose] public section


/-! Endpoint counterexamples to the legacy resonant-pulse characterizations. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open Qatlib.Papers.ResonantGates16.MainResults.SourceModel
open Qatlib.Papers.ResonantGates16.MainResults.AchievableTuples

namespace Qatlib.Papers.ResonantGates16.MainResults.ContractRefute

/-- The actual phase-product semantics force A(1)=1, stronger than the legacy disjunction. -/
theorem achievable_A_one {L : ℕ} {A B C D : Polynomial ℝ}
    (h : Achievable L A B C D) : A.eval 1 = 1 := by
  obtain ⟨φs, hφ⟩ := h
  have hU0 : tupleMatrix L A B C D 0 = 1 := by
    rw [← hφ 0, responseMatrix_zero]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hU0
  by_cases hL : L % 2 = 1
  · simpa [tupleMatrix, hL, sigmaX, sigmaY, sigmaZ, idMat] using h00
  · simpa [tupleMatrix, hL, sigmaX, sigmaY, sigmaZ, idMat] using h00

/-- A negative identity tuple satisfies every legacy algebraic condition but is unachievable. -/
theorem theorem1_contract_false :
    ¬ (∀ (L : ℕ) (A B C D : Polynomial ℝ), DegreeOK L A B C D →
      (Achievable L A B C D ↔
        ParityOK L A B C D ∧ EndpointOK A B ∧ NormOK L A B C D)) := by
  intro h
  have hdeg : DegreeOK 0 (-1) 0 0 0 := by simp [DegreeOK]
  have hcond : ParityOK 0 (-1) 0 0 0 ∧ EndpointOK (-1) 0 ∧
      NormOK 0 (-1) 0 0 0 := by
    simp [ParityOK, OddPoly, EvenPoly, EndpointOK, NormOK]
  have hach := (h 0 (-1) 0 0 0 hdeg).mpr hcond
  have hA := achievable_A_one hach
  norm_num at hA

/-- The legacy AC and A converse bounds admit the unachievable negative constant. -/
theorem partial_A_counterexample :
    ParityOK 0 (-1) 0 0 0 ∧
      (∀ θ : ℝ, ((-1 : Polynomial ℝ).eval (Real.cos (θ / 2))) ^ 2 +
          (Real.cos (θ / 2)) ^ 2 *
            ((0 : Polynomial ℝ).eval (Real.sin (θ / 2))) ^ 2 ≤ 1) ∧
      ¬ AchievableAC 0 (-1) 0 ∧ ¬ AchievableA 0 (-1) := by
  refine ⟨by simp [ParityOK, OddPoly, EvenPoly], by simp, ?_, ?_⟩
  · rintro ⟨B, D, hach⟩
    have hA := achievable_A_one hach
    norm_num at hA
  · rintro ⟨B, C, D, hach⟩
    have hA := achievable_A_one hach
    norm_num at hA

/-- Zero A and C meet every legacy fidelity-completion hypothesis but cannot be achieved. -/
theorem fidelity_contract_false :
    ¬ (∀ (L : ℕ) (A C : Polynomial ℝ),
      L % 2 = 1 → A.natDegree ≤ L ∧ C.natDegree ≤ L →
      OddPoly A ∧ OddPoly C →
      (∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2 +
        (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) →
      ∃ B D : Polynomial ℝ, Achievable L A B C D) := by
  intro h
  obtain ⟨B, D, hach⟩ := h 1 0 0 (by norm_num) (by simp)
    (by simp [OddPoly]) (by simp)
  have hA := achievable_A_one hach
  norm_num at hA

/-- Negative X and zero B meet every transition-completion hypothesis but violate A(1)=1. -/
theorem transition_contract_false :
    ¬ (∀ (L : ℕ) (A B : Polynomial ℝ),
      L % 2 = 1 → A.natDegree ≤ L ∧ B.natDegree ≤ L →
      OddPoly A ∧ OddPoly B → EndpointOK A B →
      (∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2 +
        (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1) →
      (∀ x : ℝ, 1 ≤ x → (A.eval x) ^ 2 + (B.eval x) ^ 2 ≥ 1) →
      ∃ C D : Polynomial ℝ, Achievable L A B C D) := by
  intro h
  have hdeg : (-X : Polynomial ℝ).natDegree ≤ 1 ∧
      (0 : Polynomial ℝ).natDegree ≤ 1 := by simp
  have hpar : OddPoly (-X : Polynomial ℝ) ∧ OddPoly (0 : Polynomial ℝ) := by
    simp [OddPoly]
  have hend : EndpointOK (-X : Polynomial ℝ) 0 := by simp [EndpointOK]
  have hinside : ∀ θ : ℝ,
      ((-X : Polynomial ℝ).eval (Real.cos (θ / 2))) ^ 2 +
        ((0 : Polynomial ℝ).eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
    intro θ
    simp only [Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    nlinarith [Real.cos_sq_add_sin_sq (θ / 2), sq_nonneg (Real.sin (θ / 2))]
  have houtside : ∀ x : ℝ, 1 ≤ x →
      ((-X : Polynomial ℝ).eval x) ^ 2 + ((0 : Polynomial ℝ).eval x) ^ 2 ≥ 1 := by
    intro x hx
    simp only [Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_zero,
      zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    nlinarith
  obtain ⟨C, D, hach⟩ := h 1 (-X) 0 (by norm_num) hdeg hpar hend hinside houtside
  have hA := achievable_A_one hach
  norm_num at hA

end Qatlib.Papers.ResonantGates16.MainResults.ContractRefute
