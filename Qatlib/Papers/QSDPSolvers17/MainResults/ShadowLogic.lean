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

namespace Qatlib.Papers.QSDPSolvers17.MainResults.ShadowTomography

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QSDPSolvers17.MainResults.Model
open Qatlib.Papers.QSDPSolvers17.MainResults
open scoped ComplexOrder MatrixOrder BigOperators

variable {m n D : ℕ}

/-- A measurement deviates by `ε` between `σ` and `ρ`: `|Tr(σE_i) - Tr(ρE_i)| ≥ ε`. -/
def Deviates (E : Fin m → Operator D) (ρ σ : Operator D) (ε : ℝ) : Prop :=
  ∃ i, ε ≤ |(Matrix.trace (σ * E i)).re - (Matrix.trace (ρ * E i)).re|

/-- All measurements deviate by at most `ε/2`. -/
def CloseAll (E : Fin m → Operator D) (ρ σ : Operator D) (ε : ℝ) : Prop :=
  ∀ i, |(Matrix.trace (σ * E i)).re - (Matrix.trace (ρ * E i)).re| ≤ ε / 2

/-- Unfolding the deviation predicate supplies a witnessing measurement index. -/
theorem shadow_or_finds_deviation (E : Fin m → Operator D) (ρ σ : Operator D) {ε : ℝ}
    (h : Deviates E ρ σ ε) :
    ∃ i, ε ≤ |(Matrix.trace (σ * E i)).re - (Matrix.trace (ρ * E i)).re| :=
  h

/-- Measurements all within half the positive tolerance cannot violate the full tolerance. -/
theorem shadow_or_feasible (E : Fin m → Operator D) (ρ σ : Operator D) {ε : ℝ}
    (hε : 0 < ε) (h : CloseAll E ρ σ ε) :
    ¬ Deviates E ρ σ ε := by
  rintro ⟨i, hi⟩
  have := h i
  linarith

/-- The `poly(log m, log n, r, ε⁻¹, log δ⁻¹)` copy budget of Lemma 2, with every factor
written explicitly. -/
noncomputable def shadowCopyBudget (r ε δ : ℝ) (m n : ℕ) : ℝ :=
  (Real.log (m : ℝ) + 1) * (Real.log (n : ℝ) + 1) * (r + 1) * (ε⁻¹ + 1) *
    (Real.log (1 / δ) + 1)

/-- The `√m·poly(log m, log n, r, ε⁻¹, log δ⁻¹)` gate budget of Lemma 2. -/
noncomputable def shadowGateBudget (r ε δ : ℝ) (m n : ℕ) : ℝ :=
  Real.sqrt m * shadowCopyBudget r ε δ m n

/-- The defined copy-budget expression is nonnegative under positive accuracy and dimension assumptions. -/
theorem shadowCopyBudget_nonneg (r ε δ : ℝ) (m n : ℕ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ shadowCopyBudget r ε δ m n := by
  have hlogm : 0 ≤ Real.log (m : ℝ) + 1 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have := Real.log_nonneg hmR; linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) + 1 := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have := Real.log_nonneg hnR; linarith
  have hδ1' : (1 : ℝ) ≤ 1 / δ := by
    rw [one_le_div hδ]; linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) + 1 := by
    have := Real.log_nonneg hδ1'; linarith
  unfold shadowCopyBudget
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hlogm hlogn)
    (by linarith)) (by positivity)) hlogδ

/-- The deviation exclusion and nonnegative budget formulas hold together; no measurement algorithm is constructed. -/
theorem shadow_or_lemma (E : Fin m → Operator D) (ρ σ : Operator D) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (r : ℝ) (hr : 0 ≤ r)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (Deviates E ρ σ ε →
        ∃ i, ε ≤ |(Matrix.trace (σ * E i)).re - (Matrix.trace (ρ * E i)).re|) ∧
      (CloseAll E ρ σ ε → ¬ Deviates E ρ σ ε) ∧
      0 ≤ shadowCopyBudget r ε δ m n ∧
      0 ≤ shadowGateBudget r ε δ m n := by
  refine ⟨fun h => shadow_or_finds_deviation E ρ σ h,
    fun h => shadow_or_feasible E ρ σ hε h, ?_, ?_⟩
  · exact shadowCopyBudget_nonneg r ε δ m n hr hε (by omega) (by omega) hδ hδ1
  · unfold shadowGateBudget
    exact mul_nonneg (Real.sqrt_nonneg _)
      (shadowCopyBudget_nonneg r ε δ m n hr hε (by omega) (by omega) hδ hδ1)

/-- The scalar failure and shadow-budget expressions satisfy their arithmetic identities and nonnegativity. -/
theorem shadow_tomography_corollary (r ε : ℝ) (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hε : 0 < ε) (hr : 0 ≤ r) :
    (1 - totalFailure n ε ≥ 0.96) ∧
      shadowGateBudget r ε (1 / 2) m n =
        Real.sqrt m * shadowCopyBudget r ε (1 / 2) m n ∧
      0 ≤ shadowGateBudget r ε (1 / 2) m n := by
  refine ⟨plain_model_success_probability hn hε, rfl, ?_⟩
  unfold shadowGateBudget
  exact mul_nonneg (Real.sqrt_nonneg _)
    (shadowCopyBudget_nonneg r ε (1 / 2) m n hr hε (by omega) (by omega) (by norm_num) (by norm_num))

end Qatlib.Papers.QSDPSolvers17.MainResults.ShadowTomography
