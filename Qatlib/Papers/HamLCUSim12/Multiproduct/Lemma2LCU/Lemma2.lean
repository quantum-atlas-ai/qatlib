/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2FiberCorrectedHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedHami

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2 — two-term linear combination of unitaries

Fixed source: arXiv:1202.5822v1, Lemma 2, p.2 (§II):
for unitary `U_a, U_b` with `Delta = ||U_a - U_b||` and `kappa >= 0`, there is a
circuit implementing an operator proportional to `kappa U_a + U_b` with failure
probability at most `Delta^2 kappa/(kappa+1)^2 <= 4 kappa/(kappa+1)^2`.

Model: the frozen Figure-1 circuit of the corrected source reading.  The success
branch is exact (`(kappa U_a + U_b)/(kappa+1)` on the `|0>` fiber; `sqrt(kappa)(U_b-U_a)/(kappa+1)`
on the `|1>` fiber), the sharp failure bound uses the uniform Euclidean action
bound `Delta`, and the crude bound follows because `Delta <= 2` for unitary
differences.  The `Delta`-free crude consequence is recorded separately as
`lemma2_crude_of_sharp`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2LCU

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.HamLCUSim12.Multiproduct
open Qatlib.Papers.HamLCUSim12.LCUDeferred

/-- Fixed arXiv:1202.5822v1, Lemma 2: the Figure-1 circuit gives the exact success
fiber `(kappa U_a + U_b)/(kappa+1)`, the failure fiber `sqrt(kappa)(U_b-U_a)/(kappa+1)`,
and failure probability `<= kappa Delta^2/(kappa+1)^2`. -/
theorem lemma2_two_term_lcu {I : Type} [Fintype I] [DecidableEq I] (κ : ℝ) (hκ : 0 ≤ κ)
    (Ua Ub : Matrix I I ℂ) (hUa : Ua ∈ Matrix.unitaryGroup I ℂ)
    (hUb : Ub ∈ Matrix.unitaryGroup I ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ φ : QState I, Normalized φ →
      (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) :
    (∀ ψ : QState I,
        (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => false, x)
            = ((((κ : ℂ) / (κ + 1)) • Ua + (((1 : ℂ) / (κ + 1)) • Ub)) *ᵥ ψ) x)
        ∧ (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => true, x)
            = (((((Real.sqrt κ / (κ + 1) : ℝ) : ℂ)) • (Ub - Ua)) *ᵥ ψ) x))
      ∧ (∀ ψ : QState I, Normalized ψ →
          lemma2FailureProbCorrected κ Ua Ub ψ ≤ κ * Δ ^ 2 / (κ + 1) ^ 2) := by
  refine ⟨fun ψ => lemma2FiberCorrected I κ hκ Ua Ub hUa hUb ψ, ?_⟩
  intro ψ hψ
  exact lemma2NearbyFailureCorrected I κ hκ Ua Ub hUa hUb Δ hΔ hbound ψ hψ

/-- The chained inequality of Lemma 2: since `Delta = ||U_a - U_b|| <= 2` for unitary
`U_a, U_b`, the sharp bound `kappa Delta^2/(kappa+1)^2` is at most the crude bound
`4 kappa/(kappa+1)^2`. -/
theorem lemma2_crude_of_sharp (κ Δ : ℝ) (hκ : 0 ≤ κ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2) :
    κ * Δ ^ 2 / (κ + 1) ^ 2 ≤ 4 * κ / (κ + 1) ^ 2 := by
  have hden : 0 < (κ + 1) ^ 2 := by positivity
  have hsq : Δ ^ 2 ≤ 4 := by nlinarith
  have hnum : κ * Δ ^ 2 ≤ 4 * κ := by nlinarith
  exact div_le_div_of_nonneg_right hnum hden.le

/-- Fixed arXiv:1202.5822v1, Lemma 2, crude form: the failure probability is at most
`4 kappa/(kappa+1)^2` (obtained from the sharp bound and `Delta <= 2`). -/
theorem lemma2_crude_failure {I : Type} [Fintype I] [DecidableEq I] (κ : ℝ) (hκ : 0 ≤ κ)
    (Ua Ub : Matrix I I ℂ) (hUa : Ua ∈ Matrix.unitaryGroup I ℂ)
    (hUb : Ub ∈ Matrix.unitaryGroup I ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hΔ2 : Δ ≤ 2)
    (hbound : ∀ φ : QState I, Normalized φ →
      (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2)
    (ψ : QState I) (hψ : Normalized ψ) :
    lemma2FailureProbCorrected κ Ua Ub ψ ≤ 4 * κ / (κ + 1) ^ 2 := by
  have hsharp := (lemma2_two_term_lcu κ hκ Ua Ub hUa hUb Δ hΔ hbound).2 ψ hψ
  exact le_trans hsharp (lemma2_crude_of_sharp κ Δ hκ hΔ hΔ2)

end Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2LCU
