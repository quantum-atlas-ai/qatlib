/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ResolventQPE24.MainResults.Prelude
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity

@[expose] public section


/-!
Normalization stability and explicit QLSA numerical cost-envelope inequalities.
These results do not assert resolvent-state preparation or a phase-estimation circuit.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ResolventQPE24.MainResults.ClosedBounds
open Qatlib.Papers.ResolventQPE24.MainResults.Prelude

/-- **Lemma 3.6 (complexity of preparing the resolvent state), p. 14,
Eq. (46).**  With `δ ∈ (0, ε_eig)` and accuracy `ε_st/2`, the QLSA-based
preparation of `|ψ̃_A⟩/‖|ψ̃_A⟩‖` (Eq. (45)) has query count bounded by
`C · α_A K_δ(A)/δ · log(1/ε_st)` for a constant `C` depending only on the
fixed parameters.

This is the composition of the QLSA cost
`α_M · α_M^{-1}-bound · log(1/ε)` (Lemma 2.14) with `α_M = 1+δ+α_A`
(Lemma 3.4) and `α_M^{-1}-bound ≤ K/δ` (Lemma 3.5).  The state-preparation
algorithm itself is not formalised; only its query ledger is. -/
theorem prepare_resolvent_state_unimodular
    (αA Kδ δ εeig εst : ℝ)
    (hαA : 0 < αA) (hKδ : 0 ≤ Kδ) (hδ : 0 < δ) (_hδε : δ < εeig)
    (_hε : 0 < εst) (hε1 : εst ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      qlsaQueryBound (1 + δ + αA) (Kδ / δ) (εst / 2) ≤
        C * (αA * Kδ / δ * Real.log (1 / εst)) := by
  have hB : 0 ≤ Kδ / δ := div_nonneg hKδ (le_of_lt hδ)
  have hlog : Real.log (1 / (εst / 2)) ≤ 2 * Real.log (1 / εst) := by
    have hsplit : Real.log (1 / (εst / 2)) = Real.log 2 + Real.log (1 / εst) := by
      rw [show 1 / (εst / 2) = 2 * (1 / εst) by field_simp]
      rw [Real.log_mul (by norm_num) (by positivity)]
    have h2 : Real.log 2 ≤ Real.log (1 / εst) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ _hε]
      nlinarith
    linarith
  refine ⟨2 * (1 + δ + αA) / αA, by positivity, ?_⟩
  have hbase : 0 ≤ (1 + δ + αA) * (Kδ / δ) := by positivity
  calc qlsaQueryBound (1 + δ + αA) (Kδ / δ) (εst / 2)
      = (1 + δ + αA) * (Kδ / δ) * Real.log (1 / (εst / 2)) := rfl
    _ ≤ (1 + δ + αA) * (Kδ / δ) * (2 * Real.log (1 / εst)) := by
        gcongr
    _ = (2 * (1 + δ + αA) / αA) * (αA * Kδ / δ * Real.log (1 / εst)) := by
        field_simp

/-- **Lemma 3.11 (normalised difference bound), p. 18, Eq. (89).**
If `‖x - xt‖ ≤ ε` and `x`, `xt` are nonzero, then
`‖x/‖x‖ - xt/‖xt‖‖ ≤ 2ε/‖x‖`. -/
theorem normalized_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x xt : E) (ε : ℝ) (_hε : 0 ≤ ε) (h : ‖x - xt‖ ≤ ε)
    (hx : x ≠ 0) (hxt : xt ≠ 0) :
    ‖((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt‖ ≤ 2 * ε / ‖x‖ := by
  have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hxt0 : (0 : ℝ) < ‖xt‖ := norm_pos_iff.mpr hxt
  have ha : ((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt =
      ((‖x‖ : ℝ)⁻¹) • (x - xt) +
        (((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹)) • xt := by
    rw [smul_sub]
    module
  have hq : |((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹)| * ‖xt‖ =
      |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ := by
    rw [show ((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹) =
      ((‖xt‖ : ℝ) - ‖x‖) / (‖x‖ * ‖xt‖) by
        field_simp]
    rw [abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hxt0]
    field_simp
  have hstep : ‖((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt‖ ≤
      (‖x‖ : ℝ)⁻¹ * ε + |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ := by
    rw [ha]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx0)]
    rw [hq]
    have h1 : (‖x‖ : ℝ)⁻¹ * ‖x - xt‖ ≤ (‖x‖ : ℝ)⁻¹ * ε := by gcongr
    linarith
  have hdiff : |(‖xt‖ : ℝ) - ‖x‖| ≤ ε := by
    calc |(‖xt‖ : ℝ) - ‖x‖| = |‖x‖ - ‖xt‖| := abs_sub_comm _ _
      _ ≤ ‖x - xt‖ := abs_norm_sub_norm_le x xt
      _ ≤ ε := h
  have hinv : (‖x‖ : ℝ)⁻¹ * ε + |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ ≤ 2 * ε / ‖x‖ := by
    rw [div_eq_inv_mul, div_eq_inv_mul]
    have h2 : |(‖xt‖ : ℝ) - ‖x‖| * (‖x‖ : ℝ)⁻¹ ≤ ε * (‖x‖ : ℝ)⁻¹ := by
      gcongr
    rw [mul_comm (‖x‖ : ℝ)⁻¹ ε]
    linarith
  exact hstep.trans hinv

/-- **Theorem 3.12 (complexity of solving QEUE), p. 19, Eq. (91).**
There is a constant `C` such that for every `ε_st ∈ (0,1]` one can choose
`δ ∈ Θ(ε_eig ε_st²/κ_S⁴)` (both bounds with constants recorded through `C`)
for which the QEUE query count `α_A K_δ°(A)/δ · log(1/ε_st)` is bounded by
`C · α_A κ_S⁴ K_δ°(A)/(ε_eig ε_st²) · log(1/ε_st)`.

This is the query-count consequence of Lemma 3.6 and Eq. (102); the circuit
construction and the state-accuracy analysis are not formalised. -/
theorem theorem3_12_query_complexity
    (αA κS Kδ εeig : ℝ) (hαA : 0 < αA) (hκS : 0 < κS) (hKδ : 0 ≤ Kδ)
    (hεeig : 0 < εeig) :
    ∃ C : ℝ, 0 < C ∧ ∀ εst : ℝ, 0 < εst → εst ≤ 1 →
      ∃ δ : ℝ, 0 < δ ∧
        (εeig * εst ^ 2 / κS ^ 4) / C ≤ δ ∧
        δ ≤ C * (εeig * εst ^ 2 / κS ^ 4) ∧
        αA * Kδ / δ * Real.log (1 / εst) ≤ C * qeueQueryBound αA κS Kδ εeig εst := by
  refine ⟨2, by norm_num, ?_⟩
  intro εst hεst hεst1
  have hx0 : 0 < εeig * εst ^ 2 / κS ^ 4 := by positivity
  refine ⟨εeig * εst ^ 2 / κS ^ 4, hx0, ?_, ?_, ?_⟩
  · linarith
  · nlinarith
  · rw [qeueQueryBound]
    have hlog : 0 ≤ Real.log (1 / εst) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hεst]
      linarith
    have hkl : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) := by positivity
    have hcost : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) :=
      mul_nonneg hkl hlog
    rw [show αA * Kδ / (εeig * εst ^ 2 / κS ^ 4) * Real.log (1 / εst) =
        αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) by
      field_simp]
    linarith

/-- A uniform real-resolvent QLSA cost envelope, with the fixed curve radius made explicit. -/
theorem prepare_resolvent_state_real
    (αA εeig ρ Kδ : ℝ) (hαA : 0 < αA) (hεeig : 0 < εeig)
    (_hρ : 0 ≤ ρ) (hKδ : 0 ≤ Kδ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ εst : ℝ,
      0 < δ → δ < εeig → 0 < εst → εst ≤ 1 / 2 →
      qlsaQueryBound (Real.sqrt (ρ ^ 2 + δ ^ 2) + αA) (Kδ / δ) (εst / 2) ≤
        C * (αA * Kδ / δ * Real.log (1 / εst)) := by
  refine ⟨2 * (Real.sqrt (ρ ^ 2 + εeig ^ 2) + αA) / αA, by positivity, ?_⟩
  intro δ εst hδ _hδε _hε hε1
  have hsqrt : Real.sqrt (ρ ^ 2 + δ ^ 2) ≤ Real.sqrt (ρ ^ 2 + εeig ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hlog : Real.log (1 / (εst / 2)) ≤ 2 * Real.log (1 / εst) := by
    have hsplit : Real.log (1 / (εst / 2)) = Real.log 2 + Real.log (1 / εst) := by
      rw [show 1 / (εst / 2) = 2 * (1 / εst) by field_simp]
      rw [Real.log_mul (by norm_num) (by positivity)]
    have h2 : Real.log 2 ≤ Real.log (1 / εst) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ _hε]
      nlinarith
    linarith
  have hlog0 : 0 ≤ Real.log (1 / εst) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ _hε]
    linarith
  have hloghalf : 0 ≤ Real.log (1 / (εst / 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity : 0 < εst / 2)]
    linarith
  calc qlsaQueryBound (Real.sqrt (ρ ^ 2 + δ ^ 2) + αA) (Kδ / δ) (εst / 2)
      ≤ (Real.sqrt (ρ ^ 2 + εeig ^ 2) + αA) * (Kδ / δ) *
          (2 * Real.log (1 / εst)) := by
        unfold qlsaQueryBound
        gcongr
    _ = (2 * (Real.sqrt (ρ ^ 2 + εeig ^ 2) + αA) / αA) *
        (αA * Kδ / δ * Real.log (1 / εst)) := by field_simp


end Qatlib.Papers.ResolventQPE24.MainResults.ClosedBounds
