/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HittingTimes08.MainResults.HittingInteger
public import Qatlib.Papers.HittingTimes08.MainResults.Comparison
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PhaseEstimationCost

@[expose] public section

/-!
# From spectral and scalar estimates to hitting-time bounds

Pointwise cosine estimates give the comparison with the reciprocal-square phase
mean. The singleton projection formula turns the scalar norm estimate in
Lemma 3.12 into a bound on the projection itself. Rounding up the binary logarithm
gives a phase-estimation level with explicit power and additional gate bounds.
-/

set_option autoImplicit false

open Qatlib.Papers.HittingTimes08.MainResults
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Concepts.FourierRecovery.ModularFourier
open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.HittingTimes08.MainResults

/-- The source cosine sum lies between twice and four times the reciprocal-square mean. -/
theorem two_mul_mean_le_cosMean {J : Type*} [Fintype J] (L : HittingLaw J)
    (hθ : ∀ j, L.theta j ≤ Real.pi / 2) :
    2 * L.mean ≤ (∑ j, L.mass j / (1 - Real.cos (L.theta j))) ∧
      (∑ j, L.mass j / (1 - Real.cos (L.theta j))) ≤ 4 * L.mean := by
  have hterm (j : J) :
      2 * L.val j ≤ 1 / (1 - Real.cos (L.theta j)) ∧
        1 / (1 - Real.cos (L.theta j)) ≤ 4 * L.val j := by
    let den := 1 - Real.cos (L.theta j)
    have hv := L.val_pos j
    have hθp := L.theta_pos j
    have hlo := HittingLaw.one_sub_cos_ge _ hθp.le (hθ j)
    have hhi := HittingLaw.one_sub_cos_le (L.theta j)
    have hd : 0 < den := lt_of_lt_of_le (by positivity) hlo
    rw [L.theta_sq j] at hlo hhi
    have ha := mul_le_mul_of_nonneg_right hlo hv.le
    have hb := mul_le_mul_of_nonneg_right hhi hv.le
    have ha' : (1 : ℝ) / 4 ≤ den * L.val j := by
      change (1 / L.val j / 4) * L.val j ≤ _ at ha
      rwa [show (1 / L.val j / 4) * L.val j = 1 / 4 by field_simp] at ha
    have hb' : den * L.val j ≤ (1 : ℝ) / 2 := by
      change den * L.val j ≤ (1 / L.val j / 2) * L.val j at hb
      rwa [show (1 / L.val j / 2) * L.val j = 1 / 2 by field_simp] at hb
    exact ⟨(le_div_iff₀ hd).2 (by linarith), (div_le_iff₀ hd).2 (by linarith)⟩
  constructor
  · rw [HittingLaw.mean, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left (hterm j).1 (L.mass_nonneg j)
    simpa only [mul_left_comm (L.mass j) 2, ← mul_div_assoc, mul_one] using h
  · rw [HittingLaw.mean, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left (hterm j).2 (L.mass_nonneg j)
    simpa only [mul_left_comm (L.mass j) 4, ← mul_div_assoc, mul_one] using h

/-- The ratio estimated in Appendix B is the norm of the orthogonal projection onto
the line spanned by the difference vector. -/
theorem projection_length_ge_inv_sqrt_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (φ s : E) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hin : ‖inner ℂ s φ‖ = 2 * a * c) (hs : ‖s‖ ≤ Real.sqrt (8 * a ^ 2 * c ^ 2)) :
    1 / Real.sqrt 2 ≤ ‖(Submodule.span ℂ {s}).starProjection φ‖ := by
  have hs0 : 0 < ‖s‖ := by
    apply norm_pos_iff.mpr
    intro hz
    rw [hz, inner_zero_left, norm_zero] at hin
    linarith [mul_pos (show 0 < (2 : ℝ) * a by positivity) hc]
  have hsNorm : ‖(Submodule.span ℂ {s}).starProjection φ‖ = ‖inner ℂ s φ‖ / ‖s‖ := by
    rw [Submodule.starProjection_singleton ℂ, norm_smul, norm_div]
    change ‖inner ℂ s φ‖ / ‖((‖s‖ ^ 2 : ℝ) : ℂ)‖ * ‖s‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    field_simp
  rw [hsNorm, hin]
  exact (lemma_3_12_projection ha hc).trans (div_le_div_of_nonneg_left (by positivity) hs0 hs)

/-- The ceiling binary logarithm chooses a level with power within twice the reciprocal
precision, while the corresponding exact QFT has the recorded quadratic gate count. -/
theorem estimate_levels_budget (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    ∃ m : ℕ, 1 / Δ ≤ (2 : ℝ) ^ m ∧ (2 : ℝ) ^ m ≤ 2 / Δ ∧
      (m : ℝ) ≤ Real.logb 2 (1 / Δ) + 1 ∧ qftElementaryGates m ≤ 3 * (m + 1) ^ 2 := by
  let x := Real.logb 2 (1 / Δ)
  have h1 : 1 ≤ 1 / Δ := (le_div_iff₀ hΔ).2 (by simpa using hΔ1)
  have hrec : (0 : ℝ) < 1 / Δ := zero_lt_one.trans_le h1
  have hx : 0 ≤ x := Real.logb_nonneg (by norm_num) h1
  let m := ⌈x⌉₊
  have hm : x ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
  have heq : (2 : ℝ) ^ x = 1 / Δ := Real.rpow_logb (by norm_num) (by norm_num) hrec
  have hp : (2 : ℝ) ^ (m : ℝ) = (2 : ℝ) ^ m := Real.rpow_natCast _ _
  refine ⟨m, ?_, ?_, hmu, qft_elementary_gates_quadratic m⟩
  · rw [← hp, ← heq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
  · rw [← hp]
    calc
      _ ≤ (2 : ℝ) ^ (x + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hmu
      _ = _ := by rw [Real.rpow_add (by norm_num), heq, Real.rpow_one]; ring

end Qatlib.Papers.HittingTimes08.MainResults
