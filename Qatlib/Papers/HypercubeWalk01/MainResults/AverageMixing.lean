/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.ContinuousWalk
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

noncomputable def avgContDist (n : ℕ) (T : ℝ) (x : Cube n) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, contDist n t x

noncomputable def avgContCoeff (n : ℕ) (T : ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, contCoeffByWeight n t S.card

lemma integral_cos_sq_scaled {n : ℕ} (hn : 0 < n) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.cos (2 * t / n) ^ 2 =
      (n : ℝ) / 4 * (Real.cos (2 * T / n) * Real.sin (2 * T / n)) + T / 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hc : (2 / (n : ℝ)) ≠ 0 := by positivity
  have harg : ∀ t : ℝ, 2 * t / (n : ℝ) = (2 / (n : ℝ)) * t := by
    intro t
    ring
  simp_rw [harg]
  rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.cos x ^ 2)
    (a := (0 : ℝ)) (b := T) (c := 2 / (n : ℝ)) hc]
  rw [integral_cos_sq]
  have hinv : (2 / (n : ℝ))⁻¹ = (n : ℝ) / 2 := by rw [inv_div]
  rw [hinv, smul_eq_mul]
  have hb : (2 / (n : ℝ)) * T = 2 * T / (n : ℝ) := by ring
  have hb0 : (2 / (n : ℝ)) * (0 : ℝ) = 0 := by ring
  simp only [hb0, hb, Real.cos_zero, Real.sin_zero, mul_zero, sub_zero]
  have hnu : (n : ℝ) * (2 * T / (n : ℝ)) = 2 * T := mul_div_cancel₀ (2 * T) hn0
  have key : (n : ℝ) / 2 * ((2 * T / (n : ℝ)) / 2) = T / 2 := by
    calc (n : ℝ) / 2 * ((2 * T / (n : ℝ)) / 2) = (n * (2 * T / (n : ℝ))) / 4 := by ring
      _ = (2 * T) / 4 := by rw [hnu]
      _ = T / 2 := by ring
  have hcs : (n : ℝ) / 2 *
        (Real.cos (2 * T / (n : ℝ)) * Real.sin (2 * T / (n : ℝ)) / 2)
      = (n : ℝ) / 4 *
        (Real.cos (2 * T / (n : ℝ)) * Real.sin (2 * T / (n : ℝ))) := by ring
  have hexp : (n : ℝ) / 2 *
        ((Real.cos (2 * T / (n : ℝ)) * Real.sin (2 * T / (n : ℝ)) + 2 * T / (n : ℝ)) / 2)
      = (n : ℝ) / 2 *
          (Real.cos (2 * T / (n : ℝ)) * Real.sin (2 * T / (n : ℝ)) / 2) +
        (n : ℝ) / 2 * ((2 * T / (n : ℝ)) / 2) := by ring
  rw [hexp, hcs, key]

lemma integral_cos_sq_scaled_eq10 {n : ℕ} (hn : 0 < n) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.cos (2 * t / n) ^ 2 =
      T / 2 + (n : ℝ) / 8 * Real.sin (4 * T / n) := by
  rw [integral_cos_sq_scaled hn T]
  have hsin : Real.sin (4 * T / (n : ℝ)) =
      2 * Real.sin (2 * T / (n : ℝ)) * Real.cos (2 * T / (n : ℝ)) := by
    rw [show 4 * T / (n : ℝ) = 2 * (2 * T / (n : ℝ)) by ring, Real.sin_two_mul]
  rw [hsin]
  ring

theorem avgContCoeff_weight_two {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T ≠ 0)
    {S : Finset (Fin n)} (hS : S.card = 2) :
    avgContCoeff n T S = 1 / 2 + Real.sin (4 * T / n) / (8 * T / n) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp only [avgContCoeff, hS, contCoeffByWeight]
  rw [integral_cos_sq_scaled_eq10 hn T]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hT4 : (4 : ℝ) * T ≠ 0 := by
    intro h
    exact hT (by linarith [h])
  field_simp

lemma sin_ge_neg_div_pi {x : ℝ} (hx : 0 < x) : -x / Real.pi ≤ Real.sin x := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases lt_or_ge x Real.pi with h | h
  · have hpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx h
    have hneg : -x / Real.pi < 0 := by
      rw [neg_div]
      have hxπ : 0 < x / Real.pi := div_pos hx hp
      linarith
    linarith
  · have hsin : -1 ≤ Real.sin x := Real.neg_one_le_sin x
    have hxπ : 1 ≤ x / Real.pi := (one_le_div hp).mpr (by linarith)
    have hle : -x / Real.pi ≤ -1 := by
      rw [neg_div]
      linarith
    linarith

lemma half_add_sin_div_lower {x : ℝ} (hx : 0 < x) :
    1 / 2 - 1 / (2 * Real.pi) ≤ 1 / 2 + Real.sin x / (2 * x) := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx2 : 0 < 2 * x := by linarith
  have hsin := sin_ge_neg_div_pi hx
  have h1 : (-x / Real.pi) / (2 * x) ≤ Real.sin x / (2 * x) :=
    div_le_div_of_nonneg_right hsin hx2.le
  have h2 : (-x / Real.pi) / (2 * x) = -(1 / (2 * Real.pi)) := by
    rw [neg_div]
    field_simp
  have h3 : -(1 / (2 * Real.pi)) ≤ Real.sin x / (2 * x) := h2 ▸ h1
  calc
    1 / 2 - 1 / (2 * Real.pi) = 1 / 2 + -(1 / (2 * Real.pi)) := by ring
    _ ≤ 1 / 2 + Real.sin x / (2 * x) := by linarith [h3]

theorem avgContCoeff_weight_two_lower {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    {S : Finset (Fin n)} (hS : S.card = 2) :
    1 / 2 - 1 / (2 * Real.pi) ≤ avgContCoeff n T S := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [avgContCoeff_weight_two hn hT.ne' hS]
  have hx : 0 < 4 * T / (n : ℝ) := by positivity
  have hbase := half_add_sin_div_lower hx
  have heq : Real.sin (4 * T / (n : ℝ)) / (8 * T / (n : ℝ)) =
      Real.sin (4 * T / (n : ℝ)) / (2 * (4 * T / (n : ℝ))) := by
    congr 2
    ring
  rw [heq]
  linarith

theorem fourierCoeff_avgContDist {n : ℕ} (T : ℝ) (S : Finset (Fin n)) :
    fourierCoeff (avgContDist n T) S = avgContCoeff n T S := by
  classical
  have hcont : ∀ x : Cube n, Continuous fun t : ℝ => contDist n t x := by
    intro x
    unfold contDist contCoeffByWeight
    fun_prop
  simp only [fourierCoeff, avgContCoeff, avgContDist]
  have hstep1 : ∀ x : Cube n,
      (1 / T * ∫ t in (0 : ℝ)..T, contDist n t x) * chi S x =
        (1 / T) * ∫ t in (0 : ℝ)..T, contDist n t x * chi S x := by
    intro x
    rw [intervalIntegral.integral_mul_const]
    ring
  simp only [hstep1]
  rw [← Finset.mul_sum]
  congr 1
  have hInt : ∀ x ∈ (Finset.univ : Finset (Cube n)),
      IntervalIntegrable (fun t : ℝ => contDist n t x * chi S x) MeasureTheory.volume 0 T :=
    fun x _ => (hcont x).mul_const (chi S x) |>.intervalIntegrable 0 T
  have hswap : (∑ x : Cube n, ∫ t in (0 : ℝ)..T, contDist n t x * chi S x)
      = ∫ t in (0 : ℝ)..T, ∑ x : Cube n, contDist n t x * chi S x := by
    have h := intervalIntegral.integral_finsetSum
      (a := (0 : ℝ)) (b := T) (s := (Finset.univ : Finset (Cube n)))
      (f := fun x (t : ℝ) => contDist n t x * chi S x) hInt
    simpa using h.symm
  rw [hswap]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simpa only [fourierCoeff] using!
    fourierCoeff_synthesis (fun R => contCoeffByWeight n t R.card) S

theorem no_average_mixing_time_continuous :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ), 2 ≤ n → ∀ T : ℝ, 0 < T →
      ε ≤ tvDist (avgContDist n T) := by
  refine ⟨1 / 4 - 1 / (4 * Real.pi), ?_, ?_⟩
  · have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hden : (0 : ℝ) < 4 * Real.pi := by positivity
    have hsmall : 1 / (4 * Real.pi) < 1 / 4 := by
      rw [div_lt_iff₀ hden]
      nlinarith
    linarith
  · intro n hn T hT
    have hn0 : 0 < n := by omega
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    let S : Finset (Fin n) := {a, b}
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      simp [a, b] at hv
    have hScard : S.card = 2 := by simp [S, hab]
    have hSn : S.Nonempty := by
      rw [← Finset.card_pos, hScard]
      norm_num
    have hcoeff : 1 / 2 - 1 / (2 * Real.pi) ≤ avgContCoeff n T S :=
      avgContCoeff_weight_two_lower hn0 hT hScard
    have hf : fourierCoeff (avgContDist n T) S = avgContCoeff n T S :=
      fourierCoeff_avgContDist T S
    have htv := abs_fourierCoeff_le_two_tv (avgContDist n T) hSn
    rw [hf] at htv
    have hpos : 0 < avgContCoeff n T S := by
      have hpi1 : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      have hden : (0 : ℝ) < 2 * Real.pi := by positivity
      have hA : 1 / (2 * Real.pi) < 1 / 2 := by
        rw [div_lt_iff₀ hden]
        nlinarith
      linarith
    rw [abs_of_pos hpos] at htv
    have hhalf : 1 / 4 - 1 / (4 * Real.pi) = (1 / 2 - 1 / (2 * Real.pi)) / 2 := by
      ring
    rw [hhalf]
    linarith

end Qatlib.Papers.HypercubeWalk01.MainResults
