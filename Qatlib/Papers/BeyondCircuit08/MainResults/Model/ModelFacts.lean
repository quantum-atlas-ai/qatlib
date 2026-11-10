/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

theorem fibA_norm : ‖fibA‖ = 1 := by
  simp [fibA, Complex.norm_exp]

theorem fibA_ne_zero : fibA ≠ 0 := by
  intro h0
  have h := fibA_norm
  rw [h0, norm_zero] at h
  norm_num at h

theorem fibA_pow_five : fibA ^ 5 = -1 := by
  unfold fibA
  rw [← Complex.exp_nat_mul]
  have hz : (5 : ℕ) * ((-(3 * Real.pi / 5) : ℝ) * Complex.I) =
      (3 : ℕ) * (-(Real.pi * Complex.I)) := by
    push_cast; ring
  rw [hz, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem fibA_pow_ten : fibA ^ 10 = 1 := by
  calc fibA ^ 10 = (fibA ^ 5) ^ 2 := by ring
    _ = 1 := by rw [fibA_pow_five]; norm_num

theorem fiba_norm : ‖fiba‖ = 1 := by
  unfold fiba
  rw [norm_neg, Complex.norm_pow, fibA_norm]
  norm_num

theorem fibb_norm : ‖fibb‖ = 1 := by
  unfold fibb
  rw [Complex.norm_pow, fibA_norm]
  norm_num

theorem goldenTau_pos : 0 < goldenTau := by
  unfold goldenTau; positivity

theorem goldenTau_lt_one : goldenTau < 1 := by
  unfold goldenTau
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by positivity
  rw [div_lt_one hpos]
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  linarith

theorem goldenTau_sq : goldenTau ^ 2 = 1 - goldenTau := by
  unfold goldenTau
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

def starStarStrA : Fin 5 → Symbol := ![true, false, true, false, true]

def starStarStrB : Fin 5 → Symbol := ![true, false, false, false, true]

theorem starStarStrA_adj : hasAdjacentStar starStarStrA = false := by decide

theorem starStarStrB_adj : hasAdjacentStar starStarStrB = false := by decide

theorem starStarStrA_ss : IsStarStar (n := 4) starStarStrA := by decide

theorem starStarStrB_ss : IsStarStar (n := 4) starStarStrB := by decide

def starStarElA : StarStarBasis 4 := ⟨⟨starStarStrA, starStarStrA_adj⟩, starStarStrA_ss⟩

def starStarElB : StarStarBasis 4 := ⟨⟨starStarStrB, starStarStrB_adj⟩, starStarStrB_ss⟩

theorem card_starStarBasis_four : Fintype.card (StarStarBasis 4) = 2 := by decide

theorem starStarElA_ne_starStarElB : starStarElA ≠ starStarElB := by decide

theorem starStarGen_four_zero_A :
    starStarGen 4 0 starStarElA starStarElA = fibb := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA,
    starStarStrA, starStarStrB, Subtype.coe_mk]

theorem starStarGen_four_zero_B :
    starStarGen 4 0 starStarElB starStarElB = fiba := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

theorem starStarGen_four_zero_offdiag :
    starStarGen 4 0 starStarElA starStarElB = 0 ∧
      starStarGen 4 0 starStarElB starStarElA = 0 := by
  constructor <;>
    simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
      starStarStrA, starStarStrB, Subtype.coe_mk]

private lemma starStarStrA_eq_update :
    (starStarStrA : Fin 5 → Symbol) = Function.update starStarStrB 2 true := by
  decide

private lemma starStarStrB_eq_update :
    (starStarStrB : Fin 5 → Symbol) = Function.update starStarStrA 2 false := by
  decide

theorem starStarGen_four_one_A :
    starStarGen 4 1 starStarElA starStarElA = fibc := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

theorem starStarGen_four_one_B :
    starStarGen 4 1 starStarElB starStarElB = fibe := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

theorem starStarGen_four_one_A_B :
    starStarGen 4 1 starStarElA starStarElB = fibd := by
  simp only [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]
  norm_num
  intro h
  exact absurd starStarStrA_eq_update h

theorem starStarGen_four_one_B_A :
    starStarGen 4 1 starStarElB starStarElA = fibd := by
  simp only [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]
  norm_num
  intro h
  exact absurd starStarStrB_eq_update h

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
