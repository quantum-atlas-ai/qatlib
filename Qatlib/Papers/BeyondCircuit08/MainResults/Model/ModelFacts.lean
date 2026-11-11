/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

/-!
# Fibonacci coefficients and the four-strand block

The coefficient identities establish the unit norms and root-of-unity relations of `fibA`,
together with the quadratic relation for `goldenTau`. The explicit strings `starStarStrA` and
`starStarStrB` define the two distinct basis elements of `StarStarBasis 4`.

The remaining identities compute the entries of the first two four-strand generators in this
basis, giving the concrete matrices used in the density development of [Jordan2008].

## Main statements

* `card_starStarBasis_four`: the four-strand star-star sector has two basis elements.
* `starStarGen_four_zero_A` and `starStarGen_four_zero_B`: the first generator has diagonal
  entries `fibb` and `fiba`, with zero off-diagonal entries.
* `starStarGen_four_one_A` and related entry identities: the second generator has diagonal
  entries `fibc`, `fibe` and off-diagonal entries `fibd`.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- The Fibonacci phase `fibA` has norm one. -/
theorem fibA_norm : ‖fibA‖ = 1 := by
  simp [fibA, Complex.norm_exp]

/-- The Fibonacci phase `fibA` is nonzero. -/
theorem fibA_ne_zero : fibA ≠ 0 := by
  intro h0
  have h := fibA_norm
  rw [h0, norm_zero] at h
  norm_num at h

/-- The fifth power of `fibA` is minus one. -/
theorem fibA_pow_five : fibA ^ 5 = -1 := by
  unfold fibA
  rw [← Complex.exp_nat_mul]
  have hz : (5 : ℕ) * ((-(3 * Real.pi / 5) : ℝ) * Complex.I) =
      (3 : ℕ) * (-(Real.pi * Complex.I)) := by
    push_cast; ring
  rw [hz, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The tenth power of `fibA` is one. -/
theorem fibA_pow_ten : fibA ^ 10 = 1 := by
  calc fibA ^ 10 = (fibA ^ 5) ^ 2 := by ring
    _ = 1 := by rw [fibA_pow_five]; norm_num

/-- The coefficient `fiba` has norm one. -/
theorem fiba_norm : ‖fiba‖ = 1 := by
  unfold fiba
  rw [norm_neg, Complex.norm_pow, fibA_norm]
  norm_num

/-- The coefficient `fibb` has norm one. -/
theorem fibb_norm : ‖fibb‖ = 1 := by
  unfold fibb
  rw [Complex.norm_pow, fibA_norm]
  norm_num

/-- The reciprocal golden ratio `goldenTau` is positive. -/
theorem goldenTau_pos : 0 < goldenTau := by
  unfold goldenTau; positivity

/-- The reciprocal golden ratio `goldenTau` is strictly less than one. -/
theorem goldenTau_lt_one : goldenTau < 1 := by
  unfold goldenTau
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by positivity
  rw [div_lt_one hpos]
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  linarith

/-- The reciprocal golden ratio satisfies `goldenTau ^ 2 = 1 - goldenTau`. -/
theorem goldenTau_sq : goldenTau ^ 2 = 1 - goldenTau := by
  unfold goldenTau
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

/-- The five-symbol string with stars at indices zero, two, and four. -/
def starStarStrA : Fin 5 → Symbol := ![true, false, true, false, true]

/-- The five-symbol string with stars only at indices zero and four. -/
def starStarStrB : Fin 5 → Symbol := ![true, false, false, false, true]

/-- The string `starStarStrA` has no adjacent stars. -/
theorem starStarStrA_adj : hasAdjacentStar starStarStrA = false := by decide

/-- The string `starStarStrB` has no adjacent stars. -/
theorem starStarStrB_adj : hasAdjacentStar starStarStrB = false := by decide

/-- The two endpoint symbols of `starStarStrA` are stars. -/
theorem starStarStrA_ss : IsStarStar (n := 4) starStarStrA := by decide

/-- The two endpoint symbols of `starStarStrB` are stars. -/
theorem starStarStrB_ss : IsStarStar (n := 4) starStarStrB := by decide

/-- The basis element of `StarStarBasis 4` represented by `starStarStrA`. -/
def starStarElA : StarStarBasis 4 := ⟨⟨starStarStrA, starStarStrA_adj⟩, starStarStrA_ss⟩

/-- The basis element of `StarStarBasis 4` represented by `starStarStrB`. -/
def starStarElB : StarStarBasis 4 := ⟨⟨starStarStrB, starStarStrB_adj⟩, starStarStrB_ss⟩

/-- The four-strand star-star basis has exactly two elements. -/
theorem card_starStarBasis_four : Fintype.card (StarStarBasis 4) = 2 := by decide

/-- The two explicitly constructed elements `starStarElA` and `starStarElB` are distinct. -/
theorem starStarElA_ne_starStarElB : starStarElA ≠ starStarElB := by decide

/-- The first four-strand generator has entry `fibb` at the diagonal position indexed by
`starStarElA` [Jordan2008]. -/
theorem starStarGen_four_zero_A :
    starStarGen 4 0 starStarElA starStarElA = fibb := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA,
    starStarStrA, starStarStrB, Subtype.coe_mk]

/-- The first four-strand generator has entry `fiba` at the diagonal position indexed by
`starStarElB`. -/
theorem starStarGen_four_zero_B :
    starStarGen 4 0 starStarElB starStarElB = fiba := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

/-- The two off-diagonal entries of the first four-strand generator in the explicit star-star
basis are zero. -/
theorem starStarGen_four_zero_offdiag :
    starStarGen 4 0 starStarElA starStarElB = 0 ∧
      starStarGen 4 0 starStarElB starStarElA = 0 := by
  constructor <;>
    simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
      starStarStrA, starStarStrB, Subtype.coe_mk]

/-- Updating the middle symbol of `starStarStrB` to a star gives `starStarStrA`. -/
private lemma starStarStrA_eq_update :
    (starStarStrA : Fin 5 → Symbol) = Function.update starStarStrB 2 true := by
  decide

/-- Updating the middle symbol of `starStarStrA` to a nonstar gives `starStarStrB`. -/
private lemma starStarStrB_eq_update :
    (starStarStrB : Fin 5 → Symbol) = Function.update starStarStrA 2 false := by
  decide

/-- The second four-strand generator has entry `fibc` at the diagonal position indexed by
`starStarElA`. -/
theorem starStarGen_four_one_A :
    starStarGen 4 1 starStarElA starStarElA = fibc := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

/-- The second four-strand generator has entry `fibe` at the diagonal position indexed by
`starStarElB`. -/
theorem starStarGen_four_one_B :
    starStarGen 4 1 starStarElB starStarElB = fibe := by
  simp [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]

/-- The second four-strand generator has entry `fibd` in row `starStarElA` and column
`starStarElB` [Jordan2008]. -/
theorem starStarGen_four_one_A_B :
    starStarGen 4 1 starStarElA starStarElB = fibd := by
  simp only [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]
  norm_num
  intro h
  exact absurd starStarStrA_eq_update h

/-- The second four-strand generator has entry `fibd` in row `starStarElB` and column
`starStarElA`. -/
theorem starStarGen_four_one_B_A :
    starStarGen 4 1 starStarElB starStarElA = fibd := by
  simp only [starStarGen, blockGen, fibRepEntry, starStarElA, starStarElB,
    starStarStrA, starStarStrB, Subtype.coe_mk]
  norm_num
  intro h
  exact absurd starStarStrB_eq_update h

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
