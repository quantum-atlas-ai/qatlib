/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An explicit cubic product-formula error family

This module constructs a symmetric three-exponential word from the Pauli `Z` and `X` generators.
It matches the ideal exponential through degree two and computes a nonzero cubic deviation,
giving a concrete example for the product-formula error analysis of [ChildsEtAl2021Trotter].

Within `radius = 1 / (24 * exp 1)`, the actual operator-norm error lies between `|t| ^ 3 / 6`
and `3 * |t| ^ 3`. The execution and target are unitary, the bounds extend under real generator
scaling, and `not_fourth_order` excludes any local bound of the form `K * t ^ 4`.

## Main statements

* `cubic`: identifies the cubic coefficient deviation.
* `frontier1`: gives two-sided cubic bounds on the actual error.
* `execution_unitary`: proves unitarity of the executed and ideal operators.
* `family_bounds`: gives the scaled cubic bounds.
* `not_fourth_order`: rules out a fourth-power local error bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-- The type of complex two-by-two matrices used in the explicit lower-bound family. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli `Z` matrix `diag(1, -1)`. -/
def hZ : Mat := !![1, 0; 0, -1]
/-- The Pauli `X` matrix with zero diagonal and unit off-diagonal entries. -/
def hX : Mat := !![0, 1; 1, 0]
/-- The skew-Hermitian generator obtained by multiplying `hZ` by the imaginary unit. -/
def genZ : Mat := Complex.I • hZ
/-- The skew-Hermitian generator obtained by multiplying `hX` by the imaginary unit. -/
def genX : Mat := Complex.I • hX
/-- The symmetric three-generator word consisting of half of `genZ`, then `genX`, then half of
`genZ`. -/
def word : List Mat := [(1/2 : ℝ) • genZ, genX, (1/2 : ℝ) • genZ]
/-- The sum of the two skew-Hermitian generators. -/
def total : Mat := genZ + genX

/-- The explicit cubic deviation matrix with diagonal entries `-i / 3`, `i / 3` and off-diagonal
entries `i / 6`. -/
def leading : Mat := !![-Complex.I / 3, Complex.I / 6; Complex.I / 6, Complex.I / 3]

/-- The matrix `hZ` is Hermitian. -/
theorem hermitian_hZ : hZᴴ = hZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hZ, Matrix.conjTranspose_apply]

/-- The matrix `hX` is Hermitian. -/
theorem hermitian_hX : hXᴴ = hX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hX, Matrix.conjTranspose_apply]

/-- The matrices `hZ` and `hX` do not commute. -/
theorem noncommuting : hZ * hX ≠ hX * hZ := by
  intro h
  have := congrArg (fun M : Mat => M 0 1) h
  norm_num [hZ, hX, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- The symmetric word matches the exponential coefficients of `total` through degree two. -/
theorem coefficients (n : ℕ) (hn : n ≤ 2) :
    suzukiSeries word n = ((n.factorial : ℝ)⁻¹) • total ^ n := by
  interval_cases n <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [word, total, genZ, genX, hZ, hX, suzukiSeries,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, Matrix.one_apply, Matrix.smul_apply, Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three]

/-- The cubic coefficient deviation of the symmetric word equals `leading`. -/
theorem cubic : suzukiSeries word 3 - ((3 : ℕ).factorial : ℝ)⁻¹ • total ^ 3 = leading := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [word, total, leading, genZ, genX, hZ, hX, suzukiSeries,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, Matrix.one_apply, Matrix.smul_apply, Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three] <;> ring

/-- Both skew-Hermitian generators have operator norm at most one. -/
theorem gen_norms : ‖genZ‖ ≤ 1 ∧ ‖genX‖ ≤ 1 := by
  constructor
  · apply l2_norm_unitary_le_one
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [genZ, hZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, star_smul, Complex.I_mul_I]
  · apply l2_norm_unitary_le_one
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [genX, hX, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, star_smul, Complex.I_mul_I]

/-- The word mass and the norm of the total generator are at most two. -/
theorem masses : suzukiMass word ≤ 2 ∧ ‖total‖ ≤ 2 := by
  obtain ⟨hz, hx⟩ := gen_norms
  constructor
  · simp only [word, suzukiMass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  · exact (norm_add_le _ _).trans (by linarith)

/-- The norm of each matrix entry is bounded by the operator norm. -/
theorem entry_norm_le (A : Mat) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi :=
      PiLp.norm_apply_le (toEuclidean_fromVec (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i
  have he : (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = A i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  change ‖(A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i‖ ≤ ‖toEuclidean_fromVec
      (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- The cubic deviation matrix has norm at least one third. -/
theorem leading_lower : (1/3 : ℝ) ≤ ‖leading‖ := by
  have h := entry_norm_le leading 0 0
  norm_num [leading, norm_div] at h
  exact h

/-- The difference between the symmetric exponential word and the exponential of the total
generator. -/
def error (t : ℝ) : Mat := suzukiExponentialWord word t - NormedSpace.exp (t • total)
/-- The error remaining after subtracting the cubic leading term from `error`. -/
def remainder (t : ℝ) : Mat := error t - t ^ 3 • leading

/-- The difference of the two Taylor truncations through degree three equals `t ^ 3 • leading`. -/
theorem truncation_difference (t : ℝ) :
    (∑ n ∈ Finset.range 4, t ^ n • suzukiSeries word n) -
      (∑ n ∈ Finset.range 4, t ^ n • suzukiSeries [total] n) = t ^ 3 • leading := by
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub, suzukiSeries_singleton]
  have h0 : suzukiSeries word 0 - ((0 : ℕ).factorial : ℝ)⁻¹ • total^0 = 0 :=
    sub_eq_zero.mpr (coefficients 0 (by omega))
  have h1 : suzukiSeries word 1 - ((1 : ℕ).factorial : ℝ)⁻¹ • total^1 = 0 :=
    sub_eq_zero.mpr (coefficients 1 (by omega))
  have h2 : suzukiSeries word 2 - ((2 : ℕ).factorial : ℝ)⁻¹ • total^2 = 0 :=
    sub_eq_zero.mpr (coefficients 2 (by omega))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, cubic,
    smul_zero, zero_add, add_zero]

/-- The cubic deviation matrix has norm at most eight thirds. -/
theorem leading_upper : ‖leading‖ ≤ (8/3 : ℝ) := by
  rw [← cubic]
  have hw := suzukiSeries_norm_le word 3
  have hh := suzukiSeries_norm_le [total] 3
  rw [suzukiSeries_singleton] at hh
  have hm := masses
  have hp : 0 ≤ suzukiMass word := general_trotter_mass_nonneg word
  have hw' : suzukiMass word ^ 3 ≤ 2 ^ 3 := by gcongr; exact hm.1
  have hh' : ‖total‖ ^ 3 ≤ 2 ^ 3 := by gcongr; exact hm.2
  have hs : suzukiMass [total] = ‖total‖ := by simp [suzukiMass]
  rw [hs] at hh
  have ht := norm_sub_le (suzukiSeries word 3) (((3 : ℕ).factorial : ℝ)⁻¹ • total ^ 3)
  norm_num [Nat.factorial] at hw hh
  linarith

/-- A word of mass at most two has Taylor tail after degree three bounded by `2 * exp 1 * |t| ^
4` when `|t| ≤ 1 / 2`. -/
theorem tail_bound (xs : List Mat) (hm : suzukiMass xs ≤ 2)
    (t : ℝ) (ht : |t| ≤ 1/2) :
    ‖suzukiExponentialWord xs t - ∑ n ∈ Finset.range 4, t ^ n • suzukiSeries xs n‖ ≤
      2 * Real.exp 1 * |t| ^ 4 := by
  have h := general_trotter_taylor_tail xs t 4
  have hmass := general_trotter_mass_nonneg xs
  have ha : |t| * suzukiMass xs ≤ 1 := by nlinarith [abs_nonneg t]
  have he : Real.exp (|t| * suzukiMass xs) ≤ Real.exp 1 := Real.exp_le_exp.mpr ha
  have hp : (|t| * suzukiMass xs)^4 ≤ (|t| * 2)^4 := by
    gcongr
  have hb : Real.exp (|t| * suzukiMass xs) * (|t| * suzukiMass xs)^4 ≤
      Real.exp 1 * (|t| * 2)^4 := mul_le_mul he hp (by positivity) (by positivity)
  norm_num [Nat.factorial] at h
  have hn : 0 ≤ Real.exp 1 * |t|^4 := by positivity
  nlinarith

/-- The remainder after the cubic leading term is bounded by `4 * exp 1 * |t| ^ 4` when `|t| ≤ 1
/ 2`. -/
theorem remainder_bound (t : ℝ) (ht : |t| ≤ 1/2) :
    ‖remainder t‖ ≤ 4 * Real.exp 1 * |t|^4 := by
  have hx := tail_bound word masses.1 t ht
  have hh := tail_bound [total] (by simpa [suzukiMass] using! masses.2) t ht
  have he : suzukiExponentialWord [total] t = NormedSpace.exp (t • total) := by
    simp [suzukiExponentialWord]
  rw [he] at hh
  have hid : remainder t =
      (suzukiExponentialWord word t - ∑ n ∈ Finset.range 4, t^n • suzukiSeries word n) -
      (NormedSpace.exp (t • total) - ∑ n ∈ Finset.range 4, t^n • suzukiSeries [total] n) := by
    have h := truncation_difference t
    dsimp [remainder, error]
    rw [← h]
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The explicit radius `1 / (24 * exp 1)` for the cubic error estimates. -/
def radius : ℝ := 1 / (24 * Real.exp 1)

/-- The error-estimate radius is positive. -/
theorem radius_pos : 0 < radius := by unfold radius; positivity

/-- The error-estimate radius is at most one half. -/
theorem radius_le_half : radius ≤ 1/2 := by
  have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
  unfold radius
  apply (div_le_iff₀ (by positivity : 0 < 24 * Real.exp 1)).mpr
  linarith

/-- Within `radius`, the remainder norm is at most `|t| ^ 3 / 6`. -/
theorem remainder_small (t : ℝ) (ht : |t| ≤ radius) :
    ‖remainder t‖ ≤ (1/6 : ℝ) * |t|^3 := by
  have hb := remainder_bound t (ht.trans radius_le_half)
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have ht' : 24 * Real.exp 1 * |t| ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 24 * Real.exp 1)).mp ht
    nlinarith
  have hp := mul_le_mul_of_nonneg_right ht' (pow_nonneg (abs_nonneg t) 3)
  nlinarith [pow_nonneg (abs_nonneg t) 3]

/-- Within `radius`, the remainder norm is at most half the norm of the cubic leading term. -/
theorem remainder_half_leading (t : ℝ) (ht : |t| ≤ radius) :
    ‖remainder t‖ ≤ (1/2 : ℝ) * ‖t^3 • leading‖ := by
  have hb := remainder_small t ht
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  have h := mul_le_mul_of_nonneg_left leading_lower (pow_nonneg (abs_nonneg t) 3)
  linarith

/-- Within `radius`, the actual error norm lies between `|t| ^ 3 / 6` and `3 * |t| ^ 3`. -/
theorem frontier1 (t : ℝ) (ht : |t| ≤ radius) :
    (1/6 : ℝ) * |t|^3 ≤ ‖error t‖ ∧ ‖error t‖ ≤ 3 * |t|^3 := by
  have hr := remainder_small t ht
  have hlow := leading_lower
  have hupp := leading_upper
  have hn : ‖t^3 • leading‖ = |t|^3 * ‖leading‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
  have hl := norm_sub_norm_le (t^3 • leading) (error t)
  rw [norm_sub_rev] at hl
  change ‖t^3 • leading‖ - ‖error t‖ ≤ ‖remainder t‖ at hl
  have hu := norm_sub_le (error t - t^3 • leading) (-(t^3 • leading))
  have heq : error t - t^3 • leading - -(t^3 • leading) = error t := by abel
  rw [heq, norm_neg, hn] at hu
  change ‖error t‖ ≤ ‖remainder t‖ + |t|^3 * ‖leading‖ at hu
  rw [hn] at hl
  have hp : 0 ≤ |t|^3 := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow hp]
  · nlinarith [mul_le_mul_of_nonneg_left hupp hp]

/-- The error equals the explicit symmetric product of the three generator exponentials minus
the ideal exponential. -/
theorem actual_execution (t : ℝ) : error t =
    NormedSpace.exp ((t/2) • genZ) * NormedSpace.exp (t • genX) *
      NormedSpace.exp ((t/2) • genZ) - NormedSpace.exp (t • total) := by
  simp [error, word, suzukiExponentialWord, smul_smul, div_eq_mul_inv, mul_assoc]

/-- The generators `genZ` and `genX` are skew-Hermitian. -/
theorem generators_skew : genZᴴ = -genZ ∧ genXᴴ = -genX := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [genZ, genX, hZ, hX, Matrix.conjTranspose_apply]

/-- Both the symmetric exponential word and the ideal exponential are unitary for every real
time. -/
theorem execution_unitary (t : ℝ) :
    suzukiExponentialWord word t ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      NormedSpace.exp (t • total) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hz := generators_skew.1
  have hx := generators_skew.2
  have hs : ((1/2 : ℝ) • genZ)ᴴ = -((1/2 : ℝ) • genZ) := by
    simp [Matrix.conjTranspose_smul, hz]
  constructor
  · apply (Matrix.unitaryGroup (Fin 2) ℂ).list_prod_mem
    intro U hU
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hU
    apply general_trotter_exp_unitary
    simp only [word, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl
    · exact hs
    · exact hx
    · exact hs
  · apply general_trotter_exp_unitary
    simp [total, Matrix.conjTranspose_add, hz, hx, add_comm]

/-- The product-formula error after scaling every generator and the total generator by the real
scalar `a`. -/
def scaledError (a t : ℝ) : Mat :=
  suzukiExponentialWord (word.map (fun X => a • X)) t -
    NormedSpace.exp (t • (a • total))

/-- Scaling the generators by `a` is equivalent to replacing time by `a * t` in the error. -/
theorem scaled_execution (a t : ℝ) : scaledError a t = error (a*t) := by
  simp [scaledError, error, suzukiExponentialWord, List.map_map, Function.comp_def, smul_smul,
      mul_comm]

/-- When `|a * t| ≤ radius`, the scaled error norm lies between `|a| ^ 3 * |t| ^ 3 / 6` and `3 *
|a| ^ 3 * |t| ^ 3`. -/
theorem family_bounds (a t : ℝ) (ht : |a*t| ≤ radius) :
    (1/6 : ℝ) * |a|^3 * |t|^3 ≤ ‖scaledError a t‖ ∧
      ‖scaledError a t‖ ≤ 3 * |a|^3 * |t|^3 := by
  rw [scaled_execution]
  simpa only [abs_mul, mul_pow, mul_assoc] using! frontier1 (a*t) ht

/-- For every real `K` and positive `δ`, some `0 < t ≤ δ` has error norm greater than `K * t ^
4`. -/
theorem not_fourth_order (K δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ δ ∧ K*t^4 < ‖error t‖ := by
  let t := min (min radius δ) (1 / (12 * (|K| + 1)))
  have ht : 0 < t := lt_min (lt_min radius_pos hδ) (by positivity)
  have htr : t ≤ radius := (min_le_left _ _).trans (min_le_left _ _)
  have htd : t ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have htk : t ≤ 1 / (12 * (|K|+1)) := min_le_right _ _
  have hkpos : 0 < 12 * (|K|+1) := by positivity
  have hk := (le_div_iff₀ hkpos).mp htk
  have habs : |t| = t := abs_of_pos ht
  have hl := (frontier1 t (by rwa [habs])).1
  rw [habs] at hl
  have hKt : K*t < 1/6 := by
    have hle := mul_le_mul_of_nonneg_right (le_abs_self K) ht.le
    nlinarith [abs_nonneg K]
  refine ⟨t, ht, htd, ?_⟩
  have hprod := mul_lt_mul_of_pos_right hKt (pow_pos ht 3)
  nlinarith

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily
