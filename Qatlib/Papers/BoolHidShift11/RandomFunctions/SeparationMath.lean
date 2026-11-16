/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier.SourceInfluenceFourier
public import Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalMath

@[expose] public section


/-! # Preserved complete legacy mathematical components

These definitions and conditional estimates retain their complete original
mathematics. Free success/query fields are not an oracle algorithm; scalar
amplification estimates are not a repetition or termination proof.
-/
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open scoped BigOperators ENNReal
namespace Qatlib.Papers.BoolHidShift11.RandomFunctions.SeparationMath
open Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalMath

/-- A quadratic query lower bound implies the corresponding square-root bound. -/
theorem sqrtQueries {n t : ℕ}
    (h : (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2) :
    Real.sqrt (((2 : ℝ) ^ n - 2) / 3) ≤ (t : ℝ) := by
  rw [Real.sqrt_le_iff]
  exact ⟨Nat.cast_nonneg t, by linarith⟩

/-! ### Exponential versus linear -/

/-- `6·(4n)² < 2ⁿ` for `n ≥ 16`; exponential growth eventually dominates any
linear function, the quantitative form of the `Ω(2^{n/2})` versus `O(n)`
separation. -/
theorem expGrowth : ∀ n : ℕ, 16 ≤ n → 6 * (4 * (n : ℝ)) ^ 2 < (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    by_cases h16 : 16 ≤ k
    · have hstep := ih h16
      have hk' : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h16
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
        rw [pow_succ]
        ring
      rw [hpow]
      push_cast
      nlinarith
    · have hk15 : k = 15 := by omega
      subst hk15
      norm_num

/-- The resulting separation of query counts: `4n < √(2^n/6)` for `n ≥ 16`. -/
theorem expSeparation {n : ℕ} (hn : 16 ≤ n) :
    4 * (n : ℝ) < Real.sqrt ((2 : ℝ) ^ n / 6) := by
  have h := expGrowth n hn
  have hpos : (0 : ℝ) < 4 * (n : ℝ) := by positivity
  have hsq : (4 * (n : ℝ)) ^ 2 < (2 : ℝ) ^ n / 6 := by nlinarith
  calc
    4 * (n : ℝ) = Real.sqrt ((4 * (n : ℝ)) ^ 2) := by rw [Real.sqrt_sq hpos.le]
    _ < Real.sqrt ((2 : ℝ) ^ n / 6) := Real.sqrt_lt_sqrt (by positivity) hsq

/-- `√(2^n/6) ≤ √((2^n - 2)/3)`, i.e. the constant `1/6` only loses a factor
of `2` relative to Lemma 2's denominator. -/
theorem sqrtComparison {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt ((2 : ℝ) ^ n / 6) ≤ Real.sqrt (((2 : ℝ) ^ n - 2) / 3) := by
  apply Real.sqrt_le_sqrt
  have hp : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at this ⊢
    linarith
  linarith

/-- **Classical side of Theorem 2**: any classical algorithm that solves a
uniformly random BHSP instance with probability at least `1/2` makes more than
`4n` oracle queries once `n ≥ 16`. This is Lemma 2 plus the exponential/linear
comparison. -/
theorem exceedLinear {n t : ℕ} (hn : 16 ≤ n)
    (h : (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2) : 4 * (n : ℝ) < (t : ℝ) := by
  have h1 := sqrtQueries h
  have h2 := expSeparation hn
  have h3 := sqrtComparison (by omega : 2 ≤ n)
  linarith

/-! ### The quantum side and the separation -/

/-- A legacy free success/query record, without oracle execution semantics. -/
structure FreeAlgorithm where
  /-- Success probability over the uniform distribution on `(f, v)`. -/
  successProb : ℝ
  /-- Number of oracle queries on instances of dimension `n`. -/
  queryCount : ℕ → ℝ
  /-- Bounded error, the paper's "with bounded error". -/
  success_ge : (2 / 3 : ℝ) ≤ successProb
  /-- Query counts are nonnegative. -/
  query_nonneg : ∀ n : ℕ, 0 ≤ queryCount n

/-- Conditional cost arithmetic for the literal free record and the supplied counting bound. -/
theorem costComparison (alg : FreeAlgorithm) {C : ℝ}
    (hq : ∀ n : ℕ, alg.queryCount n ≤ C * (n : ℝ)) (hC4 : C ≤ 4) :
    ∀ (n t : ℕ), 16 ≤ n → (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2 →
      alg.queryCount n < (t : ℝ) := by
  intro n t hn hcl
  have h1 : alg.queryCount n ≤ C * (n : ℝ) := hq n
  have h2 : 4 * (n : ℝ) < (t : ℝ) := exceedLinear hn hcl
  have h3 : C * (n : ℝ) ≤ 4 * (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  linarith


end Qatlib.Papers.BoolHidShift11.RandomFunctions.SeparationMath
