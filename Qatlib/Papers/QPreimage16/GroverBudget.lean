/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch
import Qatlib.Foundations.ResourceBounds.LogBudgets

/-!
# Grover circuits and priced preimage-search budgets

This module instantiates prepared Grover search with the fiber `preimages f y` as its marked
set, in the preimage-search setting of [AmyEtAl2017]. It defines the phase oracle, iteration
count, and circuit, and proves circuit execution, normalization, resource counts, and success
bounds for permutation inputs or singleton fibers.

The results `program_budget_from_threshold` and `unique_preimage_budget` convert the logarithmic
threshold `n / 2 + v * log2 n ≤ C` into a bound of `2 ^ C` on the query count priced by `n ^ v`.

## Main statements

* `preimage_query_budget`: For positive width, the preimage circuit uses at most `(π / 4) * 2 ^
  ((n : ℝ) / 2)` queries. This is the Grover query estimate used in [Amy et al., Section
  2][AmyEtAl2017].
* `native_preimage_budget`: For a permutation on a positive-width register, the logarithmic
  budget hypothesis yields circuit unitarity, normalized output, success at least `1 - 1 / 2ⁿ`,
  and priced query count at most `2 ^ C`.
* `unique_preimage_budget`: For positive width and a singleton target fiber, the logarithmic
  budget hypothesis yields unitarity, normalized output, success at least `1 - 1 / 2ⁿ`, and
  priced query count at most `2 ^ C`. This realizes the overhead-adjusted budget discussed in
  [AmyEtAl2017].

## References

* [Amy et al., 2017][AmyEtAl2017]
-/

namespace Qatlib.Papers.QPreimage16.GroverBudget
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.ResourceBounds.LogBudgets

/-- The finite fiber of `y` under `f` on Boolean registers. -/
def preimages {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) : Finset (Reg n) :=
  Finset.univ.filter (fun x => f x = y)

/-- For a permutation of Boolean registers, the fiber of `y` is the singleton containing its
inverse image. -/
theorem preimages_eq_singleton {n : ℕ} (f : Reg n ≃ Reg n) (y : Reg n) :
    preimages f y = {f.symm y} := by
  ext x
  simp [preimages, Equiv.eq_symm_apply]

/-- The diagonal phase oracle that negates basis states in the fiber of `y` and fixes the
remaining basis states. -/
def preimagePhase {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if decide (x ∈ preimages f y) then -1 else 1)

/-- The Grover iteration count chosen using the search angle for one marked item among all
`n`-bit registers. -/
def iterations (n : ℕ) : ℕ :=
  groverIterations (knownCountAngle ((1 : ℝ) / Fintype.card (Reg n)))

/-- The prepared Grover circuit at the iteration count `iterations n`. -/
def program (n : ℕ) : Circuit (Reg n) := PreparedGroverCircuit n (iterations n)

/-- Running the preimage circuit from the zero basis state gives the Grover state for the fiber
of `y` at the chosen iteration count. -/
theorem run_program {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) :
    Run (preimagePhase f y) (program n) (Ket (ZeroStr n)) =
      GroverState (preimages f y) (iterations n) := by
  exact run_preparedGroverCircuit n (iterations n) (preimages f y)

/-- The preimage circuit makes exactly `iterations n` oracle queries. -/
theorem program_queries (n : ℕ) : QueryCount (program n) = iterations n :=
  queryCount_preparedGroverCircuit n (iterations n)

/-- The preimage circuit has exactly `iterations n + 1` counted gate macros. -/
theorem program_macros (n : ℕ) : GateCount (program n) = iterations n + 1 :=
  gateCount_preparedGroverCircuit n (iterations n)

/-- The prepared preimage-search circuit is unitary. -/
theorem program_unitary (n : ℕ) : IsUnitaryCircuit (program n) :=
  (preparedGroverAlgorithm n (iterations n)).unitary

/-- For positive width and a permutation input, measuring the output in the target fiber
succeeds with probability at least `1 - 1 / 2ⁿ`. -/
theorem preimage_success {n : ℕ} (hn : 0 < n) (f : Reg n ≃ Reg n) (y : Reg n) :
    1 - (1 : ℝ) / (2 : ℝ)^n ≤
      MeasureProb (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) (preimages f y) := by
  rw [run_program]
  have hN : 1 < Fintype.card (Reg n) := by
    rw [card_reg]
    have hh : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num only [pow_one] at hh
    omega
  have h := knownCount_success (I := Reg n) Fintype.card_pos (preimages f y)
    (m := 1) (by rw [preimages_eq_singleton]; simp) (by norm_num) hN
  simpa only [iterations, Nat.cast_one, card_reg, Nat.cast_pow, Nat.cast_ofNat] using h

/-- For positive width, the preimage circuit uses at most `(π / 4) * 2 ^ ((n : ℝ) / 2)` queries.
This is the Grover query estimate used in [Amy et al., Section 2][AmyEtAl2017]. -/
theorem preimage_query_budget {n : ℕ} (hn : 0 < n) :
    (QueryCount (program n) : ℝ) ≤ Real.pi/4 * (2 : ℝ)^((n : ℝ)/2) := by
  rw [program_queries]
  have hN : 1 < Fintype.card (Reg n) := by
    rw [card_reg]
    have hh : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num only [pow_one] at hh
    omega
  have h := knownCount_query_budget (I := Reg n) (m := 1) (by norm_num) hN
  simp only [Nat.cast_one, card_reg, Nat.cast_pow, Nat.cast_ofNat] at h
  have hs : Real.sqrt (1 / (2 : ℝ)^n) = 1 / (2 : ℝ)^((n : ℝ)/2) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1), Real.sqrt_one, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    congr 2; ring
  rw [hs] at h
  dsimp [iterations]
  simp only [card_reg, Nat.cast_pow, Nat.cast_ofNat]
  convert h using 1; field_simp

/-- The diagonal phase-oracle entry is minus one when `f x = y` and one otherwise. -/
theorem preimagePhase_diagonal {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) (x : Reg n) :
    preimagePhase f y x x = if f x = y then (-1 : ℂ) else 1 := by
  simp [preimagePhase, preimages]

/-- The output of the preimage-search circuit from the zero basis state is normalized. -/
theorem preimage_output_normalized {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) :
    Normalized (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) := by
  exact normalized_preparedGroverCircuit n (iterations n) (preimages f y)

/-- The circuit query count multiplied by the real-valued price factor `n ^ v`. -/
def pricedQueries (n : ℕ) (v : ℝ) : ℝ := (n : ℝ)^v * QueryCount (program n)

/-- For positive width, the threshold `n / 2 + v * log2 n ≤ C` implies a priced-query bound of
`2 ^ C`. -/
theorem program_budget_from_threshold {n : ℕ} (hn : 0 < n) (v C : ℝ)
    (hbudget : (n : ℝ)/2 + v*log2 n ≤ C) : pricedQueries n v ≤ (2 : ℝ)^C := by
  have hp : 0 ≤ (n : ℝ)^v := Real.rpow_nonneg (by positivity) _
  have hq := preimage_query_budget hn
  have hpi : Real.pi/4 ≤ 1 := by linarith [Real.pi_lt_d2]
  calc pricedQueries n v ≤ (n : ℝ)^v * (Real.pi/4 * (2 : ℝ)^((n : ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hq hp
    _ ≤ (n : ℝ)^v * (2 : ℝ)^((n : ℝ)/2) := by
        apply mul_le_mul_of_nonneg_left _ hp
        nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((n : ℝ)/2)]
    _ ≤ (2 : ℝ)^C := (exponential_budget_iff n hn v C).2 hbudget

/-- For a permutation on a positive-width register, the logarithmic budget hypothesis yields
circuit unitarity, normalized output, success at least `1 - 1 / 2ⁿ`, and priced query count
at most `2 ^ C`. -/
theorem native_preimage_budget {n : ℕ} (hn : 0 < n) (v C : ℝ)
    (hbudget : (n : ℝ)/2 + v*log2 n ≤ C) (f : Reg n ≃ Reg n) (y : Reg n) :
    IsUnitaryCircuit (program n) ∧
      Normalized (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) ∧
      1 - (1 : ℝ)/(2 : ℝ)^n ≤
        MeasureProb (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) (preimages f y) ∧
      pricedQueries n v ≤ (2 : ℝ)^C :=
  ⟨program_unitary n, preimage_output_normalized f y, preimage_success hn f y,
    program_budget_from_threshold hn v C hbudget⟩

/-- For positive width and a target fiber of cardinality one, the preimage circuit succeeds with
probability at least `1 - 1 / 2ⁿ`. This extends the permutation setting of [Amy et al.,
Section 2][AmyEtAl2017] to singleton fibers. -/
theorem unique_fiber_success {n m : ℕ} (hn : 0 < n) (f : Reg n → Reg m) (y : Reg m)
    (hunique : (preimages f y).card = 1) :
    1 - (1 : ℝ)/(2 : ℝ)^n ≤
      MeasureProb (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) (preimages f y) := by
  rw [run_program]
  have hN : 1 < Fintype.card (Reg n) := by
    rw [card_reg]
    have hh : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num only [pow_one] at hh
    omega
  have h := knownCount_success (I := Reg n) Fintype.card_pos (preimages f y)
    (m := 1) hunique (by norm_num) hN
  simpa only [iterations, Nat.cast_one, card_reg, Nat.cast_pow, Nat.cast_ofNat] using h

/-- For positive width and a singleton target fiber, the logarithmic budget hypothesis yields
unitarity, normalized output, success at least `1 - 1 / 2ⁿ`, and priced query count at most
`2 ^ C`. This realizes the overhead-adjusted budget discussed in [AmyEtAl2017]. -/
theorem unique_preimage_budget {n m : ℕ} (hn : 0 < n) (v C : ℝ)
    (hbudget : (n : ℝ)/2 + v*log2 n ≤ C) (f : Reg n → Reg m) (y : Reg m)
    (hunique : (preimages f y).card = 1) :
    IsUnitaryCircuit (program n) ∧
      Normalized (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) ∧
      1 - (1 : ℝ)/(2 : ℝ)^n ≤
        MeasureProb (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) (preimages f y) ∧
      pricedQueries n v ≤ (2 : ℝ)^C :=
  ⟨program_unitary n, preimage_output_normalized f y, unique_fiber_success hn f y hunique,
    program_budget_from_threshold hn v C hbudget⟩

end
end Qatlib.Papers.QPreimage16.GroverBudget
