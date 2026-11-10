/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch
import Qatlib.Foundations.ResourceBounds.LogBudgets
set_option warningAsError false

namespace Qatlib.Papers.QPreimage16.GroverBudget
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.ResourceBounds.LogBudgets

def preimages {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) : Finset (Reg n) :=
  Finset.univ.filter (fun x => f x = y)

theorem preimages_eq_singleton {n : ℕ} (f : Reg n ≃ Reg n) (y : Reg n) :
    preimages f y = {f.symm y} := by
  ext x
  simp [preimages, Equiv.eq_symm_apply]

def preimagePhase {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if decide (x ∈ preimages f y) then -1 else 1)

def iterations (n : ℕ) : ℕ :=
  groverIterations (knownCountAngle ((1 : ℝ) / Fintype.card (Reg n)))

def program (n : ℕ) : Circuit (Reg n) := PreparedGroverCircuit n (iterations n)

theorem run_program {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) :
    Run (preimagePhase f y) (program n) (Ket (ZeroStr n)) =
      GroverState (preimages f y) (iterations n) := by
  exact run_preparedGroverCircuit n (iterations n) (preimages f y)

theorem program_queries (n : ℕ) : QueryCount (program n) = iterations n :=
  queryCount_preparedGroverCircuit n (iterations n)

theorem program_macros (n : ℕ) : GateCount (program n) = iterations n + 1 :=
  gateCount_preparedGroverCircuit n (iterations n)

theorem program_unitary (n : ℕ) : IsUnitaryCircuit (program n) :=
  (preparedGroverAlgorithm n (iterations n)).unitary

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

theorem preimagePhase_diagonal {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) (x : Reg n) :
    preimagePhase f y x x = if f x = y then (-1 : ℂ) else 1 := by
  simp [preimagePhase, preimages]

theorem preimage_output_normalized {n m : ℕ} (f : Reg n → Reg m) (y : Reg m) :
    Normalized (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) := by
  exact normalized_preparedGroverCircuit n (iterations n) (preimages f y)

def pricedQueries (n : ℕ) (v : ℝ) : ℝ := (n : ℝ)^v * QueryCount (program n)

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

theorem native_preimage_budget {n : ℕ} (hn : 0 < n) (v C : ℝ)
    (hbudget : (n : ℝ)/2 + v*log2 n ≤ C) (f : Reg n ≃ Reg n) (y : Reg n) :
    IsUnitaryCircuit (program n) ∧
      Normalized (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) ∧
      1 - (1 : ℝ)/(2 : ℝ)^n ≤
        MeasureProb (Run (preimagePhase f y) (program n) (Ket (ZeroStr n))) (preimages f y) ∧
      pricedQueries n v ≤ (2 : ℝ)^C :=
  ⟨program_unitary n, preimage_output_normalized f y, preimage_success hn f y,
    program_budget_from_threshold hn v C hbudget⟩

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
