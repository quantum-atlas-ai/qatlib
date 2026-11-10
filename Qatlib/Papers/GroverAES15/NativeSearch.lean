/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverAES15.NativeOracle
import Qatlib.Papers.GroverAES15.KeyPredicate
set_option warningAsError false

namespace Qatlib.Papers.GroverAES15.NativeSearch
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.CipherCircuits.CipherOracle
open Qatlib.Papers.GroverAES15.KeyPredicate
open Qatlib.Papers.GroverAES15.NativeOracle
open scoped Matrix
variable {n r : ℕ}

def iterations (n m : ℕ) : ℕ :=
  if 2*m ≤ Fintype.card (Reg n) then
    groverIterations (knownCountAngle ((m:ℝ)/Fintype.card (Reg n))) else 0

def program (n m : ℕ) : Circuit (Reg n) := PreparedGroverCircuit n (iterations n m)

theorem phase_literal (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) :
    phaseMatrix (transcript enc texts) (target ciphertexts) =
      Matrix.diagonal (fun key => if decide (key ∈ marked enc texts ciphertexts) then (-1:ℂ) else 1) := by
  ext x y
  simp [phaseMatrix, marked, Matrix.diagonal_apply]

theorem run_ideal (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (j : ℕ) :
    Run (phaseMatrix (transcript enc texts) (target ciphertexts)) (PreparedGroverCircuit n j)
      (Ket (ZeroStr n)) = GroverState (marked enc texts ciphertexts) j := by
  have h := run_preparedGroverCircuit n j (marked enc texts ciphertexts)
  change Run (Matrix.diagonal (fun key => if decide (key ∈ marked enc texts ciphertexts)
    then (-1:ℂ) else 1)) (PreparedGroverCircuit n j) (Ket (ZeroStr n)) = _ at h
  rw [← phase_literal enc texts ciphertexts] at h
  exact h

def physicalProgram (n m r : ℕ) : Circuit (Whole (Reg n) (Fin r × Fin 128)) :=
  workCircuit (program n m)

def initial (n r : ℕ) : Whole (Reg n) (Fin r × Fin 128) → ℂ := embed (Ket (ZeroStr n))

def output (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    Whole (Reg n) (Fin r × Fin 128) → ℂ :=
  Run (oracleMatrix (transcript enc texts) (target ciphertexts)) (physicalProgram n m r) (initial n r)

def successEvent (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) :
    Finset (Whole (Reg n) (Fin r × Fin 128)) := fullEvent (marked enc texts ciphertexts)

theorem output_exact (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    output enc texts ciphertexts m =
      embed (GroverState (marked enc texts ciphertexts) (iterations n m)) := by
  unfold output physicalProgram initial
  rw [run_workCircuit]
  exact congrArg embed (run_ideal enc texts ciphertexts (iterations n m))

theorem physicalProgram_unitary (n m r : ℕ) : IsUnitaryCircuit (physicalProgram n m r) :=
  workCircuit_unitary _ (preparedGroverAlgorithm n (iterations n m)).unitary

theorem output_normalized (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    Normalized (output enc texts ciphertexts m) :=
  normalized_work_run _ _ _ (preparedGroverAlgorithm n (iterations n m)).unitary _ (normalized_ket _)

theorem output_born (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    MeasureProb (output enc texts ciphertexts m) (successEvent enc texts ciphertexts) =
      MeasureProb (GroverState (marked enc texts ciphertexts) (iterations n m))
        (marked enc texts ciphertexts) := by
  rw [output_exact]
  exact measure_embed _ _

theorem physical_queries (n m r : ℕ) : QueryCount (physicalProgram n m r) = iterations n m := by
  rw [physicalProgram, workCircuit_queries]
  exact queryCount_preparedGroverCircuit n (iterations n m)

theorem physical_macros (n m r : ℕ) : GateCount (physicalProgram n m r) = iterations n m + 1 := by
  rw [physicalProgram, workCircuit_macros]
  exact gateCount_preparedGroverCircuit n (iterations n m)

theorem uniform_mass (A : Finset (Reg n)) :
    MeasureProb (Uniform (Reg n)) A = (A.card:ℝ)/Fintype.card (Reg n) := by
  simp [MeasureProb, BornProb, Uniform, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, inv_pow, div_eq_mul_inv]

theorem sparse_success (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block)
    {m : ℕ} (hA : (marked enc texts ciphertexts).card = m) (hm : 0 < m)
    (half : 2*m ≤ Fintype.card (Reg n)) :
    1 - (m:ℝ)/Fintype.card (Reg n) ≤
      MeasureProb (output enc texts ciphertexts m) (successEvent enc texts ciphertexts) := by
  rw [output_born]
  unfold iterations
  rw [if_pos half]
  exact knownCount_success Fintype.card_pos _ hA hm (by omega)

theorem known_count_success (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block)
    {m : ℕ} (hA : (marked enc texts ciphertexts).card = m) (hm : 0 < m) :
    (1:ℝ)/2 ≤ MeasureProb (output enc texts ciphertexts m) (successEvent enc texts ciphertexts) := by
  have hp : (0:ℝ) < Fintype.card (Reg n) := Nat.cast_pos.mpr Fintype.card_pos
  by_cases half : 2*m ≤ Fintype.card (Reg n)
  · have h := sparse_success enc texts ciphertexts hA hm half
    have hfrac : (m:ℝ)/Fintype.card (Reg n) ≤ 1/2 := by
      apply (div_le_iff₀ hp).mpr
      have hh : (2:ℝ)*m ≤ Fintype.card (Reg n) := by exact_mod_cast half
      linarith
    linarith
  · rw [output_born]
    have hz : iterations n m = 0 := if_neg half
    rw [hz]
    change (1:ℝ)/2 ≤ MeasureProb (Uniform (Reg n)) (marked enc texts ciphertexts)
    rw [uniform_mass, hA]
    apply (le_div_iff₀ hp).mpr
    have hh : (Fintype.card (Reg n):ℝ) < 2*m := by
      exact_mod_cast (by omega : Fintype.card (Reg n) < 2*m)
    linarith

theorem physical_query_budget (n m r : ℕ) (hm : 0 < m) :
    (QueryCount (physicalProgram n m r):ℝ) ≤
      Real.pi/(4*Real.sqrt ((m:ℝ)/Fintype.card (Reg n))) := by
  rw [physical_queries]
  by_cases half : 2*m ≤ Fintype.card (Reg n)
  · simp only [iterations, if_pos half]
    exact knownCount_query_budget hm (by omega)
  · simp only [iterations, if_neg half, Nat.cast_zero]
    positivity

theorem unique_key_success (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block)
    (hn : 0 < n) (hA : (marked enc texts ciphertexts).card = 1) :
    1 - (1:ℝ)/(2:ℝ)^n ≤
      MeasureProb (output enc texts ciphertexts 1) (successEvent enc texts ciphertexts) := by
  have hN : 2 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    simpa using h
  have h := sparse_success enc texts ciphertexts hA (by norm_num) (by omega)
  simpa only [Nat.cast_one, card_reg, Nat.cast_pow, Nat.cast_ofNat] using h

end
end Qatlib.Papers.GroverAES15.NativeSearch
