/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverAES15.NativeOracle
import Qatlib.Papers.GroverAES15.KeyPredicate

/-!
# Known-count Grover search for transcript-matching keys

This module constructs a prepared Grover circuit for the set of keys matching supplied block
transcripts and lifts it to the cipher workspace. The output is exactly an embedded Grover
state, with normalization, query counts, and success bounds formalizing the search component of
[GrasslEtAl2015].

The iteration choice uses the known marked count when it is at most half the key space and
otherwise uses zero Grover iterations. Positive known counts yield success probability at least
one half, with stronger bounds in the sparse and unique-key cases.

## Main statements

* `output_exact`: the exact embedded Grover output.
* `known_count_success`: a one-half success bound for a positive known marked count.
* `physical_query_budget`: the inverse-square-root query bound.
* `unique_key_success`: the success bound for a unique matching key.

## References

* [Grassl et al., 2015][GrasslEtAl2015]
-/

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

/-- The known-count Grover iteration choice when `2*m` is at most the key-space cardinality, and
zero iterations otherwise. -/
def iterations (n m : ℕ) : ℕ :=
  if 2*m ≤ Fintype.card (Reg n) then
    groverIterations (knownCountAngle ((m:ℝ)/Fintype.card (Reg n))) else 0

/-- The prepared Grover circuit using the iteration count chosen for `n` key bits and `m` marked
keys. -/
def program (n m : ℕ) : Circuit (Reg n) := PreparedGroverCircuit n (iterations n m)

/-- The transcript phase oracle is diagonal, applying `-1` exactly to keys in the marked set and
`1` to all other keys. -/
theorem phase_literal (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) :
    phaseMatrix (transcript enc texts) (target ciphertexts) =
      Matrix.diagonal (fun key => if decide (key ∈ marked enc texts ciphertexts) then (-1:ℂ) else 1) := by
  ext x y
  simp [phaseMatrix, marked, Matrix.diagonal_apply]

/-- Running the prepared phase-oracle circuit from the zero basis state produces the Grover
state for the transcript-matching key set after `j` iterations. -/
theorem run_ideal (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (j : ℕ) :
    Run (phaseMatrix (transcript enc texts) (target ciphertexts)) (PreparedGroverCircuit n j)
      (Ket (ZeroStr n)) = GroverState (marked enc texts ciphertexts) j := by
  have h := run_preparedGroverCircuit n j (marked enc texts ciphertexts)
  change Run (Matrix.diagonal (fun key => if decide (key ∈ marked enc texts ciphertexts)
    then (-1:ℂ) else 1)) (PreparedGroverCircuit n j) (Ket (ZeroStr n)) = _ at h
  rw [← phase_literal enc texts ciphertexts] at h
  exact h

/-- The workspace lift of the prepared key-register Grover program, with space for `r`
ciphertext blocks. -/
def physicalProgram (n m r : ℕ) : Circuit (Whole (Reg n) (Fin r × Fin 128)) :=
  workCircuit (program n m)

/-- The zero key basis state embedded with the auxiliary cipher workspace. -/
def initial (n r : ℕ) : Whole (Reg n) (Fin r × Fin 128) → ℂ := embed (Ket (ZeroStr n))

/-- The state obtained by executing the physical key-search program with the transcript oracle
and initial embedded state. -/
def output (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    Whole (Reg n) (Fin r × Fin 128) → ℂ :=
  Run (oracleMatrix (transcript enc texts) (target ciphertexts)) (physicalProgram n m r) (initial n r)

/-- The event that the key matches all supplied transcript pairs and the auxiliary bank is
clean. -/
def successEvent (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) :
    Finset (Whole (Reg n) (Fin r × Fin 128)) := fullEvent (marked enc texts ciphertexts)

/-- The physical search output is the embedded Grover state for the marked keys at the chosen
iteration count [GrasslEtAl2015]. -/
theorem output_exact (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    output enc texts ciphertexts m =
      embed (GroverState (marked enc texts ciphertexts) (iterations n m)) := by
  unfold output physicalProgram initial
  rw [run_workCircuit]
  exact congrArg embed (run_ideal enc texts ciphertexts (iterations n m))

/-- The physical key-search program is a unitary circuit [GrasslEtAl2015]. -/
theorem physicalProgram_unitary (n m r : ℕ) : IsUnitaryCircuit (physicalProgram n m r) :=
  workCircuit_unitary _ (preparedGroverAlgorithm n (iterations n m)).unitary

/-- The physical key-search output is normalized [GrasslEtAl2015]. -/
theorem output_normalized (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    Normalized (output enc texts ciphertexts m) :=
  normalized_work_run _ _ _ (preparedGroverAlgorithm n (iterations n m)).unitary _ (normalized_ket _)

/-- The success probability of the physical output equals the marked-set probability of the
corresponding Grover state. -/
theorem output_born (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block) (m : ℕ) :
    MeasureProb (output enc texts ciphertexts m) (successEvent enc texts ciphertexts) =
      MeasureProb (GroverState (marked enc texts ciphertexts) (iterations n m))
        (marked enc texts ciphertexts) := by
  rw [output_exact]
  exact measure_embed _ _

/-- The physical key-search program uses exactly the chosen number of oracle queries. -/
theorem physical_queries (n m r : ℕ) : QueryCount (physicalProgram n m r) = iterations n m := by
  rw [physicalProgram, workCircuit_queries]
  exact queryCount_preparedGroverCircuit n (iterations n m)

/-- The physical key-search program has one more gate step than its chosen Grover iteration
count. -/
theorem physical_macros (n m r : ℕ) : GateCount (physicalProgram n m r) = iterations n m + 1 := by
  rw [physicalProgram, workCircuit_macros]
  exact gateCount_preparedGroverCircuit n (iterations n m)

/-- A uniform key state assigns an event its cardinality divided by the key-space cardinality. -/
theorem uniform_mass (A : Finset (Reg n)) :
    MeasureProb (Uniform (Reg n)) A = (A.card:ℝ)/Fintype.card (Reg n) := by
  simp [MeasureProb, BornProb, Uniform, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, inv_pow, div_eq_mul_inv]

/-- If the actual marked count is positive and at most half the key space, the physical search
succeeds with probability at least `1 - m / |Reg n|`. -/
theorem sparse_success (enc : Reg n → Block → Block) (texts ciphertexts : Fin r → Block)
    {m : ℕ} (hA : (marked enc texts ciphertexts).card = m) (hm : 0 < m)
    (half : 2*m ≤ Fintype.card (Reg n)) :
    1 - (m:ℝ)/Fintype.card (Reg n) ≤
      MeasureProb (output enc texts ciphertexts m) (successEvent enc texts ciphertexts) := by
  rw [output_born]
  unfold iterations
  rw [if_pos half]
  exact knownCount_success Fintype.card_pos _ hA hm (by omega)

/-- If `m` is the positive actual marked count, the physical key-search output has success
probability at least one half [GrasslEtAl2015]. -/
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

/-- For positive `m`, the query count is at most `π / (4 * √(m / |Reg n|))` [GrasslEtAl2015]. -/
theorem physical_query_budget (n m r : ℕ) (hm : 0 < m) :
    (QueryCount (physicalProgram n m r):ℝ) ≤
      Real.pi/(4*Real.sqrt ((m:ℝ)/Fintype.card (Reg n))) := by
  rw [physical_queries]
  by_cases half : 2*m ≤ Fintype.card (Reg n)
  · simp only [iterations, if_pos half]
    exact knownCount_query_budget hm (by omega)
  · simp only [iterations, if_neg half, Nat.cast_zero]
    positivity

/-- For a positive key length and exactly one marked key, the physical search succeeds with
probability at least `1 - 1/2^n`. -/
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
