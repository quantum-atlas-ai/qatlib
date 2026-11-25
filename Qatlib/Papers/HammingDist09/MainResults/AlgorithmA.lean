/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HammingDist09.MainResults.Basic
public import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
public import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
public import Qatlib.Foundations.PureStateMath.Tensor

@[expose] public section

/-!
# The counted Hamming-distance word

Algorithm A of arXiv:0912.0583v1 (p. 6) prepares the data and the answer,
applies the Hamming-weight phase, makes one bit query, permutes the data
by the even-length involution, and applies the final Walsh transform.
The list is written in matrix-product order, so its rightmost gate acts first.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators
open Qatlib.Papers.HammingDist09.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability (WellFormedAdjointCircuit)

namespace Qatlib.Papers.HammingDist09.MainResults

/-- The shared scale of the entries of the `n`-bit Walsh transform. -/
def walshScale (n : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)⁻¹

/-- The normalized binary character table, as a matrix on `n` data bits. -/
def walshGate (n : ℕ) : Matrix (Word n) (Word n) ℂ :=
  Matrix.of (fun y x => walshScale n * (-1 : ℂ) ^ (dot y x).val)

private theorem walshScale_mul (n : ℕ) :
    walshScale n * walshScale n = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← pow_two, walshScale, inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (by positivity), Complex.ofReal_pow, Complex.ofReal_ofNat]

private theorem dot_swap {n : ℕ} (x y : Word n) : dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private theorem word_add_zero_iff {n : ℕ} (x y : Word n) : x + y = 0 ↔ x = y := by
  have hy : y + y = 0 := by
    funext j
    exact zmod2_add_self (y j)
  constructor
  · intro h
    exact add_right_cancel (h.trans hy.symm)
  · rintro rfl
    exact hy

/-- Orthogonality of the normalized binary characters gives a unitary Walsh gate. -/
theorem walshGate_unitary (n : ℕ) : walshGate n ∈ Matrix.unitaryGroup (Word n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext y z
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hscale : star (walshScale n) = walshScale n := by
    simp [walshScale]
  simp only [Matrix.conjTranspose_apply, walshGate, Matrix.of_apply,
    star_mul', star_pow, star_neg, star_one, hscale]
  have hterm (x : Word n) :
      (walshScale n * (-1 : ℂ) ^ (dot x y).val) *
          (walshScale n * (-1 : ℂ) ^ (dot x z).val) =
        ((2 : ℂ) ^ n)⁻¹ * (-1 : ℂ) ^ (dot (y + z) x).val := by
    rw [dot_swap x y, dot_swap x z]
    calc
      _ = (walshScale n * walshScale n) *
          ((-1 : ℂ) ^ (dot y x).val * (-1 : ℂ) ^ (dot z x).val) := by ring
      _ = _ := by rw [← neg_one_pow_dot_add, walshScale_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_neg_one_pow_dot]
  simp only [word_add_zero_iff]
  by_cases h : y = z
  · subst z
    simp
  · simp [h]

/-- The sign on the second binary digit of the Hamming weight, before the query. -/
def weightPhase (n : ℕ) : Matrix (Word n) (Word n) ℂ :=
  Matrix.diagonal (fun x => (-1 : ℂ) ^ b1 (wt x))

/-- The bit added by the oracle for the hidden word `a`. -/
def distanceBit {n : ℕ} (a x : Word n) : Bool := decide (b1 (dist a x) = 1)

/-- Algorithm A's matrix word, with precisely one forward query. -/
def hammingWord (n : ℕ) : List (AdjointStep (Word n × Bool)) :=
  [.gate (TensorGate (walshGate n) 1),
   .gate (TensorGate (permMatrix (hatX (n := n))) 1),
   .forward,
   .gate (TensorGate (weightPhase n) 1),
   .gate (TensorGate (walshGate n) Hadamard),
   .gate (TensorGate 1 PauliX)]

/-- The explicit steps are unitary at even word length. -/
theorem hammingWord_wellFormed {n : ℕ} (hn : Even n) :
    WellFormedAdjointCircuit (hammingWord n) := by
  have hphase : weightPhase n ∈ Matrix.unitaryGroup (Word n) ℂ := by
    apply diagonal_mem_unitaryGroup
    intro x
    simp [norm_pow]
  have h1 : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ :=
    Submonoid.one_mem _
  have h2 : (1 : Matrix (Word n) (Word n) ℂ) ∈ Matrix.unitaryGroup (Word n) ℂ :=
    Submonoid.one_mem _
  simp [hammingWord, tensorGate_unitary (walshGate_unitary n) h1,
    tensorGate_unitary (permMatrix_unitary (hatX_hatX_of_even hn)) h1,
    tensorGate_unitary hphase h1, tensorGate_unitary (walshGate_unitary n) hadamard_unitary,
    tensorGate_unitary h2 pauliX_unitary]

/-- The word calls the hidden oracle exactly once. -/
theorem hammingWord_queryCount (n : ℕ) : adjointQueryCount (hammingWord n) = 1 := rfl

private theorem walsh_zero (n : ℕ) :
    ApplyGate (walshGate n) (Ket (0 : Word n)) = fun _ => walshScale n := by
  funext x
  simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, walshGate, dot]

private theorem distance_phase {n : ℕ} (a x : Word n) :
    (if distanceBit a x then (-1 : ℂ) else 1) = (-1 : ℂ) ^ b1 (dist a x) := by
  have h : b1 (dist a x) < 2 := Nat.mod_lt _ (by decide)
  interval_cases hm : b1 (dist a x) <;> simp [distanceBit, hm]

/-- Evaluating the counted circuit on the all-zero input yields the normalized amplitude
formula of Theorem 3.2 with the answer qubit restored to its minus state. -/
theorem hammingWord_amplitude {n : ℕ} (hn : Even n) (a : Word n) :
    ApplyGate (evaluate (BitOracleOn (distanceBit a)) (hammingWord n))
        (Ket ((0 : Word n), false)) =
      TensorState (algNormAmp a) Minus := by
  simp only [hammingWord, evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul]
  simp only [← tensorState_ket_ket, applyGate_tensorGate, applyGate_one, applyGate_pauliX_ket,
    Bool.not_false, applyGate_hadamard_ket_true, walsh_zero, weightPhase, applyGate_diagonal,
    applyGate_bitOracleOn_tensorState_minus]
  have hdata :
      ApplyGate (permMatrix (hatX (n := n)))
          (ApplyGate (PhaseOracle (distanceBit a))
            (fun x => (-1 : ℂ) ^ b1 (wt x) * walshScale n)) =
        fun x => walshScale n *
          (-1 : ℂ) ^ (b1 (wt (hatX x)) + b1 (dist a (hatX x))) := by
    funext x
    rw [applyGate_permMatrix (hatX_hatX_of_even hn), applyGate_phaseOracle, distance_phase, pow_add]
    ring
  rw [hdata]
  congr 1
  funext y
  simp only [ApplyGate, Matrix.mulVec, dotProduct, walshGate, Matrix.of_apply, algNormAmp, algAmp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← walshScale_mul]
  ring

/-- At even length the evaluated word returns the hidden data ket up to its source global
phase, preserving the minus state of the answer register. -/
theorem hammingWord_recovers {n : ℕ} (hn : Even n) (a : Word n) :
    ApplyGate (evaluate (BitOracleOn (distanceBit a)) (hammingWord n))
      (Ket ((0 : Word n), false)) =
        TensorState (((-1 : ℂ) ^ b1 (wt a)) • Ket a) Minus := by
  rw [hammingWord_amplitude hn]
  congr 1
  funext y
  rw [(theorem_3_2 hn a).1 y]
  by_cases h : y = a <;> simp [Ket, h]

end Qatlib.Papers.HammingDist09.MainResults
