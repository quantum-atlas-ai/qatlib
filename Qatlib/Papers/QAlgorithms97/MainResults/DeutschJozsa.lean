/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted

/-!
# Deutsch-Jozsa interference and readout

This module constructs the uniform, phase-encoded, and final states of the Deutsch-Jozsa
algorithm and relates them to a one-query bit-oracle circuit. It proves the deterministic
constant-versus-balanced outcome rule and identifies the sign-sum definition of balance with
equal output counts, following [CleveEtAl1998].

## Main statements

* `deutschJozsa_single_query`: the promised output probabilities and one-query count.
* `dj_circuit_run`: the bit-oracle circuit realizes the specified final state.
* `djBalanced_iff_counts`: balance is equivalent to exactly half of the inputs being true.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

variable {n : ℕ}

/-- The common amplitude of the uniform state on `n` Boolean qubits, given by the `n`th power of
the inverse square root of two. -/
def djUniformAmp (n : ℕ) : ℂ := ((Real.sqrt 2 : ℂ)⁻¹) ^ n

/-- The complex sign associated with a Boolean function value, equal to minus one for true and
one for false. -/
def djSign {n : ℕ} (f : Reg n → Bool) (x : Reg n) : ℂ :=
  if f x then (-1 : ℂ) else 1

/-- The constant-amplitude state produced by applying Hadamards to the all-zero register. -/
def djAfterH (n : ℕ) : QState (Reg n) := fun _ => djUniformAmp n

/-- The uniform register state after application of the Boolean phase oracle. -/
def djPhaseState {n : ℕ} (f : Reg n → Bool) : QState (Reg n) :=
  ApplyGate (PhaseOracle f) (djAfterH n)

/-- The state obtained by applying the final Hadamard transform to the phase-encoded uniform
state. -/
def djFinalState {n : ℕ} (f : Reg n → Bool) : QState (Reg n) :=
  ApplyGate (HadamardN n) (djPhaseState f)

/-- A Boolean function is constant if all inputs have the same output bit. -/
def DJConstant {n : ℕ} (f : Reg n → Bool) : Prop := ∃ b : Bool, ∀ x, f x = b

/-- A Boolean function is balanced when the sum of its complex signs is zero. -/
def DJBalanced {n : ℕ} (f : Reg n → Bool) : Prop := (∑ x : Reg n, djSign f x) = 0

/-- The Deutsch-Jozsa word with a lifted Hadamard transform, one query, and a final lifted
Hadamard transform. -/
def djCircuit (n : ℕ) : Circuit (Reg n × Bool) :=
  [Step.gate (LiftGate (HadamardN n)), Step.query,
    Step.gate (LiftGate (HadamardN n))]

/-- The Hadamard transform of the all-zero basis state is `djAfterH n`. -/
@[simp] lemma dj_afterH_apply (n : ℕ) :
    ApplyGate (HadamardN n) (Ket (ZeroStr n)) = djAfterH n := by
  funext x
  rw [ApplyGate, hadamardN_mulVec_ket_zero]
  rfl

/-- Each phase-state amplitude is the uniform amplitude multiplied by the function's sign at
that input. -/
lemma djPhaseState_apply {n : ℕ} (f : Reg n → Bool) (x : Reg n) :
    djPhaseState f x = djSign f x * djUniformAmp n := by
  unfold djPhaseState djSign djAfterH
  rw [OracleInterfaces.phaseOracle_apply]

/-- The square of the uniform amplitude is the inverse of `2 ^ n`. -/
lemma djUniformAmp_sq (n : ℕ) :
    djUniformAmp n * djUniformAmp n = ((2 : ℂ) ^ n)⁻¹ := by
  unfold djUniformAmp
  rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
    rw [pow_two, inv_sqrt2_mul_self]
  rw [h2, ← inv_pow]

/-- The square of the uniform amplitude multiplied by `2 ^ n` is one. -/
lemma djUniformAmp_sq_mul_card (n : ℕ) :
    djUniformAmp n * djUniformAmp n * (2 : ℂ) ^ n = 1 := by
  rw [djUniformAmp_sq]
  exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num))

/-- The sum of the binary signs for a Hadamard row is `2 ^ n` for the zero row and zero
otherwise. -/
lemma hadamardN_row_sum_zero (y : Reg n) :
    (∑ x : Reg n, ∏ i, (if y i && x i then (-1 : ℂ) else 1)) =
      if y = ZeroStr n then (2 : ℂ) ^ n else 0 := by
  have h := bv_orthogonality (n := n) y (ZeroStr n)
  simpa [ZeroStr, funext_iff] using! h

/-- The sum of a Hadamard row is the uniform amplitude times `2 ^ n` at the zero row, and zero
elsewhere. -/
lemma dj_hadamard_row_sum (y : Reg n) :
    (∑ x : Reg n, HadamardN n y x) =
      djUniformAmp n * (if y = ZeroStr n then (2 : ℂ) ^ n else 0) := by
  calc
    (∑ x : Reg n, HadamardN n y x)
        = ∑ x : Reg n,
            djUniformAmp n * ∏ i, (if y i && x i then (-1 : ℂ) else 1) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hadamardN_apply]
          rfl
    _ = djUniformAmp n *
          ∑ x : Reg n, ∏ i, (if y i && x i then (-1 : ℂ) else 1) := by
          rw [Finset.mul_sum]
    _ = djUniformAmp n * (if y = ZeroStr n then (2 : ℂ) ^ n else 0) := by
          rw [hadamardN_row_sum_zero]

/-- Each final Deutsch-Jozsa amplitude is the uniform amplitude times the Hadamard-weighted sum
of the function signs. -/
lemma dj_final_apply (f : Reg n → Bool) (y : Reg n) :
    djFinalState f y =
      djUniformAmp n * ∑ x : Reg n, HadamardN n y x * djSign f x := by
  unfold djFinalState
  rw [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [djPhaseState_apply]
  ring

/-- For a constant function, the final state is the all-zero basis state with sign determined by
the constant output. -/
lemma dj_constant_state (f : Reg n → Bool) (b : Bool) (hf : ∀ x, f x = b) :
    djFinalState f =
      fun y => if y = ZeroStr n then (if b then (-1 : ℂ) else 1) else 0 := by
  funext y
  rw [dj_final_apply]
  have hsig : ∀ x, djSign f x = (if b then (-1 : ℂ) else 1) := by
    intro x
    simp [djSign, hf x]
  simp only [hsig]
  rw [← Finset.sum_mul, dj_hadamard_row_sum]
  by_cases hy : y = ZeroStr n
  · rw [if_pos hy, if_pos hy]
    calc
      djUniformAmp n *
          (djUniformAmp n * (2 : ℂ) ^ n * (if b then (-1 : ℂ) else 1))
          = (if b then (-1 : ℂ) else 1) *
              (djUniformAmp n * djUniformAmp n * (2 : ℂ) ^ n) := by ring
      _ = (if b then (-1 : ℂ) else 1) * 1 := by rw [djUniformAmp_sq_mul_card]
      _ = (if b then (-1 : ℂ) else 1) := by ring
  · rw [if_neg hy, if_neg hy]
    ring

/-- A balanced function gives zero amplitude at the all-zero output. -/
lemma dj_balanced_zero (f : Reg n → Bool) (hb : DJBalanced f) :
    djFinalState f (ZeroStr n) = 0 := by
  rw [dj_final_apply]
  have hrow : ∀ x : Reg n, HadamardN n (ZeroStr n) x = djUniformAmp n := by
    intro x
    rw [hadamardN_apply_zero_left]
    rfl
  simp only [hrow]
  rw [← Finset.mul_sum, hb]
  ring

/-- A constant function yields the all-zero outcome with probability one. -/
lemma dj_constant_zero_prob (f : Reg n → Bool) (b : Bool) (hf : ∀ x, f x = b) :
    MeasureProb (djFinalState f) ({ZeroStr n} : Finset (Reg n)) = 1 := by
  rw [MeasureProb, Finset.sum_singleton, BornProb, dj_constant_state f b hf]
  by_cases hb : b <;> simp [hb]

/-- A balanced function yields the all-zero outcome with probability zero. -/
lemma dj_balanced_zero_prob (f : Reg n → Bool) (hb : DJBalanced f) :
    MeasureProb (djFinalState f) ({ZeroStr n} : Finset (Reg n)) = 0 := by
  simp [MeasureProb, BornProb, dj_balanced_zero f hb]

/-- The final Deutsch-Jozsa state is normalized for every Boolean function. -/
lemma djFinalState_normalized (f : Reg n → Bool) : Normalized (djFinalState f) := by
  have h0 : Normalized (djAfterH n) := by
    rw [← dj_afterH_apply]
    exact normalized_applyGate (hadamardN_unitary n) (normalized_ket _)
  exact normalized_applyGate (hadamardN_unitary n)
    (normalized_applyGate (OracleInterfaces.phaseOracle_unitary f) h0)

/-- A balanced function gives a nonzero register outcome with probability one. -/
lemma dj_balanced_nonzero_prob (f : Reg n → Bool) (hb : DJBalanced f) :
    MeasureProb (djFinalState f) (Finset.univ.erase (ZeroStr n)) = 1 := by
  have hnorm := djFinalState_normalized f
  have hsplit :
      MeasureProb (djFinalState f) (Finset.univ.erase (ZeroStr n)) +
        MeasureProb (djFinalState f) ({ZeroStr n} : Finset (Reg n)) = 1 := by
    rw [MeasureProb, MeasureProb, Finset.sum_singleton]
    rw [Finset.sum_erase_add (s := (Finset.univ : Finset (Reg n)))
      (f := fun x => BornProb (djFinalState f) x) (Finset.mem_univ _)]
    simpa [MeasureProb] using measureProb_univ hnorm
  have hz := dj_balanced_zero_prob f hb
  linarith

/-- The Deutsch-Jozsa construction yields zero with certainty for constant functions and a
nonzero outcome with certainty for balanced functions, with exactly one query [Cleve et al.,
Section 3][CleveEtAl1998]. -/
theorem deutschJozsa_single_query (f : Reg n → Bool) :
    (DJConstant f → MeasureProb (djFinalState f) ({ZeroStr n} : Finset (Reg n)) = 1) ∧
    (DJBalanced f →
      MeasureProb (djFinalState f) ({ZeroStr n} : Finset (Reg n)) = 0 ∧
      MeasureProb (djFinalState f) (Finset.univ.erase (ZeroStr n)) = 1) ∧
    QueryCount (djCircuit n) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hf⟩
    exact dj_constant_zero_prob f b hf
  · intro hb
    exact ⟨dj_balanced_zero_prob f hb, dj_balanced_nonzero_prob f hb⟩
  · simp [djCircuit]

/-- On the zero register and minus ancilla, the bit-oracle Deutsch-Jozsa word produces
`djFinalState f` tensored with the unchanged ancilla and uses one query [CleveEtAl1998]. -/
theorem dj_circuit_run (f : Reg n → Bool) :
    Run (BitOracleOn f) (djCircuit n) (TensorState (Ket (ZeroStr n)) Minus) =
      TensorState (djFinalState f) Minus ∧
    QueryCount (djCircuit n) = 1 := by
  refine ⟨?_, ?_⟩
  · simp only [djCircuit, Run, applyGate_liftGate]
    rw [dj_afterH_apply, OracleInterfaces.bitOracle_minus, applyGate_liftGate]
    rfl
  · simp [djCircuit]

/-- The sum of function signs is `2 ^ n` minus twice the number of inputs where the function is
true. -/
lemma sum_djSign_eq (f : Reg n → Bool) :
    (∑ x : Reg n, djSign f x) =
      (2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x => f x)).card : ℂ) := by
  have h : (∑ x : Reg n, djSign f x) =
      ∑ x : Reg n, (1 - 2 * (if f x then (1 : ℂ) else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f x
    · simp [djSign, hx]; norm_num
    · simp [djSign, hx]
  rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  rw [Finset.sum_boole]
  norm_num

/-- A Boolean function is balanced exactly when twice its number of true inputs equals `2 ^ n`
[CleveEtAl1998]. -/
lemma djBalanced_iff_counts (f : Reg n → Bool) :
    DJBalanced f ↔
      2 * (Finset.univ.filter (fun x => f x)).card = 2 ^ n := by
  rw [DJBalanced, sum_djSign_eq]
  constructor
  · intro h
    have h' : (2 : ℂ) * ((Finset.univ.filter (fun x => f x)).card : ℂ) = (2 : ℂ) ^ n := by
      have := sub_eq_zero.mp h
      exact this.symm
    have h'' : ((2 * (Finset.univ.filter (fun x => f x)).card : ℕ) : ℂ) =
        ((2 ^ n : ℕ) : ℂ) := by
      push_cast
      simpa [mul_comm] using h'
    exact Nat.cast_injective h''
  · intro h
    have h' : (2 : ℂ) * ((Finset.univ.filter (fun x => f x)).card : ℂ) = (2 : ℂ) ^ n := by
      have : ((2 * (Finset.univ.filter (fun x => f x)).card : ℕ) : ℂ) =
          ((2 ^ n : ℕ) : ℂ) := by exact_mod_cast h
      push_cast at this
      simpa using this
    rw [h']
    ring

end Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
