/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.SingleQuery97.MainResults.FourierLayers
import Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces

/-!
# Recovering binary affine coefficients

Binary affine maps are represented both over `ZMod 2` and as Boolean registers. The character
identities reduce a selected combination of output bits to a parity secret, and the explicit
one-query circuit `affineWord` recovers that secret with certainty, giving all rows in `m`
queries as in [CleveEtAl1998].

## Main statements

* `affine_parity_constant_iff`: constant output parity is equivalent to vanishing column sums.
* `affineWord_run`: the exact final state of the affine-query circuit.
* `affine_all_rows`: deterministic recovery of every row with total query count `m`.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.AffineCoefficients

/-- The value of a Boolean bit in the field `ZMod 2`. -/
def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0

/-- A Boolean register viewed as a vector over `ZMod 2`. -/
def regVec {n : ℕ} (x : Reg n) : Fin n → ZMod 2 := fun i => bitVal (x i)

/-- Matrix-vector multiplication over `ZMod 2` for a finite rectangular matrix. -/
def matVec {m n : ℕ} (A : Fin m → Fin n → ZMod 2) (v : Fin n → ZMod 2) :
    Fin m → ZMod 2 :=
  fun i => ∑ j, A i j * v j

/-- The vector obtained by summing all rows of a matrix over `ZMod 2`. -/
def rowSum {m n : ℕ} (A : Fin m → Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun j => ∑ i, A i j

/-- The affine image of a Boolean register under the matrix `A` and offset `b`, computed over
`ZMod 2`. -/
def affineVec {m n : ℕ} (A : Fin m → Fin n → ZMod 2) (b : Fin m → ZMod 2)
    (x : Reg n) : Fin m → ZMod 2 :=
  fun i => matVec A (regVec x) i + b i

/-- The sum of the coordinates of a finite vector over `ZMod 2`. -/
def vecSum {m : ℕ} (v : Fin m → ZMod 2) : ZMod 2 := ∑ i, v i

/-- The coordinate sum of an affine image is the dot product with the sum of the rows, plus the
coordinate sum of the offset. -/
lemma vecSum_affineVec {m n : ℕ} (A : Fin m → Fin n → ZMod 2)
    (b : Fin m → ZMod 2) (x : Reg n) :
    vecSum (affineVec A b x) =
      (∑ j, rowSum A j * regVec x j) + vecSum b := by
  simp only [vecSum, affineVec, matVec, rowSum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]

/-- The coordinate sum of an affine image is always the offset sum if and only if every
coordinate of the sum of the rows vanishes. -/
theorem affine_parity_constant_iff {m n : ℕ} (A : Fin m → Fin n → ZMod 2)
    (b : Fin m → ZMod 2) :
    (∀ x : Reg n, vecSum (affineVec A b x) = vecSum b) ↔
      ∀ j, rowSum A j = 0 := by
  constructor
  · intro h j
    let x0 : Reg n := fun k => decide (k = j)
    have hx : ∀ k, regVec x0 k = if k = j then (1 : ZMod 2) else 0 := by
      intro k
      by_cases hk : k = j <;> simp [regVec, bitVal, x0, hk]
    have h0 := h x0
    rw [vecSum_affineVec] at h0
    have hsum : (∑ j', rowSum A j' * regVec x0 j') = rowSum A j := by
      rw [Finset.sum_eq_single j]
      · simp [hx j]
      · intro j' _ hj'
        simp [hx j', hj']
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum] at h0
    have h0' : rowSum A j + vecSum b = 0 + vecSum b := by simpa using h0
    exact add_right_cancel h0'
  · intro h x
    rw [vecSum_affineVec]
    have hzero : ∀ j, rowSum A j * regVec x j = 0 := by
      intro j
      rw [h j, zero_mul]
    rw [Finset.sum_eq_zero (fun j _ => hzero j)]
    simp

/-- The Boolean parity of a finite bit vector, true exactly when its number of true coordinates
is odd. -/
def boolParity {k : ℕ} (v : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => v i).card % 2 = 1)

/-- The Boolean affine output bit given by the parity of rowwise products with `x`, followed by
addition of the offset bit. -/
def affineBit {m n : ℕ} (A : Fin m → Reg n) (b : Reg m) (i : Fin m)
    (x : Reg n) : Bool :=
  boolParity (fun j => A i j && x j) != b i

/-- The parity of the affine output coordinates selected by the mask `c`. -/
def affinePhaseBit {m n : ℕ} (c : Reg m) (A : Fin m → Reg n) (b : Reg m) :
    Reg n → Bool :=
  fun x => boolParity (fun i => c i && affineBit A b i x)

/-- The bit vector obtained by taking the parity of the rows of `A` selected by `c`. -/
def recoveredSecret {m n : ℕ} (c : Reg m) (A : Fin m → Reg n) : Reg n :=
  fun j => boolParity (fun i => c i && A i j)

open OracleInterfaces
open Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib.Papers.QComplexity97.XorSeparation

/-- Boolean conjunction becomes multiplication in `ZMod 2`. -/
theorem bitVal_and (a b : Bool) : bitVal (a && b) = bitVal a * bitVal b := by
  cases a <;> cases b <;> decide

/-- Boolean inequality becomes addition in `ZMod 2`. -/
theorem bitVal_ne (a b : Bool) : bitVal (a != b) = bitVal a + bitVal b := by
  cases a <;> cases b <;> decide

/-- The value of Boolean parity in `ZMod 2` is the sum of the values of the input bits. -/
theorem bitVal_boolParity {k : ℕ} (v : Reg k) :
    bitVal (boolParity v) = ∑ i, bitVal (v i) := by
  have hs : (∑ i, bitVal (v i)) =
      ((Finset.univ.filter fun i => v i).card : ZMod 2) := by
    simp [bitVal]
  rw [hs, ← ZMod.natCast_mod (Finset.univ.filter fun i => v i).card 2]
  have hm := Nat.mod_lt (Finset.univ.filter fun i => v i).card (by omega : 0 < 2)
  interval_cases h : (Finset.univ.filter fun i => v i).card % 2 <;>
    simp [boolParity, bitVal, h]

/-- The standard additive character of a Boolean value is one for false and minus one for true. -/
theorem bit_character (b : Bool) :
    ZMod.stdAddChar (bitVal b) = (if b then (-1 : ℂ) else 1) := by
  cases b <;> simp [bitVal,
    Qatlib.Papers.SingleQuery97.MainResults.FourierLayers.binary_character_one]

/-- The binary character equals the standard additive character evaluated at the binary dot
product. -/
theorem binaryCharacter_dot {k : ℕ} (c v : Reg k) :
    binaryCharacter c v = ZMod.stdAddChar (∑ i, bitVal (c i) * bitVal (v i)) := by
  rw [Qatlib.Papers.SingleQuery97.MainResults.CharacterSum.map_finsetSum_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← bitVal_and, bit_character]

/-- The selected sum of affine output bits splits into the dot product with `recoveredSecret`
and the selected offset sum over `ZMod 2`. -/
theorem affine_selected_sum {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) (x : Reg n) :
    (∑ i, bitVal (c i) * bitVal (affineBit A b i x)) =
      (∑ j, bitVal (recoveredSecret c A j) * bitVal (x j)) +
        ∑ i, bitVal (c i) * bitVal (b i) := by
  simp only [affineBit, recoveredSecret, bitVal_ne, bitVal_boolParity, bitVal_and]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The character of an affine output factors into the offset character and the character of the
recovered secret evaluated on the input. -/
theorem binaryCharacter_affine {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) (x : Reg n) :
    binaryCharacter c (fun i => affineBit A b i x) =
      binaryCharacter c b * binaryCharacter (recoveredSecret c A) x := by
  rw [binaryCharacter_dot, affine_selected_sum, AddChar.map_add_eq_mul,
    ← binaryCharacter_dot, ← binaryCharacter_dot, mul_comm]

/-- Every binary character value has complex norm one. -/
theorem binaryCharacter_norm {m : ℕ} (c b : Reg m) : ‖binaryCharacter c b‖ = 1 := by
  rw [binaryCharacter_dot]
  exact ZMod.stdAddChar.norm_apply (∑ i, bitVal (c i) * bitVal (b i))

/-- The sign determined by `affinePhaseBit` equals the corresponding binary character of the
affine output. -/
theorem affinePhase_character {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) (x : Reg n) :
    (if affinePhaseBit c A b x then (-1 : ℂ) else 1) =
      binaryCharacter c (fun i => affineBit A b i x) := by
  rw [← bit_character, affinePhaseBit, bitVal_boolParity]
  simp only [bitVal_and]
  exact (binaryCharacter_dot _ _).symm

/-- The Hadamard transform of the character-weighted uniform state is the basis state of
`recoveredSecret`, multiplied by the offset character. -/
theorem affine_character_readout {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) :
    ApplyGate (HadamardN n)
      (fun x => binaryCharacter c (fun i => affineBit A b i x) * Uniform (Reg n) x) =
        fun z => binaryCharacter c b * Ket (recoveredSecret c A) z := by
  have hp : (fun x => binaryCharacter c (fun i => affineBit A b i x) * Uniform (Reg n) x) =
      binaryCharacter c b • ApplyGate (HadamardN n) (Ket (recoveredSecret c A)) := by
    rw [← bv_phase_prepares_secret]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [OracleInterfaces.phaseOracle_apply, bv_character_phase, binaryCharacter_affine]
    simp only [binaryCharacter, mul_assoc]
  rw [hp]
  change (HadamardN n).mulVec (binaryCharacter c b • _) = _
  rw [Matrix.mulVec_smul]
  change binaryCharacter c b • ApplyGate (HadamardN n)
    (ApplyGate (HadamardN n) (Ket (recoveredSecret c A))) = _
  rw [← applyGate_mul, bv_hadamard_square, applyGate_one]
  rfl

/-- For every output mask, the phase-oracle circuit prepares the recovered secret basis state up
to a complex scalar of norm one. -/
theorem affine_coefficients_recoverable {n m : ℕ} (A : Fin m → Reg n)
    (b : Reg m) :
    ∀ c : Reg m, ∃ θ : ℂ, ‖θ‖ = 1 ∧
      ApplyGate (HadamardN n)
        (ApplyGate (PhaseOracle (affinePhaseBit c A b))
          (ApplyGate (HadamardN n) (Ket (ZeroStr n))))
      = fun z => θ * (Ket (recoveredSecret c A)) z := by
  intro c
  refine ⟨binaryCharacter c b, binaryCharacter_norm c b, ?_⟩
  rw [applyGate_hadamardN_ket_zero]
  have hp : ApplyGate (PhaseOracle (affinePhaseBit c A b)) (Uniform (Reg n)) =
      fun x => binaryCharacter c (fun i => affineBit A b i x) * Uniform (Reg n) x := by
    funext x
    rw [OracleInterfaces.phaseOracle_apply, affinePhase_character]
  rw [hp]
  exact affine_character_readout A b c

/-- The affine-query circuit consisting of Hadamards on both registers, one output-oracle query,
and Hadamards on the input register. -/
def affineWord (n m : ℕ) : Circuit (Reg n × Reg m) :=
  [Step.gate (TensorGate (HadamardN n) (HadamardN m)), Step.query,
   Step.gate (TensorGate (HadamardN n) 1)]

/-- The affine-query word contains exactly one query and two gate steps. -/
theorem affineWord_resources (n m : ℕ) :
    QueryCount (affineWord n m) = 1 ∧ GateCount (affineWord n m) = 2 := by
  constructor <;> rfl

/-- Every gate step of `affineWord` is unitary. -/
theorem affineWord_unitary (n m : ℕ) : IsUnitaryCircuit (affineWord n m) := by
  simp only [affineWord, isUnitaryCircuit_gate, isUnitaryCircuit_query,
    isUnitaryCircuit_nil, and_true]
  exact ⟨tensorGate_unitary (hadamardN_unitary n) (hadamardN_unitary m),
    tensorGate_unitary (hadamardN_unitary n) (Matrix.unitaryGroup (Reg m) ℂ).one_mem⟩

/-- The affine output-oracle circuit sends the zero input and mask basis state to the recovered
secret with the offset character as a phase, tensored with `outputAnswer c` [CleveEtAl1998]. -/
theorem affineWord_run {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) :
    Run (outputOracle (fun x => fun i => affineBit A b i x)) (affineWord n m)
      (TensorState (Ket (ZeroStr n)) (Ket c)) =
        TensorState (fun z => binaryCharacter c b * Ket (recoveredSecret c A) z)
          (outputAnswer c) := by
  simp only [affineWord, Run, applyGate_tensorGate, applyGate_hadamardN_ket_zero]
  change ApplyGate (TensorGate (HadamardN n) 1)
    (Run (outputOracle (fun x => fun i => affineBit A b i x)) [Step.query]
      (TensorState (Uniform (Reg n)) (outputAnswer c))) = _
  rw [outputOracle_kickback, applyGate_tensorGate, applyGate_one, affine_character_readout]

/-- Measuring the input register of the affine-query output yields `recoveredSecret c A` with
probability one. -/
theorem affineWord_readout {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) :
    MeasureProb
      (Run (outputOracle (fun x => fun i => affineBit A b i x)) (affineWord n m)
        (TensorState (Ket (ZeroStr n)) (Ket c)))
      ({recoveredSecret c A} ×ˢ (Finset.univ : Finset (Reg m))) = 1 := by
  rw [affineWord_run, measureProb_tensorState_left (outputAnswer_normalized c)]
  simp [MeasureProb, BornProb, Qatlib.Foundations.PureStateMath.Ket,
    binaryCharacter_norm]

/-- The output of the affine-query circuit on the specified basis-state input is normalized. -/
theorem affineWord_normalized {n m : ℕ} (A : Fin m → Reg n) (b c : Reg m) :
    Normalized
      (Run (outputOracle (fun x => fun i => affineBit A b i x)) (affineWord n m)
        (TensorState (Ket (ZeroStr n)) (Ket c))) :=
  (affineWord_unitary n m).normalized_run (outputOracle_unitary _)
    (normalized_tensorState (normalized_ket _) (normalized_ket _))

/-- The Boolean mask selecting exactly the coordinate `i`. -/
def rowSelector {m : ℕ} (i : Fin m) : Reg m := fun j => decide (j = i)

/-- Selecting a single row makes the recovered secret equal that row of `A`. -/
theorem recoveredSecret_row {n m : ℕ} (A : Fin m → Reg n) (i : Fin m) :
    recoveredSecret (rowSelector i) A = A i := by
  funext j
  have hi : Function.Injective bitVal := by decide
  apply hi
  rw [recoveredSecret, bitVal_boolParity]
  simp only [bitVal_and]
  have hsel (k : Fin m) : bitVal (rowSelector i k) = if k = i then 1 else 0 := by
    simp [bitVal, rowSelector]
  simp_rw [hsel, ite_mul, one_mul, zero_mul]
  simp

/-- Each row of the affine matrix is measured with probability one using its row selector, and
the total query count of the `m` runs is `m` [Cleve et al., Section 3][CleveEtAl1998]. -/
theorem affine_all_rows {n m : ℕ} (A : Fin m → Reg n) (b : Reg m) :
    (∀ i : Fin m,
      MeasureProb
        (Run (outputOracle (fun x => fun j => affineBit A b j x)) (affineWord n m)
          (TensorState (Ket (ZeroStr n)) (Ket (rowSelector i))))
        ({A i} ×ˢ (Finset.univ : Finset (Reg m))) = 1) ∧
      (∑ _ : Fin m, QueryCount (affineWord n m)) = m := by
  constructor
  · intro i
    simpa only [recoveredSecret_row] using affineWord_readout A b (rowSelector i)
  · simp [(affineWord_resources n m).1]

end Qatlib.Papers.QAlgorithms97.MainResults.AffineCoefficients
