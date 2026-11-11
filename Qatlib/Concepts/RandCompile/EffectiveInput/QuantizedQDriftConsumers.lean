/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift

/-!
# A signed Pauli example of quantized qDRIFT

This module specializes signed dyadic coefficient quantization to the target `(1/3) X - (2/3)
Z`. At precision two the rounded generator is `(1/4) X - (3/4) Z`, with sampling weights one and
three. The example instantiates the qDRIFT simulation framework of [Campbell2019] with explicit
ancillary trace-norm and path-resource bounds.

## Main statements

* `quantized_signed_xz_actual_consumer`: computes the signed digits and sampling weights.
* `quantized_signed_xz_reference_error`: bounds the simulation error for the Pauli target.
* `quantized_signed_xz_path_ledger`: counts gates, fair bits, and comparisons on each sampled
  path.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.RandCompile.FairBitSampling

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RandCompile.EffectiveInput
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The rational coefficient pair `1/3` and `-2/3` for the Pauli example. -/
def quantizedXZCoefficients : Fin 2 → ℚ := fun j => if j=0 then 1/3 else -2/3

/-- The real coefficient pair `1/3` and `-2/3` defining the target Hamiltonian. -/
noncomputable def quantizedXZTargetCoefficients : Fin 2 → ℝ := fun j => if j=0 then 1/3 else -2/3

/-- The pair of Pauli operators `pauliX` and `pauliZ`. -/
def quantizedXZTerms : Fin 2 → Operator 2 := fun j => if j=0 then pauliX else pauliZ

/-- The target Hamiltonian `(1/3) X - (2/3) Z`. -/
noncomputable def quantizedXZTarget : Operator 2 :=
  (1/3 : ℂ) • pauliX + (-2/3 : ℂ) • pauliZ

/-- The rounded Hamiltonian `(1/4) X - (3/4) Z` at dyadic precision two. -/
noncomputable def quantizedXZGenerator : Operator 2 :=
  (1/4 : ℂ) • pauliX + (-3/4 : ℂ) • pauliZ

/-- At precision two, the coefficients `1/3` and `-2/3` give signed digits one and minus three,
sampling weights one and three, and total weight four. -/
theorem quantized_signed_xz_actual_consumer :
    let a : Fin 2 → ℚ := fun j => if j=0 then 1/3 else -2/3
    dyadicCoefficient 2 (a 0)=1 ∧ dyadicCoefficient 2 (a 1)= -3 ∧
      dyadicWeights 2 a 0=1 ∧ dyadicWeights 2 a 1=3 ∧ weightTotal (dyadicWeights 2 a)=4 := by
  norm_num [dyadicCoefficient, dyadicWeights, weightTotal, Fin.sum_univ_two]

/-- Both terms of the Pauli example are Hermitian contractions. -/
private theorem quantized_pauli_contract :
    ∀ j, (quantizedXZTerms j).IsHermitian ∧ ‖quantizedXZTerms j‖ ≤ 1 := by
  intro j
  have hx : pauliX.IsHermitian := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [pauliX, Matrix.conjTranspose_apply]
  have hz : pauliZ.IsHermitian := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [pauliZ, Matrix.conjTranspose_apply]
  unfold quantizedXZTerms
  split_ifs
  · refine ⟨hx, l2_norm_unitary_le_one ?_⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hx.eq]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨hz, l2_norm_unitary_le_one ?_⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hz.eq]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The real coefficient sum over the Pauli terms equals `quantizedXZTarget`. -/
theorem quantizedXZ_target_eq :
    (∑ j, (quantizedXZTargetCoefficients j : ℂ) • quantizedXZTerms j) = quantizedXZTarget := by
  ext i j
  simp [Fin.sum_univ_two, quantizedXZTargetCoefficients, quantizedXZTerms, quantizedXZTarget,
    Matrix.smul_apply]

/-- The decoded precision-two dyadic coefficient sum over the Pauli terms equals
`quantizedXZGenerator`. -/
theorem quantizedXZ_generator_eq :
    (∑ j, ((dyadicCoefficient 2 (quantizedXZCoefficients j) : ℂ)/(2 : ℂ)^2) •
      quantizedXZTerms j) = quantizedXZGenerator := by
  norm_num [Fin.sum_univ_two, quantizedXZCoefficients, quantizedXZTerms,
    quantizedXZGenerator, dyadicCoefficient]

/-- For positive step count, the ancillary trace-norm error relative to the Pauli target is at
most `(4 * t^2 / n + 2 * n * (1/2)^R + |t| / 2)` times the input trace norm. -/
theorem quantized_signed_xz_reference_error (n R r : ℕ) (t : ℝ)
    (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (hn : 0 < n) :
    Matrix.traceNorm (quantizedQdriftOutput 2 quantizedXZCoefficients 0 n R quantizedXZTerms t r X-
      TensorGate (HamiltonianEvolution quantizedXZTarget t) (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution quantizedXZTarget t) (1 : Operator r))ᴴ) ≤
      (4*t^2/(n : ℝ)+2*n*(1/2 : ℝ)^R+|t|/2)*Matrix.traceNorm X := by
  have hw : weightTotal (dyadicWeights 2 quantizedXZCoefficients)=4 :=
    quantized_signed_xz_actual_consumer.2.2.2.2
  have ha : (∑ j, |quantizedXZTargetCoefficients j-(quantizedXZCoefficients j : ℝ)|) ≤ 0 := by
    norm_num [Fin.sum_univ_two, quantizedXZTargetCoefficients, quantizedXZCoefficients]
  have he := quantized_qdrift_actual_reference_error 2 2 2 n R r quantizedXZCoefficients
    quantizedXZTargetCoefficients 0 quantizedXZTerms t 0 X hn (by omega) quantized_pauli_contract ha
  rw [quantizedXZ_target_eq, hw] at he
  convert he using 1
  ring

/-- Every sampled circuit for the rounded Pauli example is unitary, uses zero oracle queries and
`n` gates, and has both fair-bit and comparison counts at most `2 * n * R`. -/
theorem quantized_signed_xz_path_ledger (n R : ℕ) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights 2 quantizedXZCoefficients)))) :
    let w := dyadicWeights 2 quantizedXZCoefficients
    let K := dyadicSignedTerms 2 quantizedXZCoefficients quantizedXZTerms
    IsUnitaryCircuit (fairQdriftCircuit w 0 n R K (t/4) ω) ∧
      QueryCount (fairQdriftCircuit w 0 n R K (t/4) ω)=0 ∧
      GateCount (fairQdriftCircuit w 0 n R K (t/4) ω)=n ∧
      (∑ k, (fairQdriftPick w 0 R (ω k)).2.1) ≤ n*2*R ∧
      (∑ k, (fairQdriftPick w 0 R (ω k)).2.2) ≤ n*2*R := by
  have hw : weightTotal (dyadicWeights 2 quantizedXZCoefficients)=4 :=
    quantized_signed_xz_actual_consumer.2.2.2.2
  have he := fair_bit_qdrift_actual_quantum_and_classical_path_counts 2 2 n R
    (dyadicWeights 2 quantizedXZCoefficients) 0
    (dyadicSignedTerms 2 quantizedXZCoefficients quantizedXZTerms) (t/4) ω (by omega)
    (fun j => (dyadicSignedTerms_contract 2 quantizedXZCoefficients quantizedXZTerms
      quantized_pauli_contract j).1)
  simpa only [hw, show Nat.clog 2 4=2 from by decide] using he
end Qatlib.Concepts.RandCompile.EffectiveInput
