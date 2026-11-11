/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.MixturePaths
import Qatlib.Concepts.ClusterPatterns.WireComposition.PauliMixtureTwirling

/-!
# Phase perturbations of Hadamard channel mixtures

Defines `noisyHadamardChoice`, the fair mixture of the identity and a phase-perturbed Hadamard
gate. It computes the average access distance from the unperturbed mixture and bounds the
accumulated trace-norm error of repeated applications, including applications to one half of a
Bell state.

The module also provides explicit output matrices that distinguish the perturbed and unperturbed
channels. The channel and trace-distance background is described in [NielsenChuang2010].

## Main statements

* `noisy_hadamard_mixture_data`: unitarity and the exact access distance.
* `noisy_hadamard_mixture_counted_error`: repeated-channel error and circuit counts.
* `noisy_hadamard_mixture_concrete_and_entangled`: concrete outputs and a Bell-state error
  bound.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The qubit diagonal matrix with diagonal entries `1` and `ζ`. -/
noncomputable def noisyHadamardPhase (ζ : ℂ) : Operator 2 :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else ζ)

/-- Selects the identity for `false` and the phase matrix times the Hadamard gate for `true`. -/
noncomputable def noisyHadamardChoice (ζ : ℂ) : Bool → Operator 2
  | false => 1
  | true => noisyHadamardPhase ζ * relabelGate boolEquivFin2 Hadamard

/-- The two-qubit Bell vector with amplitude `1 / sqrt 2` on equal basis labels and zero
elsewhere. -/
noncomputable def noisyMixtureBell : QState (Fin 2 × Fin 2) :=
  fun p => if p.1 = p.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- Relabeling both matrix indices commutes with conjugate transpose. -/
private lemma relabel_star {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (U : Matrix I I ℂ) : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.conjTranspose_apply]

/-- Relabeling both indices preserves the identity matrix. -/
private lemma relabel_one {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.one_apply]

/-- Relabeling both indices preserves matrix multiplication. -/
private lemma relabel_mul {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (U V : Matrix I I ℂ) :
    relabelGate e U * relabelGate e V = relabelGate e (U * V) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Equiv.sum_comp e.symm (fun k : I => U (e.symm i) k * V k (e.symm j))]

/-- Relabeling both indices by an equivalence preserves unitarity. -/
private lemma relabel_unitary' {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have h : Uᴴ * U = 1 := by
    have h' := (Matrix.mem_unitaryGroup_iff'.mp hU)
    rwa [Matrix.star_eq_conjTranspose] at h'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, relabel_star, relabel_mul, h,
    relabel_one]

/-- The product of two unitary operators is unitary. -/
private lemma unitary_mul' {D : ℕ} {M N : Operator D}
    (hM : M ∈ Matrix.unitaryGroup (Fin D) ℂ) (hN : N ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    M * N ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  have hM' : Mᴴ * M = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.mp hM)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hN' : Nᴴ * N = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.mp hN)
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.mul_assoc (N)ᴴ (M)ᴴ (M * N), ← Matrix.mul_assoc (M)ᴴ M N, hM',
    Matrix.one_mul, hN']

/-- The phase matrix is unitary when `ζ` has norm one. -/
private lemma noisyHadamardPhase_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    noisyHadamardPhase ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hzz : ζ * (starRingEnd ℂ) ζ = 1 := by
    have hn : Complex.normSq ζ = 1 := by
      rw [← Complex.norm_mul_self_eq_normSq, ← sq, hζ, one_pow]
    rw [mul_comm ζ (starRingEnd ℂ ζ), ← Complex.normSq_eq_conj_mul_self, hn,
      Complex.ofReal_one]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, noisyHadamardPhase]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    Matrix.one_apply, map_mul, map_one, map_zero]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, hzz]

/-- Right multiplication by a unitary preserves the matrix norm used in this module. -/
private lemma l2_norm_mul_unitary_eq {D : ℕ} (A : Operator D) {H : Operator D}
    (hH : H ∈ Matrix.unitaryGroup (Fin D) ℂ) : ‖A * H‖ = ‖A‖ := by
  have hHH : H * Hᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff.mp hH)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hnormH : ‖H‖ ≤ 1 := l2_norm_unitary_le_one hH
  have hnormHc : ‖Hᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hnormH
  refine le_antisymm ?_ ?_
  · calc ‖A * H‖ ≤ ‖A‖ * ‖H‖ := Matrix.l2_opNorm_mul A H
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hnormH (norm_nonneg _)
    _ = ‖A‖ := mul_one _
  calc ‖A‖ = ‖A * (H * Hᴴ)‖ := by rw [hHH, Matrix.mul_one]
    _ = ‖(A * H) * Hᴴ‖ := by rw [← Matrix.mul_assoc]
    _ ≤ ‖A * H‖ * ‖Hᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖A * H‖ * 1 := mul_le_mul_of_nonneg_left hnormHc (norm_nonneg _)
    _ = ‖A * H‖ := mul_one _

/-- Subtracting the identity from the phase matrix gives the diagonal matrix with entries zero
and `ζ - 1`. -/
private lemma phase_sub_one (ζ : ℂ) :
    noisyHadamardPhase ζ - 1
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (0 : ℂ) else ζ - 1) := by
  ext i j
  simp only [noisyHadamardPhase, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- The norm of the qubit diagonal matrix with entries zero and `c` equals the complex norm of
`c`. -/
private lemma norm_diag01 (c : ℂ) :
    ‖(Matrix.diagonal (fun i : Fin 2 => if i = 0 then (0 : ℂ) else c) : Operator 2)‖ = ‖c‖ := by
  set D : Operator 2 := Matrix.diagonal (fun i : Fin 2 => if i = 0 then (0 : ℂ) else c) with hD
  have hc1 : (if (0 : Fin 2) = 0 then (0 : ℂ) else c) = 0 := by simp
  have hc2 : (if (1 : Fin 2) = 0 then (0 : ℂ) else c) = c := by simp
  have h0 : (if (0 : Fin 2) = 0 then (0 : ℂ) else c) = 0 := hc1
  have hact : ∀ v : QState (Fin 2), D *ᵥ v = fun i => (if i = 0 then (0 : ℂ) else c) * v i := by
    intro v
    funext i
    rw [hD]
    exact Matrix.mulVec_diagonal _ _ _
  have hsq : ∀ v : QState (Fin 2),
      ‖toEuclidean_fromVec (D *ᵥ v)‖ ^ 2 ≤ ‖c‖ ^ 2 * ‖toEuclidean_fromVec v‖ ^ 2 := by
    intro v
    have hcalc : ‖toEuclidean_fromVec (D *ᵥ v)‖ ^ 2 = ‖c‖ ^ 2 * ‖v 1‖ ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq, hact, Fin.sum_univ_two]
      have e0 : ‖((fun i : Fin 2 => (if i = 0 then (0 : ℂ) else c) * v i) 0)‖ ^ 2 = 0 := by
        simp
      have e1 : ‖((fun i : Fin 2 => (if i = 0 then (0 : ℂ) else c) * v i) 1)‖ ^ 2
          = ‖c‖ ^ 2 * ‖v 1‖ ^ 2 := by
        have hval : (fun i : Fin 2 => (if i = 0 then (0 : ℂ) else c) * v i) 1 = c * v 1 := by
          simp
        rw [hval, norm_mul, mul_pow]
      rw [e0, e1, zero_add]
    rw [hcalc, norm_toEuclidean_fromVec_sq, Fin.sum_univ_two]
    have hsingle : ‖v 1‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg (‖v 0‖))
    exact mul_le_mul_of_nonneg_left hsingle (sq_nonneg ‖c‖)
  refine le_antisymm ?_ ?_
  · refine l2_opNorm_le_of_mulVec_le (norm_nonneg c) _ fun v => ?_
    have hkey := hsq v
    have hrew : ‖c‖ ^ 2 * ‖toEuclidean_fromVec v‖ ^ 2
        = (‖c‖ * ‖toEuclidean_fromVec v‖) ^ 2 := by ring
    rw [hrew] at hkey
    calc ‖toEuclidean_fromVec (D *ᵥ v)‖
        = Real.sqrt (‖toEuclidean_fromVec (D *ᵥ v)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((‖c‖ * ‖toEuclidean_fromVec v‖) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = ‖c‖ * ‖toEuclidean_fromVec v‖ :=
          Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · have hbound := l2_norm_mulVec_fromVec_le D (Ket 1)
    have hketnorm : ‖toEuclidean_fromVec (Ket (1 : Fin 2))‖ = 1 := by
      have h2 : ‖toEuclidean_fromVec (Ket (1 : Fin 2))‖ ^ 2 = 1 := by
        rw [norm_toEuclidean_fromVec_sq]
        simp [Qatlib.Foundations.PureStateMath.Ket]
      calc ‖toEuclidean_fromVec (Ket (1 : Fin 2))‖
          = Real.sqrt (‖toEuclidean_fromVec (Ket (1 : Fin 2))‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt 1 := by rw [h2]
        _ = 1 := Real.sqrt_one
    have hvecnorm : ‖toEuclidean_fromVec (D *ᵥ (Ket (1 : Fin 2)))‖ = ‖c‖ := by
      have h2 : ‖toEuclidean_fromVec (D *ᵥ (Ket (1 : Fin 2)))‖ ^ 2 = ‖c‖ ^ 2 := by
        rw [norm_toEuclidean_fromVec_sq, hact]
        simp only [Qatlib.Foundations.PureStateMath.Ket, Fin.isValue, h0, norm_zero, zero_add, hc2]
        simp
      calc ‖toEuclidean_fromVec (D *ᵥ (Ket (1 : Fin 2)))‖
          = Real.sqrt (‖toEuclidean_fromVec (D *ᵥ (Ket (1 : Fin 2)))‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (‖c‖ ^ 2) := by rw [h2]
        _ = ‖c‖ := Real.sqrt_sq (norm_nonneg _)
    rw [hketnorm, hvecnorm, mul_one] at hbound
    exact hbound

/-- The norm of the phase matrix minus the identity equals `‖ζ - 1‖`. -/
private lemma phase_sub_one_norm (ζ : ℂ) :
    ‖noisyHadamardPhase ζ - 1‖ = ‖ζ - 1‖ := by
  rw [phase_sub_one, norm_diag01]

/-- For unit-norm `ζ`, both selected gates are unitary and the access distance from the
unperturbed fair mixture is `‖ζ - 1‖ / 2`. -/
theorem noisy_hadamard_mixture_data (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∀ b : Bool, noisyHadamardChoice ζ b ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
    mixtureAccessDistance pauliFairBit (noisyHadamardChoice ζ) (noisyHadamardChoice 1)
      = ‖ζ - 1‖ / 2 := by
  have hH : relabelGate boolEquivFin2 Hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    relabel_unitary' boolEquivFin2 hadamard_unitary
  refine ⟨?_, ?_⟩
  · intro b
    cases b with
    | false => exact one_unitary
    | true => exact unitary_mul' (noisyHadamardPhase_unitary hζ) hH
  · have hphase1 : noisyHadamardPhase 1 = 1 := by
      ext i j
      simp only [noisyHadamardPhase, Matrix.diagonal_apply, Matrix.one_apply]
      fin_cases i <;> fin_cases j <;> simp
    have htrue : ‖noisyHadamardChoice ζ true - noisyHadamardChoice 1 true‖ = ‖ζ - 1‖ := by
      show ‖noisyHadamardPhase ζ * relabelGate boolEquivFin2 Hadamard
          - noisyHadamardPhase 1 * relabelGate boolEquivFin2 Hadamard‖ = _
      rw [hphase1, Matrix.one_mul]
      rw [show noisyHadamardPhase ζ * relabelGate boolEquivFin2 Hadamard
            - relabelGate boolEquivFin2 Hadamard
            = (noisyHadamardPhase ζ - 1) * relabelGate boolEquivFin2 Hadamard from by
          rw [Matrix.sub_mul, Matrix.one_mul]]
      rw [l2_norm_mul_unitary_eq _ hH, phase_sub_one_norm]
    have hfalse : ‖noisyHadamardChoice ζ false - noisyHadamardChoice 1 false‖ = 0 := by
      simp [noisyHadamardChoice]
    rw [mixtureAccessDistance]
    simp only [pauliFairBit_prob, Fintype.sum_bool, htrue, hfalse, norm_zero, mul_zero,
      add_zero, mul_comm ((1 : ℝ) / 2) ‖ζ - 1‖, mul_one_div]

/-- Multiplying two complex factors of one half and then `z` equals one quarter times `z`. -/
private lemma inv2_mul_inv2 {z : ℂ} (h : z = z) : (2⁻¹ : ℂ) * 2⁻¹ * z = 4⁻¹ * z := by
  have hnum : (2⁻¹ : ℂ) * 2⁻¹ = 4⁻¹ := by norm_num
  rw [hnum]

/-- Multiplying `z` by the product of two complex factors of one half equals `z` times one
quarter. -/
private lemma inv2_mul_inv2' (z : ℂ) : z * ((2⁻¹ : ℂ) * 2⁻¹) = z * 4⁻¹ := by
  have hnum : (2⁻¹ : ℂ) * 2⁻¹ = 4⁻¹ := by norm_num
  rw [hnum]

/-- The product of two complex factors of one half is one quarter. -/
private lemma inv2_mul_inv2_eq : (2⁻¹ : ℂ) * 2⁻¹ = 4⁻¹ := by norm_num

/-- The square of the complex inverse of `sqrt 2` equals the complex embedding of one half. -/
private lemma sqrt2_inv_pow2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = ((1 / 2 : ℝ) : ℂ) := by
  rw [inv_pow, sqrt2_sq]
  push_cast [Complex.ofReal_div]
  norm_num

/-- The product of two complex-embedded real halves equals the complex embedding of one quarter. -/
private lemma inv2_inv2_real : ((1/2 : ℝ) : ℂ) * ((1/2 : ℝ) : ℂ) = ((1/4 : ℝ) : ℂ) := by
  push_cast
  norm_num

/-- For unit-norm `ζ`, the trace-norm error after `n` reference-extended mixture steps is at
most `n * ‖ζ - 1‖` times the input trace norm. Every length-`n` path circuit has zero
queries and `n` gates. -/
theorem noisy_hadamard_mixture_counted_error (ζ : ℂ) (n r : ℕ)
    (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (hζ : ‖ζ‖ = 1) :
    Matrix.traceNorm (referenceMixturePower pauliFairBit (noisyHadamardChoice ζ) r n ρ -
      referenceMixturePower pauliFairBit (noisyHadamardChoice 1) r n ρ) ≤
      (n : ℝ) * ‖ζ - 1‖ * Matrix.traceNorm ρ ∧
    (∀ ω : Fin n → Bool, QueryCount (mixturePathCircuit (noisyHadamardChoice ζ) ω) = 0 ∧
      GateCount (mixturePathCircuit (noisyHadamardChoice ζ) ω) = n) := by
  have h1ζ : ‖(1 : ℂ)‖ = 1 := by norm_num
  have hunitζ := (noisy_hadamard_mixture_data ζ hζ).1
  have hunit1 := (noisy_hadamard_mixture_data 1 h1ζ).1
  have hdist := (noisy_hadamard_mixture_data ζ hζ).2
  constructor
  · have hbound := finite_reference_iterated_mixture_error pauliFairBit
      (noisyHadamardChoice ζ) (noisyHadamardChoice 1) r n ρ hunitζ hunit1
    rw [hdist] at hbound
    have hEq : 2 * (n : ℝ) * (‖ζ - 1‖ / 2) * Matrix.traceNorm ρ
        = (n : ℝ) * ‖ζ - 1‖ * Matrix.traceNorm ρ := by ring
    rw [← hEq]
    exact hbound
  · intro ω
    have h := mixture_path_circuit_semantics_cost (noisyHadamardChoice ζ) n ω
      (Ket (0 : Fin 2))
    exact ⟨h.2.1, h.2.2.1⟩

/-- The product of two complex inverses of `sqrt 2` equals the complex embedding of one half. -/
private lemma inv_sqrt2_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
    = ((1 / 2 : ℝ) : ℂ) := by
  rw [← pow_two, inv_pow, sqrt2_sq]
  norm_num

/-- The unperturbed fair mixture sends the zero-basis pure state to the matrix with diagonal
entries `3/4`, `1/4` and off-diagonal entries `1/4`. -/
private lemma noisy_hadamard_mixture_one :
    ChannelMixture pauliFairBit (noisyHadamardChoice 1) (outerProduct (Ket (0 : Fin 2)))
      = !![3/4, 1/4; 1/4, 1/4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChannelMixture, Fintype.sum_bool, pauliFairBit_prob, noisyHadamardChoice,
      noisyHadamardPhase, relabelGate, Matrix.reindex_apply, boolEquivFin2, Hadamard,
      outerProduct, Qatlib.Foundations.PureStateMath.Ket, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.conj_ofReal]
  all_goals try rw [inv_sqrt2_sq]
  all_goals push_cast
  all_goals norm_num

/-- Computes the phase-`I` mixture output on the zero-basis state and proves it differs from the
unperturbed output. It also bounds the repeated-channel error on a Bell input by `n * ‖ζ -
1‖` for unit-norm `ζ`. -/
theorem noisy_hadamard_mixture_concrete_and_entangled :
    ChannelMixture pauliFairBit (noisyHadamardChoice Complex.I) (outerProduct (Ket (0 : Fin 2)))
      = !![3/4, -Complex.I/4; Complex.I/4, 1/4] ∧
    ChannelMixture pauliFairBit (noisyHadamardChoice Complex.I) (outerProduct (Ket (0 : Fin 2))) ≠
      ChannelMixture pauliFairBit (noisyHadamardChoice 1) (outerProduct (Ket (0 : Fin 2))) ∧
    (∀ (ζ : ℂ) (n : ℕ), ‖ζ‖ = 1 →
      Matrix.traceNorm (referenceMixturePower pauliFairBit (noisyHadamardChoice ζ) 2 n
          (outerProduct noisyMixtureBell) -
        referenceMixturePower pauliFairBit (noisyHadamardChoice 1) 2 n
          (outerProduct noisyMixtureBell)) ≤ (n : ℝ) * ‖ζ - 1‖) := by
  have hI : ‖(Complex.I : ℂ)‖ = 1 := by norm_num
  have h1ζ : ‖(1 : ℂ)‖ = 1 := by norm_num
  have hunitI := (noisy_hadamard_mixture_data Complex.I hI).1
  have hunit1 := (noisy_hadamard_mixture_data 1 h1ζ).1
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ChannelMixture, Fintype.sum_bool, pauliFairBit_prob, noisyHadamardChoice,
        noisyHadamardPhase, relabelGate, Matrix.reindex_apply, boolEquivFin2, Hadamard,
        outerProduct, Qatlib.Foundations.PureStateMath.Ket, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.conj_ofReal, Complex.conj_I]
    all_goals try rw [inv_sqrt2_sq]
    all_goals try ring_nf
    all_goals try rw [sqrt2_inv_pow2]
    all_goals push_cast
    all_goals try norm_num
    all_goals try ring_nf
    all_goals try norm_num
  · intro h
    have hL : ChannelMixture pauliFairBit (noisyHadamardChoice Complex.I)
        (outerProduct (Ket (0 : Fin 2))) 0 1 = -Complex.I / 4 := by
      simp [ChannelMixture, Fintype.sum_bool, pauliFairBit_prob, noisyHadamardChoice,
        noisyHadamardPhase, relabelGate, Matrix.reindex_apply, boolEquivFin2, Hadamard,
        outerProduct, Qatlib.Foundations.PureStateMath.Ket, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.conj_ofReal, Complex.conj_I]
      try rw [inv_sqrt2_sq]
      try ring_nf
      try rw [sqrt2_inv_pow2]
      push_cast
      try norm_num
      try ring_nf
    have hR : ChannelMixture pauliFairBit (noisyHadamardChoice 1)
        (outerProduct (Ket (0 : Fin 2))) 0 1 = 1 / 4 := by
      rw [noisy_hadamard_mixture_one]
      simp [Matrix.of_apply]
    have h01 := Matrix.ext_iff.mpr h 0 1
    rw [hL, hR] at h01
    have hcomp := Complex.ext_iff.mp h01
    norm_num at hcomp

  · intro ζ n hζ
    have hbound := (noisy_hadamard_mixture_counted_error ζ n 2
      (outerProduct noisyMixtureBell) hζ).1
    have hnorm2 : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = 1 / 2 := by
      have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hbell : Normalized noisyMixtureBell := by
      show ∑ p : Fin 2 × Fin 2, ‖noisyMixtureBell p‖ ^ 2 = 1
      rw [Fintype.sum_prod_type]
      simp only [noisyMixtureBell, Fin.isValue, Fin.sum_univ_two, hnorm2]
      norm_num
    have htr : Matrix.traceNorm (outerProduct noisyMixtureBell) = 1 := by
      have hpsd := (outerProduct_density hbell).1
      have htr1 := (outerProduct_density hbell).2
      have h1' := Matrix.PosSemidef.traceNorm_eq_trace hpsd
      rw [htr1, ← Complex.ofReal_one] at h1'
      exact Complex.ofReal_injective h1'
    rw [htr] at hbound
    rw [mul_one] at hbound
    exact hbound

end Qatlib.Concepts.MbqcFlow.FlowDecision
