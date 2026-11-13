/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.LowRankHHL.LowRankOffGridHHL

/-!
# An inconsistent low-rank HHL example

This module constructs a three-dimensional HHL example with spectrum zero, 1/10, and -1/8 and a
preparation mixing the first two basis states equally. The prepared right-hand side is
inconsistent, while its pseudoinverse solution points along basis state one.
`low_rank_uniform_hhl_inconsistent_actual_consumer` gives a success probability of at least
1/4096 and an explicit conditional-state error bound on every computed grid; the pure zero-mode
input has zero success probability.

The example uses the spectral-inversion and success-flag viewpoint of the HHL linear-systems
algorithm [HarrowHassidimLloyd2009].

## Main statements

* `lowRankExample_inverse`: Computes the pseudoinverse solution for the prepared input.
* `lowRankExample_target`: Identifies the embedded normalized solution target.
* `low_rank_uniform_hhl_inconsistent_actual_consumer`: Proves concrete success and error
  guarantees for the inconsistent example.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

namespace Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The three-dimensional spectrum with values zero at index zero, `1 / 10` at index one, and
`-1 / 8` at index two. -/
noncomputable def lowRankExampleSpectrum (i : Fin 3) : ℝ :=
    if i=0 then 0 else if i=1 then 1/10 else -1/8

/-- The three-dimensional unitary preparation matrix acting as a Hadamard matrix on the first
two coordinates and fixing the third. -/
noncomputable def lowRankExamplePrepare : Operator 3 :=
  !![(Real.sqrt 2:ℂ)⁻¹,(Real.sqrt 2:ℂ)⁻¹,0;
     (Real.sqrt 2:ℂ)⁻¹,-(Real.sqrt 2:ℂ)⁻¹,0;0,0,1]

/-- The element of `Fin 3` constructed from the value two equals the numeral two. -/
private theorem lowRank_fin_three_mk_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := rfl

/-- The elements zero and two of `Fin 3` are distinct. -/
private theorem lowRank_fin_three_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

/-- The elements two and zero of `Fin 3` are distinct. -/
private theorem lowRank_fin_three_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide

/-- The elements two and one of `Fin 3` are distinct. -/
private theorem lowRank_fin_three_two_ne_one : (2 : Fin 3) ≠ 1 := by decide

/-- The elements one and two of `Fin 3` are distinct. -/
private theorem lowRank_fin_three_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

/-- The example preparation matrix is unitary. -/
theorem lowRankExamplePrepare_unitary : lowRankExamplePrepare ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ha : (Real.sqrt 2:ℂ)⁻¹*(Real.sqrt 2:ℂ)⁻¹ = (1/2:ℂ) := by
    rw [← _root_.mul_inv_rev, ← pow_two, hs]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowRankExamplePrepare, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ha]

/-- Every eigenvalue of the example spectrum is either zero or has absolute value between `1 /
16` and `1 / 4`. -/
theorem lowRankExample_promise : ∀ i : Fin 3,
    lowRankExampleSpectrum i=0 ∨ ((1/16:ℝ) ≤ |lowRankExampleSpectrum i| ∧ |lowRankExampleSpectrum i| ≤ 1/4) := by
  intro i
  fin_cases i <;> norm_num [lowRankExampleSpectrum]

/-- The prepared basis-zero input has amplitude `1 / Real.sqrt 2` on indices zero and one and
zero on index two. -/
theorem lowRankExample_input : lowRankExamplePrepare *ᵥ Ket (0:Fin 3) =
    fun i : Fin 3 => if i=2 then 0 else (Real.sqrt 2:ℂ)⁻¹ := by
  funext i
  fin_cases i <;> norm_num [lowRankExamplePrepare, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Ket, lowRank_fin_three_mk_two, lowRank_fin_three_zero_ne_two, lowRank_fin_three_one_ne_two, lowRank_fin_three_two_ne_zero, lowRank_fin_three_two_ne_one]

/-- The pseudoinverse of the example HHL matrix sends the prepared input to `(10 / Real.sqrt 2)
• Ket 1`. -/
theorem lowRankExample_inverse :
    matrixPseudoinverse (continuousHHLMatrix lowRankExampleSpectrum (1 : Operator 3)) *ᵥ
      (lowRankExamplePrepare *ᵥ Ket 0) = ((10/Real.sqrt 2:ℝ):ℂ) • Ket (1:Fin 3) := by
  rw [(singular_hermitian_pseudoinverse_and_least_squares 3 lowRankExampleSpectrum 1 (Submonoid.one_mem _)).1]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, lowRankExample_input]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal, lowRankExampleSpectrum, Ket, lowRank_fin_three_mk_two, lowRank_fin_three_zero_ne_two, lowRank_fin_three_one_ne_two, lowRank_fin_three_two_ne_zero, lowRank_fin_three_two_ne_one, div_eq_mul_inv]

/-- The range projector of the example HHL matrix sends the prepared input to `(1 / Real.sqrt 2)
• Ket 1`. -/
theorem lowRankExample_range :
    (continuousHHLMatrix lowRankExampleSpectrum (1 : Operator 3)*
      matrixPseudoinverse (continuousHHLMatrix lowRankExampleSpectrum (1 : Operator 3))) *ᵥ
      (lowRankExamplePrepare *ᵥ Ket 0) = ((1/Real.sqrt 2:ℝ):ℂ) • Ket (1:Fin 3) := by
  rw [(singular_hermitian_pseudoinverse_and_least_squares 3 lowRankExampleSpectrum 1 (Submonoid.one_mem _)).2.1]
  simp only [spectralSupport, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
      lowRankExample_input]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal, lowRankExampleSpectrum, Ket, lowRank_fin_three_mk_two, lowRank_fin_three_zero_ne_two, lowRank_fin_three_one_ne_two, lowRank_fin_three_two_ne_zero, lowRank_fin_three_two_ne_one, div_eq_mul_inv]

/-- The least-squares overlap of the example matrix and prepared input is at least `1 / 2`. -/
theorem lowRankExample_overlap :
    (1/2:ℝ) ≤ leastSquaresOverlap (continuousHHLMatrix lowRankExampleSpectrum (1 : Operator 3))
      (lowRankExamplePrepare *ᵥ Ket 0) := by
  rw [leastSquaresOverlap, lowRankExample_range]
  change (1/2:ℝ) ≤ ‖((1/Real.sqrt 2:ℝ):ℂ) • stateVector (Ket (1:Fin 3))‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    (normalized_iff_stateVector_norm _).mp (normalized_ket _), mul_one]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- For every grid size at least two, the example's normalized HHL solution target is the
success embedding of `Ket 1`. -/
theorem lowRankExample_target (M : ℕ) (hM : 2 ≤ M) :
    uniformHHLSolutionTarget M hM lowRankExampleSpectrum (1 : Operator 3) lowRankExamplePrepare 0 =
      uniformHHLSuccessEmbed M hM (Ket (1:Fin 3)) := by
  unfold uniformHHLSolutionTarget
  rw [lowRankExample_inverse]
  (try dsimp only)
  have hs : 0 < (10/Real.sqrt 2:ℝ) := by positivity
  have hn : ‖toEuclidean_fromVec (((10/Real.sqrt 2:ℝ):ℂ) • (Ket (1:Fin 3)))‖ = 10/Real.sqrt 2 := by
    change ‖((10/Real.sqrt 2:ℝ):ℂ) • toEuclidean_fromVec (Ket (1:Fin 3))‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        norm_toEuclidean_fromVec_ket, mul_one]
  rw [hn]
  have hc : ((10/Real.sqrt 2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The least-squares overlap of the example HHL matrix with the basis-zero state is zero. -/
theorem lowRankExample_kernel :
    leastSquaresOverlap (continuousHHLMatrix lowRankExampleSpectrum (1 : Operator 3)) (Ket 0) = 0 := by
  unfold leastSquaresOverlap
  rw [(singular_hermitian_pseudoinverse_and_least_squares 3 lowRankExampleSpectrum 1 (Submonoid.one_mem _)).2.1]
  have hv : spectralSupport lowRankExampleSpectrum (1 : Operator 3) *ᵥ Ket 0 = 0 := by
    simp only [spectralSupport, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec_diagonal, lowRankExampleSpectrum, Ket, lowRank_fin_three_mk_two, lowRank_fin_three_zero_ne_two, lowRank_fin_three_one_ne_two, lowRank_fin_three_two_ne_zero, lowRank_fin_three_two_ne_one, div_eq_mul_inv]
  rw [hv]
  simp [stateVector]

/-- For every accuracy index, the computed example grid has size at least two, the prepared
input is inconsistent, the solution target is the embedded `Ket 1`, success probability is
at least `1 / 4096`, and postmeasurement error is at most `64 * lowRankAccuracy d theta k`.
The basis-zero input with identity preparation has zero success probability. -/
theorem low_rank_uniform_hhl_inconsistent_actual_consumer : ∀ k : ℕ,
  let eig := lowRankExampleSpectrum
  let B := lowRankExamplePrepare
  let d : ℝ := 1/16
  let theta : ℝ := 1/2
  let M := lowRankGrid d theta k
  2 ≤ M ∧
  (∀ hM : 2 ≤ M,
    ¬ (∃ x : QState (Fin 3), continuousHHLMatrix eig (1 : Operator 3) *ᵥ x = B *ᵥ Ket 0) ∧
    uniformHHLSolutionTarget M hM eig (1 : Operator 3) B 0 =
      uniformHHLSuccessEmbed M hM (Ket (1 : Fin 3)) ∧
    MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig (1 : Operator 3)) d B 0)
      (flagSuccessSet 3 M) ≥ 1/4096 ∧
    ‖toEuclidean_fromVec (PostMeasure
      (uniformHHLRun M hM (continuousHHLOracle eig (1 : Operator 3)) d B 0) (flagSuccessSet 3 M) -
      uniformHHLSuccessEmbed M hM (Ket (1 : Fin 3)))‖ ≤ 64*lowRankAccuracy d theta k ∧
    MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig (1 : Operator 3)) d (1 : Operator 3) 0)
      (flagSuccessSet 3 M) = 0)
 := by
  intro k
  have h := low_rank_uniform_hhl_computed_budget_and_retry 3 lowRankExampleSpectrum
    1 lowRankExamplePrepare 0 (1/16) (1/2) k (Submonoid.one_mem _) lowRankExamplePrepare_unitary
    (by norm_num) (by norm_num) lowRankExample_overlap lowRankExample_promise
  refine ⟨h.2.2.1, ?_⟩
  intro hM
  have hout := h.2.2.2 hM
  refine ⟨?_, lowRankExample_target _ hM, ?_, ?_, ?_⟩
  · rintro ⟨x,hx⟩
    have he := congrFun hx (0:Fin 3)
    norm_num [continuousHHLMatrix, lowRankExampleSpectrum, Matrix.mulVec_diagonal,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, lowRankExamplePrepare, Ket,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at he
    have hs : (Real.sqrt 2:ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    exact hs he.symm
  · have hp := hout.1
    norm_num at hp
    exact hp
  · have he := hout.2.1
    rw [lowRankExample_target _ hM] at he
    convert! he using 1
    norm_num
    ring
  · have hz := (low_rank_uniform_hhl_zero_overlap_timeout 3 _ hM lowRankExampleSpectrum 1 1 0
      (1/16) (Submonoid.one_mem _) (Submonoid.one_mem _) (by norm_num)
      (by simpa only [Matrix.one_mulVec] using! lowRankExample_kernel)).1
    exact hz

end Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
