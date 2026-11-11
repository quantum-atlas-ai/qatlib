/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.LayeredMean.CountedHHLProgram
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Near-grid perturbation bounds for HHL output

`continuousHHLMatrix` and `continuousHHLOracle` construct a matrix and its phase oracle from
real spectral data. The module bounds their differences from grid-aligned counterparts using
unitary diagonalization and reciprocal estimates, connecting matrix perturbation methods
[Bhatia1997] to the HHL program [HarrowHassidimLloyd2009].

The resulting consumer bounds the actual clean branch's mass, residual, and normalized solution
error, and specializes them to an explicit two-eigenvalue example.

## Main statements

* `continuous_neargrid_oracle_and_inverse_perturbation`: oracle and pseudoinverse perturbation
  bounds.
* `neargrid_hhl_same_program_solution_and_success`: success mass, residual, and normalized
  solution estimates.
* `neargrid_hhl_two_eigenvalue_actual_consumer`: a concrete six-query, eighteen-gate instance.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

/-- The matrix `V * diagonal eig * Vᴴ` associated with the real spectral data. -/
noncomputable def continuousHHLMatrix {D : ℕ} (eig : Fin D → ℝ) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ

/-- The matrix `V * diagonal (exp (2 * π * I * eig)) * Vᴴ` associated with the spectral phases. -/
noncomputable def continuousHHLOracle {D : ℕ} (eig : Fin D → ℝ) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))) * Vᴴ

/-- Unitary conjugation of a diagonal matrix has operator norm at most the supremum norm of its
diagonal. -/
theorem norm_conj_diagonal_le {D : ℕ} (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (w : Fin D → ℂ) :
    ‖V * Matrix.diagonal w * Vᴴ‖ ≤ ‖w‖ := by
  have hnormV : ∀ x : QState (Fin D),
      ‖toEuclidean_fromVec (V *ᵥ x)‖ = ‖toEuclidean_fromVec x‖ :=
    fun x => norm_applyGate_of_mem_unitaryGroup hV x
  have hnormV' : ∀ x : QState (Fin D),
      ‖toEuclidean_fromVec (Vᴴ *ᵥ x)‖ = ‖toEuclidean_fromVec x‖ :=
    fun x => norm_applyGate_of_mem_unitaryGroup (mem_unitaryGroup_adjoint hV) x
  refine l2_opNorm_le_of_mulVec_le (norm_nonneg _) _ fun ψ => ?_
  have hact : (V * Matrix.diagonal w * Vᴴ) *ᵥ ψ
      = V *ᵥ (Matrix.diagonal w *ᵥ (Vᴴ *ᵥ ψ)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag := l2_norm_mulVec_fromVec_le (Matrix.diagonal w) (Vᴴ *ᵥ ψ)
  rw [Matrix.l2_opNorm_diagonal] at hdiag
  have hVnorm := hnormV' ψ
  rw [hact, hnormV]
  calc ‖toEuclidean_fromVec (Matrix.diagonal w *ᵥ (Vᴴ *ᵥ ψ))‖
      ≤ ‖w‖ * ‖toEuclidean_fromVec (Vᴴ *ᵥ ψ)‖ := hdiag
    _ = ‖w‖ * ‖toEuclidean_fromVec ψ‖ := by rw [hVnorm]

/-- The difference of two diagonal matrices conjugated by the same matrix is the conjugate of
their pointwise diagonal difference. -/
theorem conj_diagonal_sub {D : ℕ} (V : Operator D) (w w' : Fin D → ℂ) :
    V * Matrix.diagonal w * Vᴴ - V * Matrix.diagonal w' * Vᴴ
      = V * Matrix.diagonal (w - w') * Vᴴ := by
  have h1 : V * Matrix.diagonal w * Vᴴ - V * Matrix.diagonal w' * Vᴴ
      = (V * Matrix.diagonal w - V * Matrix.diagonal w') * Vᴴ := by rw [Matrix.sub_mul]
  rw [h1, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

/-- For unitary `V` and nonzero diagonal entries, conjugating their pointwise reciprocals gives
a two-sided inverse. -/
theorem conj_diagonal_mul_inv {D : ℕ} (w : Fin D → ℂ) (hw : ∀ i, w i ≠ 0)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (V * Matrix.diagonal w * Vᴴ) * (V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ) = 1 ∧
      (V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ) * (V * Matrix.diagonal w * Vᴴ) = 1 := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hdd : Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [mul_inv_cancel₀ (hw i)]
    · simp [hij]
  have hdd' : Matrix.diagonal (fun i => (w i)⁻¹) * Matrix.diagonal w = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [inv_mul_cancel₀ (hw i)]
    · simp [hij]
  constructor
  · have hassoc : (V * Matrix.diagonal w * Vᴴ)
            * (V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ)
          = V * (Matrix.diagonal w * ((Vᴴ * V)
              * Matrix.diagonal (fun i => (w i)⁻¹))) * Vᴴ := by
      noncomm_ring
    rw [hassoc, hVU, Matrix.one_mul, hdd, Matrix.mul_one, hUV]
  · have hassoc : (V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ)
            * (V * Matrix.diagonal w * Vᴴ)
          = V * (Matrix.diagonal (fun i => (w i)⁻¹) * ((Vᴴ * V)
              * Matrix.diagonal w)) * Vᴴ := by
      noncomm_ring
    rw [hassoc, hVU, Matrix.one_mul, hdd', Matrix.mul_one, hUV]

/-- For unitary `V` and nonzero diagonal entries, the matrix pseudoinverse is obtained by
conjugating the pointwise reciprocal diagonal. -/
theorem pseudoinverse_conj_diagonal {D : ℕ} (w : Fin D → ℂ) (hw : ∀ i, w i ≠ 0)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    matrixPseudoinverse (V * Matrix.diagonal w * Vᴴ)
      = V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ := by
  obtain ⟨hAB, hBA⟩ := conj_diagonal_mul_inv w hw V hV
  refine (matrixPseudoinverse_unique (O := Fin D) (I := Fin D)
    (V * Matrix.diagonal w * Vᴴ) (V * Matrix.diagonal (fun i => (w i)⁻¹) * Vᴴ) ?_ ?_ ?_ ?_).symm
  · rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · rw [hAB]
    simp
  · rw [hBA]
    simp

/-- The map `t ↦ exp (2 * π * I * t)` is `2 * π`-Lipschitz on the reals. -/
theorem norm_exp_two_pi_sub (a t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ ≤ 2 * Real.pi * |a - t| := by
  have hunit : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := norm_exp_two_pi_I t
  have hsplit : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))
          * (Complex.exp (2 * Real.pi * Complex.I * ((a - t : ℝ) : ℂ)) - 1) := by
    have he : (2 * Real.pi * Complex.I * (a : ℂ))
        = (2 * Real.pi * Complex.I * (t : ℂ))
          + (2 * Real.pi * Complex.I * ((a - t : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [he, Complex.exp_add]
    ring
  have hkey : ‖Complex.exp (2 * Real.pi * Complex.I * ((a - t : ℝ) : ℂ)) - 1‖
      ≤ 2 * Real.pi * |a - t| := by
    have hexp : Complex.exp (2 * Real.pi * Complex.I * ((a - t : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((2 * Real.pi * (a - t : ℝ) : ℝ))) := by
      congr 1
      push_cast
      ring
    rw [hexp]
    refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hsplit, norm_mul, hunit, one_mul]
  exact hkey

/-- If `a` and `b` are at least `d > 0` and differ by at most `Δ`, their reciprocals differ by
at most `Δ / d^2`. -/
theorem inv_sub_inv_abs_le {a b d Δ : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b)
    (hΔ : |a - b| ≤ Δ) : |a⁻¹ - b⁻¹| ≤ Δ / d ^ 2 := by
  have hpa : 0 < a := lt_of_lt_of_le hd ha
  have hpb : 0 < b := lt_of_lt_of_le hd hb
  have hpos : 0 < a * b := mul_pos hpa hpb
  have hrw : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  have hΔ' : |b - a| ≤ Δ := by rw [abs_sub_comm]; exact hΔ
  have h2 : d ^ 2 ≤ a * b := by nlinarith [ha, hb, mul_nonneg hd.le hd.le]
  have hΔ0 : (0 : ℝ) ≤ Δ := le_trans (abs_nonneg _) hΔ
  rw [hrw, abs_div, abs_of_pos hpos]
  have hmle := mul_le_mul hΔ' h2 (sq_nonneg d) hΔ0
  rwa [← div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < d ^ 2)] at hmle

/-- The conjugate transpose of the diagonal spectral-phase matrix multiplied by that matrix is
the identity. -/
theorem continuousHHLOracleDiagonal_adjoint_mul {D : ℕ} (eig : Fin D → ℝ) :
    (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))))ᴴ
      * Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 : Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_exp_two_pi_I, one_pow]
    have h2 : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ)) = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast h1
    simpa using! h2
  · simp [hij]

/-- The continuous spectral-phase oracle is unitary when its eigenbasis matrix is unitary. -/
theorem continuous_hhl_oracle_unitary {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have h := continuousHHLOracleDiagonal_adjoint_mul eig
  rw [Matrix.mem_unitaryGroup_iff', continuousHHLOracle, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show Vᴴ * (V * (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ)))
            * Vᴴ)) = (Vᴴ * V) * (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I *
            (eig i : ℂ))) * Vᴴ) from (Matrix.mul_assoc Vᴴ V _).symm,
    hVU, Matrix.one_mul,
    show (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))))ᴴ
        * (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))) * Vᴴ)
        = ((Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))))ᴴ *
            Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ)))) * Vᴴ
        from (Matrix.mul_assoc _ _ _).symm,
    h, Matrix.one_mul, hUV]

/-- If positive spectral values and their grid labels differ by at most `Δ` and are bounded
below by `d`, their oracles differ by at most `2 * π * Δ` and their matrix pseudoinverses by
at most `Δ / d^2`. The continuous oracle is unitary. -/
theorem continuous_neargrid_oracle_and_inverse_perturbation :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (eig : Fin D → ℝ) (V : Operator D) (d Δ : ℝ),
      2 ≤ M → V ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 ≤ Δ →
      (∀ i, d ≤ eig i ∧ eig i ≤ 1 ∧ d ≤ (label i).val / (M : ℝ) ∧
        |eig i - (label i).val / (M : ℝ)| ≤ Δ) →
      continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖continuousHHLOracle eig V - gridHHLOracle label V‖ ≤ 2 * Real.pi * Δ ∧
      ‖matrixPseudoinverse (continuousHHLMatrix eig V)
        - matrixPseudoinverse (gridHHLMatrix label V)‖ ≤ Δ / d ^ 2 := by
  intro D M label eig V d Δ hM hV hd hΔ hspec
  have hMpos : 0 < M := by omega
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
  set t : Fin D → ℝ := fun i => (label i).val / (M : ℝ) with ht
  have hgridEq : gridHHLOracle label V
      = V * Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * ((t i : ℂ)))) * Vᴴ := by
    have hdiag : (Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ))) : Operator D)
        = Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * ((t i : ℂ)))) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply]
        rw [primRoot_zpow_eq_exp]
        congr 1
        push_cast [ht]
        ring
      · simp [hij]
    rw [gridHHLOracle, hdiag]

  have hentry : ∀ i : Fin D,
      ‖Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * ((t i : ℂ)))‖ ≤ 2 * Real.pi * Δ := by
    intro i
    refine le_trans (norm_exp_two_pi_sub (eig i) (t i)) ?_
    exact mul_le_mul_of_nonneg_left ((hspec i).2.2.2) (by positivity)
  have horacle : ‖continuousHHLOracle eig V - gridHHLOracle label V‖ ≤ 2 * Real.pi * Δ := by
    have hsplit : continuousHHLOracle eig V - gridHHLOracle label V
        = V * Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (eig i : ℂ))
            - Complex.exp (2 * Real.pi * Complex.I * ((t i : ℂ)))) * Vᴴ := by
      rw [continuousHHLOracle, hgridEq, conj_diagonal_sub]
      rfl
    rw [hsplit]
    refine le_trans (norm_conj_diagonal_le V hV _) ?_
    exact (pi_norm_le_iff_of_nonneg (by positivity)).2 hentry

  have hw1 : ∀ i : Fin D, ((eig i : ℂ)) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hd (hspec i).1))
  have hw2 : ∀ i : Fin D, ((t i : ℂ)) ≠ 0 := by
    intro i
    have hpos : 0 < t i := lt_of_lt_of_le hd (hspec i).2.2.1
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have hgridMat : gridHHLMatrix label V = V * Matrix.diagonal (fun i => ((t i : ℂ))) * Vᴴ := by
    have hdiag : (Matrix.diagonal (fun i => ((label i).val : ℂ) / (M : ℂ)) : Operator D)
        = Matrix.diagonal (fun i => ((t i : ℂ))) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        have hc : (((label i).val : ℂ) / (M : ℂ)) = ((t i : ℂ)) := by
          push_cast [ht]
          field_simp
        simp [hc]
      · simp [hij]
    rw [gridHHLMatrix, hdiag]
  have hinv : ∀ i : Fin D, ‖(((eig i : ℂ))⁻¹ - ((t i : ℂ))⁻¹)‖ ≤ Δ / d ^ 2 := by
    intro i
    have h := inv_sub_inv_abs_le (a := eig i) (b := t i) hd (hspec i).1 (hspec i).2.2.1
      (hspec i).2.2.2
    have hcast : (((eig i : ℂ))⁻¹ - ((t i : ℂ))⁻¹) = (((eig i)⁻¹ - (t i)⁻¹ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real]
    exact h
  refine ⟨continuous_hhl_oracle_unitary eig V hV, horacle, ?_⟩
  have hpA : matrixPseudoinverse (continuousHHLMatrix eig V)
      = V * Matrix.diagonal (fun i => ((eig i : ℂ))⁻¹) * Vᴴ :=
    pseudoinverse_conj_diagonal _ hw1 V hV
  have hpG : matrixPseudoinverse (gridHHLMatrix label V)
      = V * Matrix.diagonal (fun i => ((t i : ℂ))⁻¹) * Vᴴ := by
    rw [hgridMat]
    exact pseudoinverse_conj_diagonal _ hw2 V hV
  have hsplit : matrixPseudoinverse (continuousHHLMatrix eig V)
      - matrixPseudoinverse (gridHHLMatrix label V)
      = V * Matrix.diagonal (fun i => ((eig i : ℂ))⁻¹ - ((t i : ℂ))⁻¹) * Vᴴ := by
    rw [hpA, hpG, conj_diagonal_sub]
    rfl
  rw [hsplit]
  refine le_trans (norm_conj_diagonal_le V hV _) ?_
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 hinv

/-- For the near-grid spectral promise and combined error `η < c`, the actual clean HHL branch
is nonzero, has mass at least `(c - η)^2`, and has residual at most `η`. Its normalized
state is within `2 * η / c` of the normalized pseudoinverse solution. -/
theorem neargrid_hhl_same_program_solution_and_success :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d Δ c : ℝ), 2 ≤ M → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 ≤ Δ → 0 < c → c ≤ 1 / (M : ℝ) →
      (∀ i, d ≤ eig i ∧ eig i ≤ 1 ∧ d ≤ (label i).val / (M : ℝ) ∧
        |eig i - (label i).val / (M : ℝ)| ≤ Δ) →
      let A := continuousHHLMatrix eig V
      let b := ApplyGate B (Ket j)
      let y := countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
      let η := (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ
      η < c → y ≠ 0 ∧ (c - η) ^ 2 ≤ MeasureProb y Finset.univ ∧
        ‖stateVector (A *ᵥ y - (c : ℂ) • b)‖ ≤ η ∧
        ‖stateVector (PostMeasure y Finset.univ)
          - NormedSpace.normalize (stateVector (matrixPseudoinverse A *ᵥ b))‖ ≤ 2 * η / c := by
  intro D M label eig V B j d Δ c hM hV hB hd hΔ hc0 hc1 hspec A b y η hη
  have hMpos : 0 < M := by omega
  have hG4 := continuous_neargrid_oracle_and_inverse_perturbation D M label eig V d Δ hM hV hd hΔ
    hspec
  set t : Fin D → ℝ := fun i => (label i).val / (M : ℝ) with ht
  have hWu : continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    continuous_hhl_oracle_unitary eig V hV
  have hGu : gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    (grid_hhl_spectral_matrix_and_oracle_unitary D M label V hMpos hV).2.2
  have hG2 := counted_hhl_exact_grid_clean_branch D M label V B j c hM hV hB hc0.le hc1
  have hG3 := counted_hhl_unitary_oracle_clean_branch_noise D M
    (continuousHHLOracle eig V) (gridHHLOracle label V) B j c
    (‖continuousHHLOracle eig V - gridHHLOracle label V‖) hM hWu hGu hB hc0.le hc1
    (le_refl _)
  have hnoise : ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
        - countedHHLCleanBranch (gridHHLOracle label V) M c B j)‖
      ≤ 4 * Real.pi * (M - 1 : ℕ) * Δ := by
    refine le_trans hG3 ?_
    rw [show (4 * Real.pi * (M - 1 : ℕ)) * Δ
        = 2 * ((M - 1 : ℕ) : ℝ) * (2 * Real.pi * Δ) by ring]
    exact mul_le_mul_of_nonneg_left hG4.2.1 (by positivity)

  have hb1 : ‖stateVector (ApplyGate B (Ket j))‖ = 1 := by
    have hsum := sum_normSq_mulVec_of_mem_unitaryGroup hB (Ket j)
    have hket : ∑ i, Complex.normSq ((Ket j) i) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp [Ket]
      · intro i _ hi
        simp [Ket, hi]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hmp : MeasureProb (ApplyGate B (Ket j)) Finset.univ = 1 := by
      have h2 : ∑ i, ‖(ApplyGate B (Ket j)) i‖ ^ 2 = 1 := by
        simpa only [Complex.normSq_eq_norm_sq] using! hsum.trans hket
      exact h2
    have hsq : ‖stateVector (ApplyGate B (Ket j))‖ ^ 2 = 1 := by
      rw [stateVector_norm_sq, hmp]
    have hnn := norm_nonneg (stateVector (ApplyGate B (Ket j)))
    nlinarith [hsq, hnn]

  have hw1 : ∀ i : Fin D, ((eig i : ℂ)) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hd (hspec i).1))
  obtain ⟨hAAinv, -⟩ := conj_diagonal_mul_inv (fun i => (eig i : ℂ)) hw1 V hV
  have hpinvA : matrixPseudoinverse (continuousHHLMatrix eig V)
      = V * Matrix.diagonal (fun i => ((eig i : ℂ))⁻¹) * Vᴴ :=
    pseudoinverse_conj_diagonal _ hw1 V hV
  have hApA : continuousHHLMatrix eig V * matrixPseudoinverse (continuousHHLMatrix eig V) = 1 := by
    rw [hpinvA]
    exact hAAinv
  have hAnorm : ‖continuousHHLMatrix eig V‖ ≤ 1 := by
    have hAeq : continuousHHLMatrix eig V
        = V * Matrix.diagonal (fun i => ((eig i : ℂ))) * Vᴴ := rfl
    rw [hAeq]
    refine le_trans (norm_conj_diagonal_le V hV _) ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1)).2 ?_
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le hd (hspec i).1)]
    exact (hspec i).2.1
  have hbpinv : 1 ≤ ‖stateVector (matrixPseudoinverse (continuousHHLMatrix eig V)
      *ᵥ ApplyGate B (Ket j))‖ := by
    have hkey : continuousHHLMatrix eig V
        *ᵥ (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ ApplyGate B (Ket j))
        = ApplyGate B (Ket j) := by
      rw [Matrix.mulVec_mulVec, hApA, Matrix.one_mulVec]
    have h1 := stateVector_mulVec_norm_le (continuousHHLMatrix eig V)
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ ApplyGate B (Ket j))
    rw [hkey, hb1] at h1
    have hnn := norm_nonneg (stateVector
      (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ ApplyGate B (Ket j)))
    nlinarith [h1, hAnorm, hnn]

  have hcsmul : ∀ v : QState (Fin D),
      ‖stateVector ((c : ℂ) • v)‖ = c * ‖stateVector v‖ := by
    intro v
    rw [show stateVector ((c : ℂ) • v) = (c : ℂ) • stateVector v from rfl, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0.le]
  have hxy : ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)
        - stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
            *ᵥ ApplyGate B (Ket j)))‖
      ≤ (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ := by
    have hsplit : countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
          - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
              *ᵥ ApplyGate B (Ket j))
        = (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
            - countedHHLCleanBranch (gridHHLOracle label V) M c B j)
          + (c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
              - matrixPseudoinverse (continuousHHLMatrix eig V)) *ᵥ ApplyGate B (Ket j)) := by
      have e1 : countedHHLCleanBranch (gridHHLOracle label V) M c B j
          = (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ ApplyGate B (Ket j)) :=
        hG2
      have e2 : (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ ApplyGate B (Ket j))
          - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
              *ᵥ ApplyGate B (Ket j))
          = (c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
              - matrixPseudoinverse (continuousHHLMatrix eig V)) *ᵥ ApplyGate B (Ket j)) := by
        rw [← smul_sub, ← Matrix.sub_mulVec]
      calc countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
            - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
                *ᵥ ApplyGate B (Ket j))
          = (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
              - countedHHLCleanBranch (gridHHLOracle label V) M c B j)
            + (countedHHLCleanBranch (gridHHLOracle label V) M c B j
              - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
                  *ᵥ ApplyGate B (Ket j))) := by
            abel
        _ = (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
              - countedHHLCleanBranch (gridHHLOracle label V) M c B j)
            + (c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
                - matrixPseudoinverse (continuousHHLMatrix eig V)) *ᵥ ApplyGate B (Ket j)) := by
            refine congrArg₂ (· + ·) rfl ?_
            rw [e1, e2]
    have hnormadd : ∀ x z : QState (Fin D),
        ‖stateVector (x + z)‖ ≤ ‖stateVector x‖ + ‖stateVector z‖ := by
      intro x z
      rw [show stateVector (x + z) = stateVector x + stateVector z from rfl]
      exact norm_add_le _ _
    have hpinvle : ‖stateVector ((matrixPseudoinverse (gridHHLMatrix label V)
          - matrixPseudoinverse (continuousHHLMatrix eig V)) *ᵥ ApplyGate B (Ket j))‖
        ≤ (Δ / d ^ 2) * 1 := by
      have h1 := stateVector_mulVec_norm_le
        (matrixPseudoinverse (gridHHLMatrix label V)
          - matrixPseudoinverse (continuousHHLMatrix eig V)) (ApplyGate B (Ket j))
      rw [hb1] at h1
      refine le_trans h1 ?_
      rw [mul_one, mul_one, norm_sub_rev]
      exact hG4.2.2
    calc ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)
          - stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
              *ᵥ ApplyGate B (Ket j)))‖
        = ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
            - countedHHLCleanBranch (gridHHLOracle label V) M c B j
            + (c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
                - matrixPseudoinverse (continuousHHLMatrix eig V))
                *ᵥ ApplyGate B (Ket j)))‖ := by
          show ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
            - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
              *ᵥ ApplyGate B (Ket j)))‖ = _
          rw [hsplit]
      _ ≤ ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
            - countedHHLCleanBranch (gridHHLOracle label V) M c B j)‖
            + ‖stateVector ((c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
                - matrixPseudoinverse (continuousHHLMatrix eig V))
                *ᵥ ApplyGate B (Ket j)))‖ := hnormadd _ _
      _ ≤ 4 * Real.pi * (M - 1 : ℕ) * Δ
            + ‖stateVector ((c : ℂ) • ((matrixPseudoinverse (gridHHLMatrix label V)
                - matrixPseudoinverse (continuousHHLMatrix eig V))
                *ᵥ ApplyGate B (Ket j)))‖ := by gcongr
      _ = 4 * Real.pi * (M - 1 : ℕ) * Δ
            + c * ‖stateVector ((matrixPseudoinverse (gridHHLMatrix label V)
                - matrixPseudoinverse (continuousHHLMatrix eig V))
                *ᵥ ApplyGate B (Ket j))‖ := by rw [hcsmul]
      _ ≤ 4 * Real.pi * (M - 1 : ℕ) * Δ + c * ((Δ / d ^ 2) * 1) := by gcongr
      _ = (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ := by
            rw [mul_one]
            ring

  have hxge : c ≤ ‖stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
      *ᵥ ApplyGate B (Ket j)))‖ := by
    rw [hcsmul]
    exact le_trans (le_of_eq (by rw [mul_one])) (mul_le_mul_of_nonneg_left hbpinv hc0.le)
  have hgap : (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ
      < ‖stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
          *ᵥ ApplyGate B (Ket j)))‖ := lt_of_lt_of_le hη hxge
  have hxy' : ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)
      - stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
          *ᵥ ApplyGate B (Ket j)))‖
      ≤ (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ := hxy
  obtain ⟨hyne0, hnormerr⟩ := normalize_error_of_gap hxy' hgap
  refine ⟨fun hz => hyne0 ((stateVector_eq_zero_iff _).mpr hz), ?_, ?_, ?_⟩
  · have htri := norm_sub_norm_le
        (stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
          *ᵥ ApplyGate B (Ket j))))
        (stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j))
    have hxy2 : ‖stateVector ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
          *ᵥ ApplyGate B (Ket j)))
          - stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)‖
        ≤ (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ := by
      rw [norm_sub_rev]
      exact hxy'
    have hcy : c - (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ
        ≤ ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)‖ := by
      linarith [hxge, htri, hxy2]
    have hcη : 0 ≤ c - (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ := by
      linarith [hη]
    have hsq : (c - (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ) ^ 2
        ≤ ‖stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j)‖ ^ 2 := by
      have hn := norm_nonneg
        (stateVector (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j))
      nlinarith [hcy, hcη, hn]
    rw [stateVector_norm_sq] at hsq
    exact hsq
  · have hAx : continuousHHLMatrix eig V
          *ᵥ ((c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
              *ᵥ ApplyGate B (Ket j)))
        = (c : ℂ) • (ApplyGate B (Ket j)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hApA, Matrix.one_mulVec]
    rw [show continuousHHLMatrix eig V *ᵥ countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
          - (c : ℂ) • (ApplyGate B (Ket j))
        = continuousHHLMatrix eig V
            *ᵥ (countedHHLCleanBranch (continuousHHLOracle eig V) M c B j
              - (c : ℂ) • (matrixPseudoinverse (continuousHHLMatrix eig V)
                  *ᵥ ApplyGate B (Ket j))) from by
      rw [Matrix.mulVec_sub, hAx]]
    refine le_trans (stateVector_mulVec_norm_le (continuousHHLMatrix eig V) _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)) ?_
    rw [one_mul]
    exact hxy'
  · rw [stateVector_postMeasure_univ]
    have hnorm : NormedSpace.normalize (stateVector (matrixPseudoinverse A *ᵥ b))
        = NormedSpace.normalize ((c : ℂ) • stateVector (matrixPseudoinverse A *ᵥ b)) := by
      exact (NormedSpace.normalize_smul_of_pos hc0
        (stateVector (matrixPseudoinverse A *ᵥ b))).symm
    rw [hnorm]
    refine le_trans hnormerr ?_
    have hηpos : 0 ≤ (4 * Real.pi * (M - 1 : ℕ) + c / d ^ 2) * Δ :=
      mul_nonneg (add_nonneg (by positivity) (div_nonneg hc0.le (sq_nonneg d))) hΔ
    exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two hηpos) hc0 hxge

/-- For the specified two-eigenvalue perturbation with `k ≥ 10`, the clean branch is nonzero and
satisfies the stated success-mass lower bound. The actual word uses six queries and eighteen
fixed gates. -/
theorem neargrid_hhl_two_eigenvalue_actual_consumer :
    ∀ (k : ℕ), 10 ≤ k →
      let eig : Fin 2 → ℝ := fun i => if i = 0 then 1/4 + (2:ℝ)^(-((k:ℤ))) else 1/2
      let B := relabelGate boolEquivFin2 Hadamard
      let y := countedHHLCleanBranch (continuousHHLOracle eig (1 : Operator 2)) 4 (1/4) B 0
      let η := (12 * Real.pi + 4) * (2:ℝ)^(-((k:ℤ)))
      y ≠ 0 ∧ (1/4 - η)^2 ≤ MeasureProb y Finset.univ ∧
        adjointQueryCount (countedHHLWord 4 (1/4) B) = 6 ∧
        adjointGateCount (countedHHLWord 4 (1/4) B) = 18 := by
  intro k hk
  set u : ℝ := (2:ℝ)^(-((k:ℤ))) with hudef
  have hu0 : 0 < u := by
    rw [hudef, _root_.zpow_neg, zpow_natCast]
    exact inv_pos.2 (pow_pos (by norm_num) k)
  have hu_le : u ≤ 1/1024 := by
    rw [hudef, _root_.zpow_neg, zpow_natCast, inv_eq_one_div,
      show (1:ℝ)/1024 = 1 / ((2:ℝ)^(10:ℕ)) by norm_num]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hk)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hBunit : relabelGate boolEquivFin2 Hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (relabelGate_mem_unitaryGroup boolEquivFin2 Hadamard).2 hadamard_unitary
  have hV1 : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.unitaryGroup _ ℂ).one_mem
  set label : Fin 2 → Fin 4 := fun i => ⟨i.val + 1, by have := i.isLt; omega⟩ with hlabel
  have hspec : ∀ i : Fin 2, 1/4 ≤ (if i = 0 then 1/4 + u else 1/2) ∧
      (if i = 0 then 1/4 + u else 1/2) ≤ 1 ∧ 1/4 ≤ (label i).val / (4 : ℝ)
      ∧ |(if i = 0 then 1/4 + u else 1/2) - (label i).val / (4 : ℝ)| ≤ u := by
    intro i
    have hc : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
    rcases hc with h | h
    · have hi : i = 0 := by
        ext
        simpa using! h
      subst hi
      have hif : (if (0 : Fin 2) = 0 then 1/4 + u else 1/2) = 1/4 + u := if_pos rfl
      have hval : ((label (0 : Fin 2)).val : ℝ) = 1 := by rw [hlabel]; norm_num
      rw [hif, hval]
      refine ⟨by linarith, by nlinarith [hu0, hu_le], by norm_num, ?_⟩
      rw [show 1/4 + u - 1/4 = u from by ring, abs_of_pos hu0]
    · have hi : i = 1 := by
        ext
        simpa using! h
      subst hi
      have hif : (if (1 : Fin 2) = 0 then 1/4 + u else 1/2) = 1/2 := if_neg (by decide)
      have hval : ((label (1 : Fin 2)).val : ℝ) = 2 := by rw [hlabel]; norm_num
      rw [hif, hval]
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      rw [show (1:ℝ)/2 - 2/4 = 0 from by norm_num, abs_zero]
      exact hu0.le
  have hηeq : (4 * Real.pi * (4 - 1 : ℕ) + (1/4) / ((1/4 : ℝ))^2) * u
      = (12 * Real.pi + 4) * u := by
    have h1 : ((4 - 1 : ℕ) : ℝ) = 3 := rfl
    have h2 : (1/4 : ℝ) / ((1/4 : ℝ))^2 = 4 := by norm_num
    rw [h1, h2]
    ring
  have hηlt : (4 * Real.pi * (4 - 1 : ℕ) + (1/4) / ((1/4 : ℝ))^2) * u < 1/4 := by
    rw [hηeq]
    have h1 : (12 * Real.pi + 4) * u ≤ (12 * Real.pi + 4) * (1/1024) :=
      mul_le_mul_of_nonneg_left hu_le (by positivity)
    have h2 : (12 * Real.pi + 4) * (1/1024) < 1/4 := by
      nlinarith [hpi]
    linarith
  obtain ⟨hy0, hyprob, -, -⟩ := neargrid_hhl_same_program_solution_and_success 2 4 label
    (fun i : Fin 2 => if i = 0 then 1/4 + (2:ℝ)^(-((k:ℤ))) else 1/2) (1 : Operator 2)
    (relabelGate boolEquivFin2 Hadamard) 0 (1/4) u (1/4) (by norm_num) hV1 hBunit
    (by norm_num) hu0.le (by norm_num) (by norm_num) hspec hηlt
  refine ⟨hy0, ?_, (countedHHLWord_queryCount 4 (1/4)
      (relabelGate boolEquivFin2 Hadamard) (by norm_num)).trans (by norm_num),
    (countedHHLWord_gateCount 4 (1/4)
      (relabelGate boolEquivFin2 Hadamard) (by norm_num)).trans (by norm_num)⟩
  rw [hηeq] at hyprob
  exact hyprob

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
