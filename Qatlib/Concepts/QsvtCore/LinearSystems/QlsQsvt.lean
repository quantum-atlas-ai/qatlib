/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.QlsQsvtDefs

/-!
# Threshold sectors for QSVT linear systems

This module proves that the closed singular value sectors are orthogonal projectors and
transports polynomial reciprocal approximation to a pseudoinverse estimate on those sectors.
Closed sectors retain the kernel and threshold singular values; under a spectral gap they are
the identity.

It constructs bounded odd windowed reciprocal responses and source phase words, proves vector
error estimates, and records completion conditions and execution counts. The relaxed parameter
versions require positive error and threshold at most one half independently. The mathematical
background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `clause40_closedSectorTransport`: operator norm control of the projected inverse response.
* `clause40_endpoint_noEpsLeDelta`: a phase word with sector and vector error bounds under
  independent parameter hypotheses.
* `clause40_cor8Bridge`: completion conditions and a phase realization of minimal length for its
  response.
* `clause40_endpoint_execution_ledger`: explicit execution ledger fields for a constructed word.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.QsvtCore.LinearSystems.StageBQLSQSVT

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QsvtCore.LinearSystems
namespace StageBQLSQSVT

open Qatlib SignalProcessing Polynomial Matrix
open scoped Classical Matrix.Norms.L2Operator

set_option maxHeartbeats 4000000

section Sector

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- Every real closed sector coefficient is either zero or one. -/
theorem clause40_closedSectorCoefficientReal_zero_one (δ x : ℝ) :
    closedSectorCoefficientReal δ x = 0 ∨ closedSectorCoefficientReal δ x = 1 := by
  by_cases hx : 0 < x
  · by_cases hδ : δ ≤ x
    · exact Or.inr (by simp [closedSectorCoefficientReal, hx, hδ])
    · exact Or.inl (by simp [closedSectorCoefficientReal, hx, hδ])
  · by_cases hn : x < 0
    · exact Or.inl (by simp [closedSectorCoefficientReal, hx, hn])
    · exact Or.inr (by simp [closedSectorCoefficientReal, hx, hn])

/-- Every complex closed sector coefficient is either zero or one. -/
theorem clause40_closedSectorCoefficient_zero_one (δ x : ℝ) :
    closedSectorCoefficient δ x = 0 ∨ closedSectorCoefficient δ x = 1 := by
  rcases clause40_closedSectorCoefficientReal_zero_one δ x with h | h
  · refine Or.inl ?_
    rw [closedSectorCoefficient, h]
    simp
  · refine Or.inr ?_
    rw [closedSectorCoefficient, h]
    simp

/-- A positive value strictly below the threshold has closed sector coefficient zero. -/
theorem clause40_closedSectorCoefficient_eq_zero_of_lt {δ x : ℝ} (hx : 0 < x) (hδ : x < δ) :
    closedSectorCoefficient δ x = 0 := by
  have h : closedSectorCoefficientReal δ x = 0 := by
    simp [closedSectorCoefficientReal, hx, not_le_of_gt hδ]
  rw [closedSectorCoefficient, h]
  simp

/-- For positive threshold and nonnegative `x`, the closed sector coefficient is one when `x` is
zero or at least the threshold. -/
theorem clause40_closedSectorCoefficient_eq_one_of {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x)
    (h : x = 0 ∨ δ ≤ x) : closedSectorCoefficient δ x = 1 := by
  have hr : closedSectorCoefficientReal δ x = 1 := by
    rcases h with rfl | hδx
    · simp [closedSectorCoefficientReal]
    · have hxp : 0 < x := by
        rcases lt_or_eq_of_le hx with h | h
        · exact h
        · rw [← h] at hδx
          exact absurd hδx (not_le_of_gt hδ)
      simp [closedSectorCoefficientReal, hxp, hδx]
  rw [closedSectorCoefficient, hr]
  simp

omit [DecidableEq O] in

/-- The diagonal matrix of closed sector coefficients on the input indexed singular values is
idempotent. -/
private theorem closedSector_diagonal_mul (A : Matrix O I ℂ) (δ : ℝ) :
    (diagonal (fun i : Fin (Fintype.card I) =>
        closedSectorCoefficient δ (matrixSingularValues A i))) *
      (diagonal (fun i : Fin (Fintype.card I) =>
        closedSectorCoefficient δ (matrixSingularValues A i)))
      = diagonal (fun i : Fin (Fintype.card I) =>
        closedSectorCoefficient δ (matrixSingularValues A i)) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply]
    rcases clause40_closedSectorCoefficient_zero_one δ (matrixSingularValues A i) with h | h
    · rw [h]; simp
    · rw [h]; simp
  · simp only [Matrix.diagonal_apply, hij, ite_false]

omit [DecidableEq O] in

/-- The diagonal matrix of closed sector coefficients on the input indexed singular values is
self adjoint. -/
private theorem closedSectorCoefficient_diagonal_selfAdjoint (A : Matrix O I ℂ) (δ : ℝ) :
    (diagonal (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)))ᴴ
      = diagonal (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Matrix.conjTranspose_apply, closedSectorCoefficient, Complex.conj_ofReal]
  · rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm h),
      Matrix.diagonal_apply_ne _ h, star_zero]

omit [DecidableEq O] in

/-- The diagonal matrix of closed sector coefficients on the output indexed singular values is
self adjoint. -/
private theorem closedLeftSectorCoefficient_diagonal_selfAdjoint (A : Matrix O I ℂ) (δ : ℝ) :
    (diagonal (fun j : Fin (Fintype.card O) =>
      closedSectorCoefficient δ (matrixSingularValues A j)))ᴴ
      = diagonal (fun j : Fin (Fintype.card O) =>
      closedSectorCoefficient δ (matrixSingularValues A j)) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Matrix.conjTranspose_apply, closedSectorCoefficient, Complex.conj_ofReal]
  · rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm h),
      Matrix.diagonal_apply_ne _ h, star_zero]

omit [DecidableEq O] in

/-- The diagonal matrix of closed sector coefficients on the output indexed singular values is
idempotent. -/
private theorem closedLeftSector_diagonal_mul (A : Matrix O I ℂ) (δ : ℝ) :
    (diagonal (fun j : Fin (Fintype.card O) =>
        closedSectorCoefficient δ (matrixSingularValues A j))) *
      (diagonal (fun j : Fin (Fintype.card O) =>
        closedSectorCoefficient δ (matrixSingularValues A j)))
      = diagonal (fun j : Fin (Fintype.card O) =>
        closedSectorCoefficient δ (matrixSingularValues A j)) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply]
    rcases clause40_closedSectorCoefficient_zero_one δ (matrixSingularValues A i) with h | h
    · rw [h]; simp
    · rw [h]; simp
  · simp only [Matrix.diagonal_apply, hij, ite_false]

/-- The closed right singular sector is an orthogonal projector for every matrix and threshold. -/
theorem clause40_closedRightSector_isOrthogonalProjector (A : Matrix O I ℂ) (δ : ℝ) :
    IsOrthogonalProjector (closedRightSector A δ) := by
  let _ := ‹DecidableEq O›
  constructor
  · change (basisColumns (rightSingularBasis A)
      * diagonal (fun i : Fin (Fintype.card I) =>
        closedSectorCoefficient δ (matrixSingularValues A i))
      * (basisColumns (rightSingularBasis A))ᴴ) *
      (basisColumns (rightSingularBasis A)
      * diagonal (fun i : Fin (Fintype.card I) =>
        closedSectorCoefficient δ (matrixSingularValues A i))
      * (basisColumns (rightSingularBasis A))ᴴ) = _
    calc
      _ = basisColumns (rightSingularBasis A)
          * (diagonal (fun i : Fin (Fintype.card I) =>
            closedSectorCoefficient δ (matrixSingularValues A i))
            * ((basisColumns (rightSingularBasis A))ᴴ * basisColumns (rightSingularBasis A))
            * diagonal (fun i : Fin (Fintype.card I) =>
              closedSectorCoefficient δ (matrixSingularValues A i)))
          * (basisColumns (rightSingularBasis A))ᴴ := by simp only [Matrix.mul_assoc]
      _ = basisColumns (rightSingularBasis A)
          * diagonal (fun i : Fin (Fintype.card I) =>
            closedSectorCoefficient δ (matrixSingularValues A i))
          * (basisColumns (rightSingularBasis A))ᴴ := by
        rw [basisColumns_adjoint_mul, Matrix.mul_one, closedSector_diagonal_mul]
  · have hself : (closedRightSector A δ)ᴴ = closedRightSector A δ := by
      rw [closedRightSector]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        closedSectorCoefficient_diagonal_selfAdjoint, Matrix.mul_assoc]
    exact hself

/-- The closed left singular sector is an orthogonal projector for every matrix and threshold. -/
theorem clause40_closedLeftSector_isOrthogonalProjector (A : Matrix O I ℂ) (δ : ℝ) :
    IsOrthogonalProjector (closedLeftSector A δ) := by
  let _ := ‹DecidableEq O›
  constructor
  · change (basisColumns (leftSingularBasis A)
      * diagonal (fun j : Fin (Fintype.card O) =>
        closedSectorCoefficient δ (matrixSingularValues A j))
      * (basisColumns (leftSingularBasis A))ᴴ) *
      (basisColumns (leftSingularBasis A)
      * diagonal (fun j : Fin (Fintype.card O) =>
        closedSectorCoefficient δ (matrixSingularValues A j))
      * (basisColumns (leftSingularBasis A))ᴴ) = _
    calc
      _ = basisColumns (leftSingularBasis A)
          * (diagonal (fun j : Fin (Fintype.card O) =>
            closedSectorCoefficient δ (matrixSingularValues A j))
            * ((basisColumns (leftSingularBasis A))ᴴ * basisColumns (leftSingularBasis A))
            * diagonal (fun j : Fin (Fintype.card O) =>
              closedSectorCoefficient δ (matrixSingularValues A j)))
          * (basisColumns (leftSingularBasis A))ᴴ := by simp only [Matrix.mul_assoc]
      _ = basisColumns (leftSingularBasis A)
          * diagonal (fun j : Fin (Fintype.card O) =>
            closedSectorCoefficient δ (matrixSingularValues A j))
          * (basisColumns (leftSingularBasis A))ᴴ := by
        rw [basisColumns_adjoint_mul, Matrix.mul_one, closedLeftSector_diagonal_mul]
  · have hself : (closedLeftSector A δ)ᴴ = closedLeftSector A δ := by
      rw [closedLeftSector]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        closedLeftSectorCoefficient_diagonal_selfAdjoint, Matrix.mul_assoc]
    exact hself

/-- The closed left singular sector is self adjoint. -/
theorem clause40_closedLeftSector_selfAdjoint (A : Matrix O I ℂ) (δ : ℝ) :
    (closedLeftSector A δ)ᴴ = closedLeftSector A δ :=
  (clause40_closedLeftSector_isOrthogonalProjector A δ).2

omit [DecidableEq O] in

/-- The Gram matrix between the left singular basis columns and left singular columns has
entries given by their pairwise inner products. -/
private theorem leftCompanion_gram_entries (A : Matrix O I ℂ) :
    ((basisColumns (leftSingularBasis A))ᴴ * leftSingularColumns A)
      = Matrix.of fun j i => inner ℂ (leftSingularBasis A j) (leftSingularVector A i) := by
  ext j i
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, leftSingularColumns,
    PiLp.inner_apply, mul_comm]

/-- Applying the closed left sector to the left singular columns equals multiplying those
columns by the diagonal closed sector coefficients. -/
private theorem closedLeftSector_mul_leftSingularColumns (A : Matrix O I ℂ) (δ : ℝ) :
    closedLeftSector A δ * leftSingularColumns A
      = leftSingularColumns A
        * diagonal (fun i : Fin (Fintype.card I) =>
          closedSectorCoefficient δ (matrixSingularValues A i)) := by
  let _ := ‹DecidableEq O›
  ext o i
  rw [closedLeftSector, Matrix.mul_assoc, Matrix.mul_assoc, leftCompanion_gram_entries]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : (i : ℕ) < Module.finrank ℂ A.toEuclideanLin.range
  · have hO : (i : ℕ) < Fintype.card O :=
      lt_of_lt_of_le hi (by simpa using! Submodule.finrank_le A.toEuclideanLin.range)
    have hWk : leftSingularBasis A ⟨(i : ℕ), hO⟩ = leftSingularVector A i := by
      simpa using! leftSingularBasis_apply_of_lt A ⟨(i : ℕ), hO⟩ hi
    have hite : ∀ x : Fin (Fintype.card O), inner ℂ (leftSingularBasis A x)
        (leftSingularBasis A ⟨(i : ℕ), hO⟩) = if x = ⟨(i : ℕ), hO⟩ then (1 : ℂ) else 0 :=
      fun x => (leftSingularBasis A).inner_eq_ite x _
    rw [← hWk]
    simp only [hite, mul_ite, mul_one, mul_zero, basisColumns_apply, leftSingularColumns]
    refine Eq.trans (Finset.sum_eq_single_of_mem (⟨(i : ℕ), hO⟩ : Fin (Fintype.card O))
      (Finset.mem_univ _) ?_) ?_
    · intro b _ hb
      rw [ite_eq_right hb]
    · rw [ite_eq_left rfl, hWk]
  · have hσ0 : matrixSingularValues A i = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (by omega)
    have h0 : leftSingularColumns A o i = 0 := by
      simp [leftSingularColumns, leftSingularVector_eq_zero A i hσ0]
    rw [leftSingularVector_eq_zero A i hσ0, h0]
    simp

/-- A polynomial vanishing at zero and approximating `(δ / 2) / x` on `[δ, 1]` has scalar closed
sector residual at most `ε` on `[0, 1]` under the stated sign hypotheses. -/
private theorem closedSector_entry_bound {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    {Pw : Polynomial ℝ} (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖closedSectorCoefficient δ t * ((Pw.eval t : ℝ) : ℂ) * closedSectorCoefficient δ t
      - (δ/2 : ℂ) * ((t : ℂ)⁻¹) * closedSectorCoefficient δ t‖ ≤ ε := by
  by_cases htpos : 0 < t
  · by_cases htd : t < δ
    · have hcoef : closedSectorCoefficient δ t = 0 :=
        clause40_closedSectorCoefficient_eq_zero_of_lt htpos htd
      simp only [hcoef, zero_mul, mul_zero, sub_zero, norm_zero]
      exact hε
    · have hδt : δ ≤ t := le_of_not_gt htd
      have hcoef : closedSectorCoefficient δ t = 1 :=
        clause40_closedSectorCoefficient_eq_one_of hδ (le_of_lt htpos) (Or.inr hδt)
      have h1 : ((δ : ℂ) / 2) * ((t : ℂ)⁻¹) = ((δ / 2 / t : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_div]
        field_simp
        norm_num
      simp only [hcoef, one_mul, mul_one]
      rw [h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact happrox t ⟨hδt, ht1⟩
  · have ht0' : t = 0 := le_antisymm (le_of_not_gt htpos) ht0
    subst ht0'
    have hcoef : closedSectorCoefficient δ 0 = 1 :=
      clause40_closedSectorCoefficient_eq_one_of hδ (le_refl 0) (Or.inl rfl)
    simp only [hcoef, one_mul, mul_one, heval0]
    simp only [Complex.ofReal_zero, Complex.inv_zero, mul_zero, sub_zero, norm_zero]
    exact hε

/-- For a matrix contraction, scalar reciprocal error at most `ε` on `[δ, 1]` and zero response
at zero give operator error at most `ε` for the closed sector projected adjoint odd
transform. -/
theorem clause40_closedSectorTransport
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (Pw : Polynomial ℝ) (ε δ : ℝ)
    (hA : ‖A‖ ≤ 1) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) :
    ‖closedRightSector A δ * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
        * closedLeftSector A δ
      - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ ≤ ε := by
  have hC : (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
      = basisColumns (rightSingularBasis A)
        * diagonal (fun i : Fin (Fintype.card I) => ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ))
        * (leftSingularColumns A)ᴴ := by
    rw [oddSingularTransform, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    have hd : (diagonal (fun i : Fin (Fintype.card I) =>
        ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)))ᴴ
        = diagonal (fun i : Fin (Fintype.card I) =>
        ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)) := by
      ext a b
      by_cases h : a = b
      · subst h
        simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
      · rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm h),
          Matrix.diagonal_apply_ne _ h, star_zero]
    rw [hd, Matrix.mul_assoc]
  have hUL := congrArg Matrix.conjTranspose (closedLeftSector_mul_leftSingularColumns A δ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, clause40_closedLeftSector_selfAdjoint,
    closedSectorCoefficient_diagonal_selfAdjoint] at hUL
  have hRV : ∀ X : Matrix (Fin (Fintype.card I)) O ℂ,
      closedRightSector A δ * (basisColumns (rightSingularBasis A) * X)
        = basisColumns (rightSingularBasis A)
          * (diagonal (fun i : Fin (Fintype.card I) =>
            closedSectorCoefficient δ (matrixSingularValues A i)) * X) := by
    intro X
    rw [closedRightSector, Matrix.mul_assoc,
      show (basisColumns (rightSingularBasis A))ᴴ
          * (basisColumns (rightSingularBasis A) * X)
        = ((basisColumns (rightSingularBasis A))ᴴ * basisColumns (rightSingularBasis A)) * X from by
          rw [← Matrix.mul_assoc],
      basisColumns_adjoint_mul, Matrix.one_mul, Matrix.mul_assoc]
  have hsd : ∀ (c : ℂ) (f : Fin (Fintype.card I) → ℂ),
      c • diagonal f = diagonal (fun i => c * f i) := by
    intro c f
    ext a b
    by_cases h : a = b <;> simp [h, Matrix.smul_apply]
  have hE : closedRightSector A δ
      * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
      * closedLeftSector A δ
      - (δ/2 : ℂ) • (matrixPseudoinverse A
        * closedLeftSector A δ)
      = basisColumns (rightSingularBasis A)
        * diagonal (fun i : Fin (Fintype.card I) =>
            closedSectorCoefficient δ (matrixSingularValues A i)
              * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
              * closedSectorCoefficient δ (matrixSingularValues A i)
            - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
              * closedSectorCoefficient δ (matrixSingularValues A i))
        * (leftSingularColumns A)ᴴ := by
    have hstep1 : closedRightSector A δ
        * ((oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ)
        - (δ/2 : ℂ) • (matrixPseudoinverse A
          * closedLeftSector A δ)
        = basisColumns (rightSingularBasis A)
          * ((diagonal (fun i : Fin (Fintype.card I) =>
                closedSectorCoefficient δ (matrixSingularValues A i))
              * (diagonal (fun i : Fin (Fintype.card I) =>
                ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ))
                * (diagonal (fun i : Fin (Fintype.card I) =>
                  closedSectorCoefficient δ (matrixSingularValues A i)) * (leftSingularColumns A)ᴴ)))
            - (δ/2 : ℂ) • (diagonal (fun i : Fin (Fintype.card I) =>
                ((matrixSingularValues A i : ℂ)⁻¹))
              * (diagonal (fun i : Fin (Fintype.card I) =>
                closedSectorCoefficient δ (matrixSingularValues A i)) * (leftSingularColumns A)ᴴ))) := by
      rw [hC, matrixPseudoinverse_eq]
      simp only [Matrix.mul_assoc]
      rw [hUL, ← Matrix.mul_smul, hRV, ← Matrix.mul_sub]
    rw [Matrix.mul_assoc, hstep1, ← Matrix.smul_mul, hsd, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.sub_mul,
      Matrix.diagonal_sub, ← Matrix.mul_assoc]
  have hentry : ∀ i : Fin (Fintype.card I),
      ‖closedSectorCoefficient δ (matrixSingularValues A i)
        * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
        * closedSectorCoefficient δ (matrixSingularValues A i)
        - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
          * closedSectorCoefficient δ (matrixSingularValues A i)‖ ≤ ε := by
    intro i
    exact closedSector_entry_bound hε hδ heval0 happrox
      (matrixSingularValues_nonneg A i)
      ((matrixSingularValues_le_spectralNorm A i).trans hA)
  have hdiag : ‖diagonal (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)
        * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
        * closedSectorCoefficient δ (matrixSingularValues A i)
      - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
        * closedSectorCoefficient δ (matrixSingularValues A i))‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).2 hentry
  have hVn : ‖basisColumns (rightSingularBasis A)‖ ≤ 1 := basisColumns_norm_le _
  have hUn : ‖(leftSingularColumns A)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact leftSingularColumns_norm_le A
  rw [hE]
  have h1 : ‖basisColumns (rightSingularBasis A)
      * diagonal (fun i : Fin (Fintype.card I) =>
          closedSectorCoefficient δ (matrixSingularValues A i)
            * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
            * closedSectorCoefficient δ (matrixSingularValues A i)
          - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
            * closedSectorCoefficient δ (matrixSingularValues A i))‖ ≤ ε := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    exact (mul_le_mul hVn hdiag (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul h1 hUn (norm_nonneg _) hε).trans_eq (mul_one ε))

/-- At a positive threshold, the strict coefficient is zero and the closed coefficient is one. -/
theorem clause40_threshold_stratum_kept {δ : ℝ} (hδ : 0 < δ) :
    strictSectorCoefficient δ δ = 0 ∧ closedSectorCoefficient δ δ = 1 := by
  have hti0 : thresholdIndicator 0 δ = 1 := by
    simp only [thresholdIndicator]
    rw [ite_eq_left (show (0 : ℝ)^2 < δ^2 by nlinarith [sq_pos_of_pos hδ])]
  have htiδ : thresholdIndicator δ δ = 0 := by
    simp only [thresholdIndicator]
    rw [ite_eq_right (show ¬(δ^2 < δ^2) by exact lt_irrefl _)]
  refine ⟨?_, clause40_closedSectorCoefficient_eq_one_of hδ (le_of_lt hδ) (Or.inr (le_refl δ))⟩
  simp [strictSectorCoefficient, hti0]

/-- If every nonzero input indexed singular value is at least the positive threshold, the closed
right sector is the identity. -/
theorem clause40_closedRightSector_eq_one_of_gap
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i) :
    closedRightSector A δ = 1 := by
  have hcoeff : (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)) = (fun _ => (1 : ℂ)) := by
    funext i
    by_cases h0 : matrixSingularValues A i = 0
    · rw [h0]
      exact clause40_closedSectorCoefficient_eq_one_of hδ (le_refl 0) (Or.inl rfl)
    · exact clause40_closedSectorCoefficient_eq_one_of hδ (matrixSingularValues_nonneg A i)
        (Or.inr (hgap i h0))
  have hrep : closedRightSector A δ = spectralDiagonal (rightSingularBasis A)
      (fun i : Fin (Fintype.card I) => closedSectorCoefficient δ (matrixSingularValues A i)) := rfl
  rw [hrep, hcoeff]
  simpa using! (spectralDiagonal_const (rightSingularBasis A) 1)

/-- If every nonzero input indexed singular value is at least the positive threshold, the closed
left sector is the identity. -/
theorem clause40_closedLeftSector_eq_one_of_gap
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i) :
    closedLeftSector A δ = 1 := by
  have hcoeff : (fun j : Fin (Fintype.card O) =>
      closedSectorCoefficient δ (matrixSingularValues A j)) = (fun _ => (1 : ℂ)) := by
    funext j
    by_cases h0 : matrixSingularValues A j = 0
    · rw [h0]
      exact clause40_closedSectorCoefficient_eq_one_of hδ (le_refl 0) (Or.inl rfl)
    · by_cases hj : j.val < Fintype.card I
      · have hgap' : δ ≤ matrixSingularValues A j := by
          have h := hgap (⟨j.val, hj⟩ : Fin (Fintype.card I)) h0
          rwa [show matrixSingularValues A (⟨j.val, hj⟩ : Fin (Fintype.card I))
            = matrixSingularValues A j from rfl] at h
        exact clause40_closedSectorCoefficient_eq_one_of hδ (matrixSingularValues_nonneg A j)
          (Or.inr hgap')
      · have hz : matrixSingularValues A j = 0 :=
          matrixSingularValues_of_card_le A (by omega)
        exact (h0 hz).elim
  have hrep : closedLeftSector A δ = spectralDiagonal (leftSingularBasis A)
      (fun j : Fin (Fintype.card O) => closedSectorCoefficient δ (matrixSingularValues A j)) := rfl
  rw [hrep, hcoeff]
  simpa using! (spectralDiagonal_const (leftSingularBasis A) 1)

/-- Under the singular value gap, the adjoint polynomial odd transform approximates `(δ / 2)`
times the full pseudoinverse within `ε` in operator norm. -/
theorem clause40_closedSectorTransport_of_gap
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (Pw : Polynomial ℝ) (ε δ : ℝ)
    (hA : ‖A‖ ≤ 1) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i)
    (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) :
    ‖(oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
      - (δ/2 : ℂ) • matrixPseudoinverse A‖ ≤ ε := by
  have h := clause40_closedSectorTransport A Pw ε δ hA hε hδ heval0 happrox
  rw [clause40_closedRightSector_eq_one_of_gap A δ hδ hgap,
    clause40_closedLeftSector_eq_one_of_gap A δ hδ hgap] at h
  simpa using! h

/-- For an input fixed by the closed left sector, the projected polynomial inverse response
differs from the scaled pseudoinverse response by at most `ε` times the input Euclidean
norm. -/
theorem clause40_thresholdSolutionBranch
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (Pw : Polynomial ℝ) (ε δ : ℝ) (b : O → ℂ)
    (hA : ‖A‖ ≤ 1) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)
    (hb : closedLeftSector A δ *ᵥ b = b) :
    qlsNormVec ((closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ) *ᵥ b
        - (δ/2 : ℂ) • (matrixPseudoinverse A *ᵥ b)) ≤ ε * qlsNormVec b := by
  have h := clause40_closedSectorTransport A Pw ε δ hA hε hδ heval0 happrox
  have heq : (closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
        - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)) *ᵥ b
      = (closedRightSector A δ * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ) *ᵥ b
        - (δ/2 : ℂ) • (matrixPseudoinverse A *ᵥ b) := by
    rw [Matrix.sub_mulVec]
    rw [← Matrix.mulVec_mulVec b]
    rw [Matrix.smul_mulVec]
    rw [← Matrix.mulVec_mulVec b]
    rw [hb]
  calc
    qlsNormVec ((closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ) *ᵥ b
        - (δ/2 : ℂ) • (matrixPseudoinverse A *ᵥ b))
      = qlsNormVec ((closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
          - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)) *ᵥ b) := by
          rw [heq]
    _ ≤ ‖closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
          - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ * qlsNormVec b :=
      l2_norm_mulVec_fromVec_le _ _
    _ ≤ ε * qlsNormVec b := mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- For `0 < ε ≤ δ ≤ 1 / 2`, there exist a bounded odd reciprocal approximation and a source
phase word with the stated length, parameter bounds, compilation counts, and closed sector
error at most `ε`. -/
theorem clause40_sourceWord_closedSector
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      ‖closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
        - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ ≤ ε := by
  obtain ⟨Pw, J, k, hbudget, h3k, hdeg, hpar, hbound, heval0, happrox⟩ :=
    theorem41WindowedPolynomial ε δ hε hεδ hδ
  have hdE : 2*J+1+2*3^k = 2*(J+3^k)+1 := by ring
  have hdiv : ∀ n : ℕ, (2*n+1)/2 = n := fun n => by omega
  have hdiv2 : ∀ n : ℕ, (2*n+1+1)/2 = n+1 := fun n => by omega
  have hmod : ∀ n : ℕ, (2*n+1)%2 = 1 := fun n => by omega
  obtain ⟨Φ, hlen, hodd, _, hcounts⟩ :=
    source_length_cpp_real_singular_transform H I O A U L R Pw (2*J+1+2*3^k) henc
      (by rw [hdE]; omega) (degree_le_of_natDegree_le hdeg) hpar hbound
  have hA1 : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  have hsector := clause40_closedSectorTransport A Pw ε δ hA1 hε.le (by linarith) heval0 happrox
  refine ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, ?_, ?_, ?_⟩
  · exact hodd (by rw [hdE]; exact hmod (J+3^k))
  · rw [hcounts, show (2*J+1+2*3^k)/2 = J+3^k from by rw [hdE]; exact hdiv (J+3^k),
      show (2*J+1+2*3^k+1)/2 = J+3^k+1 from by rw [hdE]; exact hdiv2 (J+3^k),
      show (2*(J+3^k) : ℕ) = 2*J+2*3^k from by ring,
      show (2*(J+3^k+1) : ℕ) = 2*J+2+2*3^k from by ring]
  · exact hsector

/-- The coefficient field of a sector readout is the closed sector coefficient at its singular
value. -/
theorem clause40_qlsSectorReadout_coefficient (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) :
    (qlsSectorReadout δ Pw σ).coefficient = closedSectorCoefficient δ σ := rfl

/-- The stratum field of a sector readout is the stratum assigned by `qlsStratum`. -/
theorem clause40_qlsSectorReadout_stratum (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) :
    (qlsSectorReadout δ Pw σ).stratum = qlsStratum δ σ := rfl

/-- A positive threshold is classified as the threshold stratum, with closed readout coefficient
one and strict sector coefficient zero. -/
theorem clause40_threshold_readout_kept {δ : ℝ} (hδ : 0 < δ) :
    qlsStratum δ δ = .threshold ∧
      (qlsSectorReadout δ (Polynomial.C 0) δ).coefficient = 1 ∧
      strictSectorCoefficient δ δ = 0 := by
  refine ⟨?_,
    clause40_closedSectorCoefficient_eq_one_of hδ (le_of_lt hδ) (Or.inr (le_refl δ)),
    clause40_threshold_stratum_kept hδ |>.1⟩
  · simp only [qlsStratum]
    rw [ite_eq_right (not_lt_of_ge (le_of_lt hδ)), ite_eq_left hδ,
      ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]

/-- The sector readout residual is at most `ε` for singular values in `[0, 1]` outside the
middle and negative strata, given the stated reciprocal approximation and zero value at
zero. -/
theorem clause40_qlsSectorReadout_residual_le {δ ε : ℝ} (hε : 0 ≤ ε) (_hδ : 0 < δ)
    {Pw : Polynomial ℝ} (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hkeep : qlsStratum δ σ ≠ .midBand ∧ qlsStratum δ σ ≠ .negative) :
    (qlsSectorReadout δ Pw σ).residual ≤ ε := by
  by_cases hσpos : 0 < σ
  · have hδσ : δ ≤ σ := by
      by_contra hcon
      have hlt : σ < δ := lt_of_not_ge hcon
      have hmid : qlsStratum δ σ = .midBand := by
        simp only [qlsStratum]
        rw [ite_eq_right (not_lt_of_ge (le_of_lt hσpos)), ite_eq_left hσpos, ite_eq_left hlt]
      exact absurd hmid hkeep.1
    rw [qlsSectorReadout]
    simp only [qlsWindowResidual, hσpos, ite_eq_left]
    have hx : σ ∈ Set.Icc δ 1 := ⟨hδσ, hσ1⟩
    have habs : |Pw.eval σ - (δ/2)/σ| ≤ ε := happrox σ hx
    exact habs
  · have hσ0' : σ = 0 := le_antisymm (le_of_not_gt hσpos) hσ0
    subst hσ0'
    rw [qlsSectorReadout]
    simp only [qlsWindowResidual]
    rw [heval0]
    simp [hε]

/-- A list of singular values in `[0, 1]` outside the middle and negative strata has maximum
readout residual at most `ε` under the stated polynomial hypotheses. -/
theorem clause40_qlsMaxResidual_le {δ ε : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    {Pw : Polynomial ℝ} (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)
    {σs : List ℝ} (hσs : ∀ σ ∈ σs, 0 ≤ σ ∧ σ ≤ 1)
    (hkeep : ∀ σ ∈ σs, qlsStratum δ σ ≠ .midBand ∧ qlsStratum δ σ ≠ .negative) :
    qlsMaxResidual (qlsSectorReadouts δ Pw σs) ≤ ε := by
  induction σs with
  | nil =>
      simp [qlsSectorReadouts, qlsMaxResidual]
      exact hε
  | cons σ σs ih =>
      have hmem : σ ∈ σ :: σs := by simp
      have hres := clause40_qlsSectorReadout_residual_le hε hδ heval0 happrox
        (hσs σ hmem).1 (hσs σ hmem).2 (hkeep σ hmem)
      have hσs' : ∀ τ ∈ σs, 0 ≤ τ ∧ τ ≤ 1 :=
        fun τ hτ => hσs τ (by simp [hτ])
      have hrest : ∀ τ ∈ σs,
          qlsStratum δ τ ≠ .midBand ∧ qlsStratum δ τ ≠ .negative :=
        fun τ hτ => hkeep τ (by simp [hτ])
      have hih := ih hσs' hrest
      simp only [qlsSectorReadouts, List.map_cons, qlsMaxResidual]
      exact max_le hres (by simpa using! hih)

/-- Reciprocal approximation on `[δ, 1]` with `0 < δ ≤ 1` implies that the polynomial value at
`δ` is within `ε` of `1 / 2`. -/
theorem clause40_threshold_point_consistency {ε δ : ℝ} (_hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {Pw : Polynomial ℝ} (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) :
    |Pw.eval δ - 1/2| ≤ ε := by
  have hx : δ ∈ Set.Icc δ 1 := ⟨le_rfl, hδ1⟩
  have h := happrox δ hx
  rw [show (δ/2)/δ = 1/2 by field_simp] at h
  exact h

/-- For `0 < ε ≤ δ ≤ 1 / 2`, a bounded reciprocal response has a source phase realization with
explicit counts, closed sector operator error at most `ε`, and vector error at most `ε`
times the input norm on the closed left sector. -/
theorem clause40_endpoint
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      ‖closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
        - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ ≤ ε ∧
      (∀ b : O → ℂ, closedLeftSector A δ *ᵥ b = b →
        qlsNormVec ((closedRightSector A δ
            * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ) *ᵥ b
          - (δ/2 : ℂ) • (matrixPseudoinverse A *ᵥ b)) ≤ ε * qlsNormVec b) := by
  obtain ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, henc', hcounts, hsector⟩ :=
    clause40_sourceWord_closedSector H I O A U L R ε δ henc hε hεδ hδ
  have hA1 : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  refine ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, henc', hcounts, hsector, ?_⟩
  intro b hb
  exact clause40_thresholdSolutionBranch A Pw ε δ b hA1 hε.le (by linarith) heval0 happrox hb

/-- With the stated logarithmic choice of `k` and bound on `J`, the window error power is at
most `2 * min (1 / (8 * J)) (ε / (32 * J))`. -/
private theorem clause40_windowError_small {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    {J : ℕ} (hJ2 : 2 ≤ J) (hbudget : (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)))
    {L : ℝ} (hLdef : L = Real.log (64/(δ*ε))) {k : ℕ}
    (hkdef : k = Nat.ceil (Real.log (256*L/(9*δ^4))/Real.log 2)) :
    (1-(3*δ*δ/8)^2)^(2^k)
      ≤ 2*min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) := by
  have hJpos : (0:ℝ) < J := by exact_mod_cast (by omega : (0:ℕ) < J)
  have hδε : δ*ε ≤ 1/4 := by
    have h := mul_le_mul hδ1 hε1 (le_of_lt hε) (by norm_num)
    calc δ*ε ≤ (1/2)*(1/2) := h
      _ = 1/4 := by norm_num
  have hA8 : (8:ℝ) ≤ 64/(δ*ε) := by
    rw [le_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
    nlinarith [hδε]
  have hL2 : (2:ℝ) ≤ L := by
    have he2 : Real.exp 2 ≤ 8 := by
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      have hup : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      have hE44 : Real.exp 1 ≤ 11/4 := hup.le.trans (by norm_num : (2.72:ℝ) ≤ 11/4)
      have hsq : (Real.exp 1)*(Real.exp 1) ≤ (11/4)*(11/4) :=
        mul_le_mul hE44 hE44 (by positivity) (by positivity)
      have h7 : (11/4:ℝ)*(11/4) ≤ 8 := by norm_num
      linarith
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    linarith

  have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 8) hA8)
  have hvpos : (0:ℝ) < 256*L/(9*δ^4) :=
    div_pos (mul_pos (by norm_num) hLpos) (mul_pos (by norm_num) (pow_pos hδ 4))
  have h2v : 256*L/(9*δ^4) ≤ (2:ℝ)^((k:ℝ)) := by
    have h1 : Real.log (256*L/(9*δ^4))/Real.log 2 ≤ (k:ℝ) := by
      have h := Nat.le_ceil (Real.log (256*L/(9*δ^4))/Real.log 2)
      rw [← hkdef] at h
      exact_mod_cast h
    have h2 : (2:ℝ)^(Real.log (256*L/(9*δ^4))/Real.log 2) = 256*L/(9*δ^4) := by
      rw [Real.rpow_def_of_pos (show (0:ℝ) < 2 by norm_num)]
      have harg : Real.log 2*(Real.log (256*L/(9*δ^4))/Real.log 2)
          = Real.log (256*L/(9*δ^4)) := by
        field_simp
      rw [harg, Real.exp_log hvpos]
    calc 256*L/(9*δ^4) = (2:ℝ)^(Real.log (256*L/(9*δ^4))/Real.log 2) := h2.symm
      _ ≤ (2:ℝ)^((k:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hrw : ((2^k : ℕ):ℝ) = (2:ℝ)^((k:ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.rpow_natCast 2 k).symm
  have hγ2k : 4*L ≤ (3*δ*δ/8)^2*((2^k : ℕ):ℝ) := by
    have hle : 4*L ≤ (3*δ*δ/8)^2*(2:ℝ)^((k:ℝ)) := by
      have h1 : (3*δ*δ/8)^2*(256*L/(9*δ^4)) = 4*L := by
        field_simp
        norm_num
      calc 4*L = (3*δ*δ/8)^2*(256*L/(9*δ^4)) := h1.symm
        _ ≤ (3*δ*δ/8)^2*(2:ℝ)^((k:ℝ)) :=
            mul_le_mul_of_nonneg_left h2v (show (0:ℝ) ≤ (3*δ*δ/8)^2 by positivity)
    rw [hrw]
    exact hle

  have hη : min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) = ε/(32*(J:ℝ)) := by
    refine min_eq_right ?_
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hJpos) (mul_pos (by norm_num) hJpos)]
    nlinarith [hε, hJpos, hε1]

  have hL' : Real.log (16/(δ*ε)) ≤ L := by
    rw [hLdef]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hδ, hε]
  have hJL : (J:ℝ)*δ ≤ 32*L := by
    have hb : (2*(J:ℝ)+1) ≤ (64/δ)*Real.log (16/(δ*ε)) := by
      have h := hbudget
      rwa [show 32*(2/δ) = 64/δ from by ring] at h
    have h1 : (2*(J:ℝ)+1)*δ ≤ 64*Real.log (16/(δ*ε)) := by
      calc (2*(J:ℝ)+1)*δ ≤ ((64/δ)*Real.log (16/(δ*ε)))*δ :=
            mul_le_mul_of_nonneg_right hb hδ.le
        _ = 64*Real.log (16/(δ*ε)) := by
            rw [mul_assoc, mul_comm (Real.log (16/(δ*ε))) δ, ← mul_assoc,
              div_mul_cancel₀ _ hδ.ne']
    nlinarith [h1, hL']
  have hlogη : Real.log (16*(J:ℝ)/ε) ≤ 4*L := by
    have hexpL : Real.exp L = 64/(δ*ε) := by
      rw [hLdef]
      exact Real.exp_log (by positivity)
    have h2 : 16*(J:ℝ)/ε ≤ 8*L*Real.exp L := by
      rw [hexpL, div_le_iff₀ hε,
        show 8*L*(64/(δ*ε))*ε = 512*L/δ from by field_simp; norm_num, le_div_iff₀ hδ]
      nlinarith [hJL]
    have h3 : Real.log (8*L*Real.exp L) ≤ 4*L := by
      have hlogmul : Real.log (8*L*Real.exp L) = Real.log 8+Real.log L+L := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) hLpos.ne') (Real.exp_ne_zero _),
          Real.log_mul (by norm_num) hLpos.ne', Real.log_exp L]
      have hln8 : Real.log 8 ≤ 3 := by
        have hE : (2.7:ℝ) ≤ Real.exp 1 :=
          ((by norm_num : (2.7:ℝ) ≤ 2.7182818283).trans_lt Real.exp_one_gt_d9).le
        have h1 : (2.7:ℝ)*(2.7:ℝ) ≤ (Real.exp 1)*(Real.exp 1) :=
          mul_le_mul hE hE (by positivity) (by positivity)
        have h2 : (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ)
            ≤ (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) := by
          have t : (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ) ≤ ((Real.exp 1)*(Real.exp 1))*(Real.exp 1) :=
            mul_le_mul h1 hE (by positivity) (by positivity)
          rw [show ((Real.exp 1)*(Real.exp 1))*(Real.exp 1)
              = (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) from by ring] at t
          exact t
        have he : Real.exp 3 = (Real.exp 1)*((Real.exp 1)*(Real.exp 1)) := by
          rw [show (3:ℝ) = 1+1+1 from by norm_num, Real.exp_add, Real.exp_add]
          ring
        have h8 : (8:ℝ) ≤ (2.7:ℝ)*(2.7:ℝ)*(2.7:ℝ) := by norm_num
        exact (Real.log_le_log (by norm_num) (by linarith)).trans (Real.log_exp 3).le
      have hlnL : Real.log L ≤ L-1 := Real.log_le_sub_one_of_pos hLpos
      rw [hlogmul]
      nlinarith
    exact (Real.log_le_log (div_pos (by nlinarith [hJpos]) hε) h2).trans h3

  have hδ2le : δ*δ ≤ 1/4 := by nlinarith [hδ1, hδ]
  have hγ1 : (3*δ*δ/8)^2 ≤ 1 := by
    have h4 : (δ*δ)*(δ*δ) ≤ 1/16 := by
      have t : (δ*δ)*(δ*δ) ≤ (1/4)*(1/4) :=
        mul_le_mul hδ2le hδ2le (by positivity) (by positivity)
      rw [show (1/4:ℝ)*(1/4) = 1/16 from by norm_num] at t
      exact t
    nlinarith [h4]
  have hbase : 1-(3*δ*δ/8)^2 ≤ Real.exp (-(3*δ*δ/8)^2) := by
    have h := Real.add_one_le_exp (-(3*δ*δ/8)^2)
    linarith
  rw [hη]
  refine le_trans (pow_le_pow_left₀ (by nlinarith [hγ1]) hbase (2^k)) ?_
  have hle : ((2^k : ℕ):ℝ)*(-(3*δ*δ/8)^2) ≤ Real.log (2*(ε/(32*(J:ℝ)))) := by
    have hlrw : Real.log (2*(ε/(32*(J:ℝ)))) = -(Real.log (16*(J:ℝ)/ε)) := by
      rw [show 2*(ε/(32*(J:ℝ))) = (16*(J:ℝ)/ε)⁻¹ from by field_simp; ring, Real.log_inv]
    rw [hlrw]
    nlinarith [hγ2k, hlogη]
  calc (Real.exp (-(3*δ*δ/8)^2))^(2^k)
      = Real.exp (((2^k : ℕ):ℝ)*(-(3*δ*δ/8)^2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log (2*(ε/(32*(J:ℝ))))) := Real.exp_le_exp.mpr hle
    _ = 2*(ε/(32*(J:ℝ))) :=
        Real.exp_log (mul_pos (by norm_num) (div_pos hε (by nlinarith [hJpos])))

/-- For independently chosen `0 < ε ≤ 1 / 2` and `0 < δ ≤ 1 / 2`, there is a bounded odd
polynomial vanishing at zero and approximating `(δ / 2) / x` on `[δ, 1]`, with the stated
degree and parameter bounds. -/
theorem clause40_relaxedWindowedReciprocal (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ),
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (2*J+1+2*3^k) Pw ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) := by
  have hδε : δ*ε ≤ 1/4 := by
    have h := mul_le_mul hδ1 hε1 (le_of_lt hε) (by norm_num)
    calc δ*ε ≤ (1/2)*(1/2) := h
      _ = 1/4 := by norm_num
  obtain ⟨hb1, hJ2, hgdeg, hgpar, hgeval0, hbudget⟩ :=
    nearOptimalReciprocal_family_degree_parity (2/δ) (ε/8)
      (by rw [lt_div_iff₀ hδ]; nlinarith) (by positivity) (by nlinarith [hε1])
  obtain ⟨herr1, herr2, hsize, herr12, hscaled⟩ :=
    nearOptimalReciprocal_error_bounds (2/δ) (ε/8)
      (by rw [lt_div_iff₀ hδ]; nlinarith) (by positivity) (by nlinarith [hε1])
  set J := nearOptimalReciprocalJ (2/δ) (ε/8) with hJdef
  set g := nearOptimalReciprocalPolynomial (2/δ) (ε/8) with hgdef
  set L := Real.log (64/(δ*ε)) with hLdef
  set k := Nat.ceil (Real.log (256*L/(9*δ^4))/Real.log 2) with hkdef
  set τ₀ := δ*Real.sqrt (5/8) with hτdef
  set γ := 3*δ*δ/8 with hγdef
  set η := min (1/(8*(J:ℝ))) (ε/(32*(J:ℝ))) with hηdef
  set w := thresholdPolynomial τ₀ k with hwdef
  set c' := (δ/2)*(1-ε/4) with hcdef
  have hJpos : (0:ℝ) < J := by exact_mod_cast (by omega : (0:ℕ) < J)
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
    nlinarith [hδε, hδ, hε]
  have hL2 : (2:ℝ) ≤ L := by
    have he2 : Real.exp 2 ≤ 8 := by
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      have hup : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      have hE44 : Real.exp 1 ≤ 11/4 := hup.le.trans (by norm_num : (2.72:ℝ) ≤ 11/4)
      have hsq : (Real.exp 1)*(Real.exp 1) ≤ (11/4)*(11/4) :=
        mul_le_mul hE44 hE44 (by positivity) (by positivity)
      have h7 : (11/4:ℝ)*(11/4) ≤ 8 := by norm_num
      linarith
    have hA8 : (8:ℝ) ≤ 64/(δ*ε) := by
      rw [le_div_iff₀ (show (0:ℝ) < δ*ε by positivity)]
      nlinarith [hδε]
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    linarith
  have hτ01 : τ₀ ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    calc τ₀ = δ*Real.sqrt (5/8) := hτdef
      _ ≤ δ*1 := by
          have h := Real.sqrt_le_sqrt (by norm_num : (5/8:ℝ) ≤ 1)
          rw [Real.sqrt_one] at h
          exact mul_le_mul_of_nonneg_left h hδ.le
      _ ≤ 1 := by nlinarith
  have hτsq : τ₀*τ₀ = δ*δ*(5/8) := by
    rw [hτdef]
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5/8 by norm_num)
    nlinarith [Real.sqrt_nonneg (5/8 : ℝ)]
  have hγpos : 0 < γ := by positivity
  have hηε : η = ε/(32*(J:ℝ)) := by
    rw [hηdef]
    refine min_eq_right ?_
    rw [div_le_div_iff₀ (show (0:ℝ) < 32*(J:ℝ) by nlinarith)
      (show (0:ℝ) < 8*(J:ℝ) by nlinarith)]
    nlinarith [hε, hJpos, hε1]
  rw [show (2/δ)/(ε/8) = 16/(δ*ε) from by field_simp; ring] at hbudget
  have hbudget2 : (2*(J:ℝ)+1) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using! hbudget
  have hwerr := clause40_windowError_small hε hε1 hδ hδ1 hJ2 hbudget2 hLdef hkdef
  have herrη : signPolynomialError γ k/2 ≤ η := by
    have h2 := hwerr
    unfold signPolynomialError at h2 ⊢
    rw [← hγdef, ← hηdef] at h2
    nlinarith

  have hwlow : ∀ x : ℝ, |x| ≤ δ/2 → |w.eval x| ≤ η := by
    intro x hx
    have hx2 : x*x ≤ δ*δ/4 := by
      have hx' := mul_le_mul hx hx (abs_nonneg x) (by nlinarith : (0:ℝ) ≤ δ/2)
      rw [abs_mul_abs_self x] at hx'
      linarith
    have hind : thresholdIndicator τ₀ x = 0 := by
      unfold thresholdIndicator
      rw [ite_eq_right]
      nlinarith
    have hgap : γ ≤ |x^2-τ₀^2| := by
      have hz : x^2-τ₀^2 ≤ -γ := by nlinarith
      rw [hγdef]
      rw [abs_of_nonpos (by nlinarith [hτsq, hx2])]
      nlinarith
    have herr := thresholdPolynomial_error_le k hτ01 hγpos hgap
      (le_trans hx (by nlinarith : δ/2 ≤ 1))
    rw [hind, zero_sub, abs_neg] at herr
    exact herr.trans herrη
  have hwhigh : ∀ x : ℝ, x ∈ Set.Icc δ 1 → 1-η ≤ w.eval x ∧ w.eval x ≤ 1 := by
    intro x hx
    have hxδ : δ ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hmem := thresholdPolynomial_eval_mem_Icc k hτ01 (abs_le.mpr ⟨by nlinarith, hx1⟩)
    have hind : thresholdIndicator τ₀ x = 1 := by
      unfold thresholdIndicator
      rw [ite_eq_left]
      nlinarith
    have hgap : γ ≤ |x^2-τ₀^2| := by
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have herr := thresholdPolynomial_error_le k hτ01 hγpos hgap
      (abs_le.mpr ⟨by nlinarith [hx1], by nlinarith [hx1]⟩)
    rw [hind] at herr
    constructor
    · have habs := abs_le.mp (herr.trans herrη)
      linarith [habs.1, habs.2]
    · exact hmem.2
  have hc'pos : 0 < c' := by
    have h4 : (0:ℝ) < 1-ε/4 := by nlinarith
    rw [hcdef]
    nlinarith [hδ, h4]
  refine ⟨C c'*(g*w), J, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using! hbudget
  · have hδ2 : (0:ℝ) ≤ δ*δ := by positivity
    have hδ2le : δ*δ ≤ 1/4 := by nlinarith [hδ1, hδ]
    have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hln3le2 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 3)]
      have hE : (27/10:ℝ) ≤ Real.exp 1 :=
        ((by norm_num : (27/10:ℝ) ≤ 2.7182818283).trans_lt Real.exp_one_gt_d9).le
      have h1 : (27/10:ℝ)*(27/10:ℝ) ≤ (Real.exp 1)*(Real.exp 1) :=
        mul_le_mul hE hE (by positivity) (by positivity)
      have h3 : (3:ℝ) ≤ (27/10:ℝ)*(27/10:ℝ) := by norm_num
      have he : Real.exp 2 = (Real.exp 1)*(Real.exp 1) := by
        rw [show (2:ℝ) = 1+1 from by norm_num, Real.exp_add]
      linarith
    have hln256 : Real.log 256 ≤ 8 := by
      have hln2le1 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
        exact (lt_of_le_of_lt (by norm_num : (2:ℝ) ≤ 2.7182818283)
          Real.exp_one_gt_d9).le
      have h256 : Real.log 256 = 8*Real.log 2 := by
        rw [show (256:ℝ) = (2:ℝ)^(8:ℕ) from by norm_num, Real.log_pow]
        norm_num
      rw [h256]
      linarith
    have hinv' : Real.log ((δ:ℝ)⁻¹)*(δ*δ) ≤ 2 := by
      have h1 : Real.log ((δ:ℝ)⁻¹) ≤ (δ:ℝ)⁻¹ :=
        Real.log_le_self (inv_pos.2 hδ).le
      have h2 : ((δ:ℝ)⁻¹)*(δ*δ) ≤ 2 := by
        rw [show ((δ:ℝ)⁻¹)*(δ*δ) = δ from by field_simp]
        nlinarith [hδ]
      exact (mul_le_mul_of_nonneg_right h1 hδ2).trans h2

    have hlnv : (Real.log (256*L/(9*δ^4)))*(δ*δ) ≤ (8+L)*(δ*δ)+8 := by
      have hsplit : Real.log (256*L/(9*δ^4))*(δ*δ)
          = (Real.log 256+Real.log L-Real.log 9)*(δ*δ)
            +4*Real.log ((δ:ℝ)⁻¹)*(δ*δ) := by
        rw [Real.log_div (by positivity)
            (mul_ne_zero (by norm_num) (pow_ne_zero 4 hδ.ne')),
            Real.log_mul (by norm_num) hLpos.ne',
            Real.log_mul (by norm_num) (pow_ne_zero 4 hδ.ne'),
            Real.log_pow δ 4, Real.log_inv δ]
        ring
      rw [hsplit]
      have hlnL : Real.log L ≤ L := Real.log_le_self hLpos.le
      have hln9 : (0:ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
      have hp1 := mul_le_mul_of_nonneg_right hln256 hδ2
      have hp2 := mul_le_mul_of_nonneg_right hlnL hδ2
      have hp3 := mul_le_mul_of_nonneg_right hln9 hδ2
      nlinarith [hp1, hp2, hp3, hinv']
    have hvge1 : (1:ℝ) ≤ 256*L/(9*δ^4) := by
      have hδ4 : δ^4 ≤ 1/16 := by nlinarith [hδ2le, hδ2]
      rw [le_div_iff₀ (mul_pos (by norm_num) (pow_pos hδ 4))]
      nlinarith [hL2, hδ4]
    have hlnvnn : (0:ℝ) ≤ Real.log (256*L/(9*δ^4)) := Real.log_nonneg hvge1
    have hln2 : Real.log 2 ≠ 0 := hln2pos.ne'
    have hkup : (k:ℝ) ≤ Real.log (256*L/(9*δ^4))/Real.log 2+1 := by
      have hnn : (0:ℝ) ≤ Real.log (256*L/(9*δ^4))/Real.log 2 :=
        div_nonneg hlnvnn hln2pos.le
      have hlt := Nat.ceil_lt_add_one hnn
      rw [← hkdef] at hlt
      linarith
    have hratio : Real.log 3/Real.log 2 ≤ 2 := by
      have hln4 : Real.log ((2:ℝ)^(2:ℕ)) = 2*Real.log 2 := by
        rw [Real.log_pow]
        norm_num
      rw [div_le_iff₀ hln2pos, ← hln4]
      exact Real.log_le_log (by norm_num) (by norm_num : (3:ℝ) ≤ (2:ℝ)^(2:ℕ))
    have hq : (Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3
        ≤ 2*Real.log (256*L/(9*δ^4)) := by
      have hrw2 : (Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3
          = (Real.log 3/Real.log 2)*Real.log (256*L/(9*δ^4)) := by ring
      rw [hrw2]
      exact mul_le_mul_of_nonneg_right hratio hlnvnn
    have hkln3 : (k:ℝ)*Real.log 3
        ≤ Real.log 3+2*Real.log (256*L/(9*δ^4)) := by
      have h1 := mul_le_mul_of_nonneg_right hkup (show (0:ℝ) ≤ Real.log 3 by positivity)
      have hrw3 : (Real.log (256*L/(9*δ^4))/Real.log 2+1)*Real.log 3
          = Real.log 3+(Real.log (256*L/(9*δ^4))/Real.log 2)*Real.log 3 := by ring
      rw [hrw3] at h1
      linarith [h1, hq]
    have hfinal1 : (k:ℝ)*Real.log 3*(δ*δ) ≤ 12*L := by
      have h1 : (k:ℝ)*Real.log 3*(δ*δ)
          ≤ (Real.log 3+2*Real.log (256*L/(9*δ^4)))*(δ*δ) :=
        mul_le_mul_of_nonneg_right hkln3 hδ2
      have hp5 : Real.log 3*(δ*δ) ≤ 2*(δ*δ) :=
        mul_le_mul_of_nonneg_right hln3le2 hδ2
      have hpL : (0:ℝ) ≤ L := le_trans (by norm_num) hL2
      have hLd := mul_le_mul_of_nonneg_left hδ2le hpL
      linarith
    have h3k : Real.exp ((k:ℝ)*Real.log 3) = (3:ℝ)^k := by
      rw [← Real.log_pow (3:ℝ) k, Real.exp_log (by norm_num : (0:ℝ) < (3:ℝ)^k)]
    have hArw : Real.exp (12*L/(δ*δ)) = (64/(δ*ε))^(12/(δ*δ)) := by
      rw [Real.rpow_def_of_pos (show (0:ℝ) < 64/(δ*ε) by positivity), ← hLdef]
      congr 1
      ring
    have hApos : (0:ℝ) < (64/(δ*ε))^(12/(δ*δ)) :=
      Real.rpow_pos_of_pos (show (0:ℝ) < 64/(δ*ε) by positivity) _
    calc (3:ℝ)^k = Real.exp ((k:ℝ)*Real.log 3) := h3k.symm
      _ ≤ Real.exp (12*L/(δ*δ)) := Real.exp_le_exp.mpr (by
        rw [le_div_iff₀ (show (0:ℝ) < δ*δ by positivity)]
        exact hfinal1)
      _ = (64/(δ*ε))^(12/(δ*δ)) := hArw
      _ ≤ 3*(64/(δ*ε))^(12/(δ*δ)) := le_mul_of_one_le_left hApos.le (by norm_num : (1:ℝ) ≤ 3)
  · have hgn := natDegree_le_of_degree_le hgdeg
    have hwn := thresholdPolynomial_natDegree_le τ₀ k
    calc (C c'*(g*w)).natDegree ≤ (C c').natDegree+(g*w).natDegree := natDegree_mul_le
      _ = (g*w).natDegree := by
          rw [natDegree_C, zero_add]
      _ ≤ g.natDegree+w.natDegree := natDegree_mul_le
      _ ≤ 2*J+1+2*3^k := add_le_add hgn hwn
  · change g.comp (-X) = C ((-1:ℝ)^(2*J+1))*g at hgpar
    unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    rw [mul_comp, C_comp, mul_comp, hgpar, thresholdPolynomial_comp_neg_X]
    have hodd1 : Odd (2*J+1) := ⟨J, rfl⟩
    have hodd2 : Odd (2*J+1+2*3^k) := ⟨J+3^k, by ring⟩
    rw [hodd1.neg_one_pow, hodd2.neg_one_pow]
    ring
  · intro x hx
    rcases le_or_gt (abs x) (δ/2) with hlow | hhigh
    · have hw := hwlow x hlow
      have hg := hsize x hx
      have hη1 : η ≤ 1/(8*(J:ℝ)) := min_le_left _ _
      have hprod : (|g.eval x|)*(|w.eval x|) ≤ 4*(J:ℝ)*(1/(8*(J:ℝ))) :=
        mul_le_mul hg (hw.trans hη1) (abs_nonneg _) (by nlinarith [hJpos])
      have hval : 4*(J:ℝ)*(1/(8*(J:ℝ))) = 1/2 := by field_simp; ring
      rw [hval] at hprod
      have hc'le : c' ≤ δ/2 := by rw [hcdef]; nlinarith
      calc |(C c'*(g*w)).eval x| = c'*((|g.eval x|)*(|w.eval x|)) := by
            simp only [eval_mul, eval_C, abs_mul, abs_of_pos hc'pos]
        _ ≤ c'*(1/2) := mul_le_mul_of_nonneg_left hprod hc'pos.le
        _ ≤ (δ/2)*(1/2) := by nlinarith [hc'le]
        _ ≤ 1 := by nlinarith
    · have hax1 : |x| ≤ 1 := abs_le.mpr ⟨by nlinarith [hx.1, hx.2], hx.2⟩
      have hwm : w.eval x ∈ Set.Icc (0:ℝ) 1 := thresholdPolynomial_eval_mem_Icc k hτ01 hax1
      have hinvle : |(x:ℝ)⁻¹| ≤ 2/δ := by
        have hxinv : ((0:ℝ) < |x|) :=
          lt_trans (show (0:ℝ) < δ/2 by nlinarith [hδ]) hhigh
        have h1 : (1:ℝ)/|x| ≤ 1/(δ/2) :=
          (one_div_le_one_div hxinv (by nlinarith [hδ])).mpr hhigh.le
        rw [abs_inv, inv_eq_one_div, show 2/δ = 1/(δ/2) from by ring]
        exact h1
      have hginv : |g.eval x-(x:ℝ)⁻¹| ≤ 2*(ε/8) := by
        rcases lt_or_ge x 0 with hxneg | hxpos2
        · have hgev : g.eval (-x) = -(g.eval x) := by
            have h2 : g.comp (-X) = C ((-1:ℝ)^(2*J+1))*g := hgpar
            have h1 : (g.comp (-X)).eval x = ((C ((-1:ℝ)^(2*J+1))*g)).eval x := by
              rw [h2]
            rw [Polynomial.eval_comp, eval_neg, eval_X, eval_mul, eval_C] at h1
            rw [h1, show ((-1:ℝ)^(2*J+1)) = -1 from Odd.neg_one_pow ⟨J, rfl⟩]
            ring
          rw [abs_of_neg hxneg] at hhigh
          have hu : -x ∈ Set.Icc ((2:ℝ)/δ)⁻¹ 1 := by
            refine ⟨by rw [inv_div]; linarith, by linarith [hx.1]⟩
          have hg' := herr12 (-x) hu
          have hconv : (-g.eval x)-(-((x:ℝ)⁻¹)) = -(g.eval x-(x:ℝ)⁻¹) := by ring
          rw [hgev, inv_neg, hconv, abs_neg] at hg'
          exact hg'
        · rw [abs_of_nonneg hxpos2] at hhigh
          exact herr12 x ⟨by rw [inv_div]; linarith, (abs_le.mp hax1).2⟩
      have hwm1 : |w.eval x| ≤ 1 := abs_le.mpr ⟨by linarith [hwm.1], hwm.2⟩
      have htri : |g.eval x| ≤ |(x:ℝ)⁻¹|+|g.eval x-(x:ℝ)⁻¹| := by
        calc |g.eval x| = |(g.eval x-(x:ℝ)⁻¹)+(x:ℝ)⁻¹| := by ring
          _ ≤ |g.eval x-(x:ℝ)⁻¹|+|(x:ℝ)⁻¹| := abs_add_le _ _
          _ = |(x:ℝ)⁻¹|+|g.eval x-(x:ℝ)⁻¹| := by ring
      have hgle : |g.eval x| ≤ 2/δ+ε/4 := by
        have h2 : 2*(ε/8) = ε/4 := by ring
        linarith [htri, hginv, hinvle, h2]
      calc |(C c'*(g*w)).eval x| = c'*((|g.eval x|)*(|w.eval x|)) := by
            simp only [eval_mul, eval_C, abs_mul, abs_of_pos hc'pos]
        _ ≤ c'*((2/δ+ε/4)*1) := by
            refine mul_le_mul_of_nonneg_left ?_ hc'pos.le
            have hpp : (0:ℝ) < 2/δ+ε/4 :=
              add_pos (div_pos (by norm_num) hδ) (by nlinarith [hε])
            exact mul_le_mul hgle hwm1 (abs_nonneg _) hpp.le
        _ = (δ/2)*(1-ε/4)*(2/δ+ε/4) := by rw [hcdef]; ring
        _ ≤ 1 := by
            have hkey : (δ/2)*(1-ε/4)*(2/δ+ε/4)
                = 1 - ε/4 + (δ*ε/8) - (δ*ε/8)*(ε/4) := by
              field_simp [hδ.ne']; ring
            rw [hkey]
            have h1 : (δ*ε/8) ≤ (ε/4) := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
              nlinarith [hδ, hδ1]
            have hdεε : (0:ℝ) ≤ δ*ε*ε :=
              mul_nonneg (mul_nonneg hδ.le hε.le) hε.le
            linarith [h1, hdεε]
  · simp only [eval_mul, eval_C, hgeval0]
    ring
  · intro x hx
    have hxδ : δ ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hxpos : 0 < x := by nlinarith
    have hax : |x| = x := abs_of_pos hxpos
    have hw1 : 1-η ≤ w.eval x := (hwhigh x hx).1
    have hw2 : w.eval x ≤ 1 := (hwhigh x hx).2
    have hg4 : |g.eval x| ≤ 4*(J:ℝ) := hsize x ⟨by nlinarith, hx1⟩
    have hginv := herr12 x ⟨by rw [inv_div]; linarith, hx1⟩
    have hwinv : |w.eval x-1| ≤ η := by
      have h1 : |1-w.eval x| ≤ η := abs_le.mpr ⟨by linarith [hw1], by nlinarith [hw2]⟩
      rw [abs_sub_comm]
      exact h1
    have hdecomp : c'*(g.eval x*(w.eval x))-(δ/2)/x
        = c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹) := by
      rw [div_eq_inv_mul]
      ring
    have hδε0 : (0:ℝ) ≤ δ*ε := mul_nonneg hδ.le hε.le
    have hsubq : (δ/2)*(1-ε/4) ≤ 1/4 := by nlinarith [hδ1, hδε0]
    have t1 : |c'*(g.eval x)*(w.eval x-1)| ≤ ε/32 := by
      have hstep : |c'*(g.eval x)*(w.eval x-1)| ≤ c'*(4*(J:ℝ)*(ε/(32*(J:ℝ)))) := by
        calc |c'*(g.eval x)*(w.eval x-1)| = c'*((|g.eval x|)*(|w.eval x-1|)) := by
              simp only [abs_mul, abs_of_pos hc'pos, mul_assoc]
          _ ≤ c'*(4*(J:ℝ)*(ε/(32*(J:ℝ)))) := by
              refine mul_le_mul_of_nonneg_left ?_ hc'pos.le
              exact mul_le_mul hg4 (hwinv.trans_eq hηε) (abs_nonneg _)
                (by nlinarith [hJpos] : (0:ℝ) ≤ 4*(J:ℝ))
      have hval : 4*(J:ℝ)*(ε/(32*(J:ℝ))) = ε/8 := by field_simp; ring
      have hkey2 : (δ/2)*(1-ε/4)*(ε/8) ≤ ε/32 := by
        have hmul := mul_le_mul_of_nonneg_right hsubq
          (by nlinarith [hε] : (0:ℝ) ≤ ε/8)
        have hfin : (1/4:ℝ)*(ε/8) = ε/32 := by ring
        linarith [hmul, hfin]
      rw [hval, hcdef] at hstep
      linarith [hstep, hkey2]
    have t2 : |c'*(g.eval x-(x:ℝ)⁻¹)| ≤ ε/16 := by
      have habs : |c'*(g.eval x-(x:ℝ)⁻¹)| = c'*|g.eval x-(x:ℝ)⁻¹| := by
        rw [abs_mul, abs_of_pos hc'pos]
      rw [habs]
      have hstep : c'*|g.eval x-(x:ℝ)⁻¹| ≤ c'*(2*(ε/8)) :=
        mul_le_mul_of_nonneg_left hginv hc'pos.le
      have hkey3 : (δ/2)*(1-ε/4)*(2*(ε/8)) ≤ ε/16 := by
        have hmul := mul_le_mul_of_nonneg_right hsubq
          (by nlinarith [hε] : (0:ℝ) ≤ 2*(ε/8))
        have hfin : (1/4:ℝ)*(2*(ε/8)) = ε/16 := by ring
        linarith [hmul, hfin]
      rw [hcdef] at hstep ⊢
      linarith [hstep, hkey3]
    have t3 : |(c'-(δ/2))*((x:ℝ)⁻¹)| ≤ ε/8 := by
      have hc : c'-(δ/2) = -(δ/2)*(ε/4) := by rw [hcdef]; ring
      have hinvle : |((x:ℝ)⁻¹)| ≤ 1/δ := by
        rw [abs_inv, abs_of_pos hxpos, inv_eq_one_div]
        exact one_div_le_one_div_of_le hδ hxδ
      rw [hc]
      calc |(-(δ/2)*(ε/4))*((x:ℝ)⁻¹)| = ((δ/2)*(ε/4))*|((x:ℝ)⁻¹)| := by
            rw [show (-(δ/2)*(ε/4))*((x:ℝ)⁻¹)
                  = -(((δ/2)*(ε/4))*((x:ℝ)⁻¹)) from by ring,
              abs_neg, abs_mul, abs_of_pos (by positivity)]
        _ ≤ ((δ/2)*(ε/4))*(1/δ) := mul_le_mul_of_nonneg_left hinvle (by positivity)
        _ = ε/8 := by field_simp; ring
    simp only [eval_mul, eval_C]
    rw [hdecomp]
    calc |c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹)|
        ≤ |c'*(g.eval x)*(w.eval x-1)|
          +|c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹)| := by
            have hrw : c'*(g.eval x)*(w.eval x-1)
                +(c'*(g.eval x-(x:ℝ)⁻¹)+(c'-(δ/2))*((x:ℝ)⁻¹))
                = c'*(g.eval x)*(w.eval x-1)+c'*(g.eval x-(x:ℝ)⁻¹)
                  +(c'-(δ/2))*((x:ℝ)⁻¹) := by ring
            rw [← hrw]
            exact abs_add_le _ _
      _ ≤ |c'*(g.eval x)*(w.eval x-1)|
          +(|c'*(g.eval x-(x:ℝ)⁻¹)|+|(c'-(δ/2))*((x:ℝ)⁻¹)|) :=
          add_le_add (le_refl _) (abs_add_le _ _)
      _ ≤ ε/32+(ε/16+ε/8) := add_le_add t1 (add_le_add t2 t3)
      _ ≤ ε := by nlinarith [hε]

/-- The relaxed windowed reciprocal construction applies to `0 < ε ≤ δ ≤ 1 / 2` with the same
degree, parity, boundedness, and approximation estimates. -/
theorem clause40_relaxedWindow_frozenSpecialisation (ε δ : ℝ) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ),
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (2*J+1+2*3^k) Pw ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) :=
  clause40_relaxedWindowedReciprocal ε δ hε (hεδ.trans hδ) (lt_of_lt_of_le hε hεδ) hδ

/-- For independent positive `ε` and `δ` at most one half, a source phase word realizes a
bounded reciprocal response with the stated length, counts, and closed sector error at most
`ε`. -/
theorem clause40_sourceWord_relaxedWindow
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      ‖closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
        - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ ≤ ε := by
  obtain ⟨Pw, J, k, hbudget, h3k, hdeg, hpar, hbound, heval0, happrox⟩ :=
    clause40_relaxedWindowedReciprocal ε δ hε hε1 hδ hδ1
  have hdE : 2*J+1+2*3^k = 2*(J+3^k)+1 := by ring
  have hdiv : ∀ n : ℕ, (2*n+1)/2 = n := fun n => by omega
  have hdiv2 : ∀ n : ℕ, (2*n+1+1)/2 = n+1 := fun n => by omega
  have hmod : ∀ n : ℕ, (2*n+1)%2 = 1 := fun n => by omega
  obtain ⟨Φ, hlen, hodd, _, hcounts⟩ :=
    source_length_cpp_real_singular_transform H I O A U L R Pw (2*J+1+2*3^k) henc
      (by rw [hdE]; omega) (degree_le_of_natDegree_le hdeg) hpar hbound
  have hA1 : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  have hsector := clause40_closedSectorTransport A Pw ε δ hA1 hε.le hδ heval0 happrox
  refine ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, ?_, ?_, ?_⟩
  · exact hodd (by rw [hdE]; exact hmod (J+3^k))
  · rw [hcounts, show (2*J+1+2*3^k)/2 = J+3^k from by rw [hdE]; exact hdiv (J+3^k),
      show (2*J+1+2*3^k+1)/2 = J+3^k+1 from by rw [hdE]; exact hdiv2 (J+3^k),
      show (2*(J+3^k) : ℕ) = 2*J+2*3^k from by ring,
      show (2*(J+3^k+1) : ℕ) = 2*J+2+2*3^k from by ring]
  · exact hsector

/-- For independent positive `ε` and `δ` at most one half, a bounded reciprocal response has a
counted source word with closed sector operator error at most `ε` and the corresponding
vector error estimate. -/
theorem clause40_endpoint_noEpsLeDelta
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      ‖closedRightSector A δ
          * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
          * closedLeftSector A δ
        - (δ/2 : ℂ) • (matrixPseudoinverse A * closedLeftSector A δ)‖ ≤ ε ∧
      (∀ b : O → ℂ, closedLeftSector A δ *ᵥ b = b →
        qlsNormVec ((closedRightSector A δ
            * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ) *ᵥ b
          - (δ/2 : ℂ) • (matrixPseudoinverse A *ᵥ b)) ≤ ε * qlsNormVec b) := by
  obtain ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, henc', hcounts, hsector⟩ :=
    clause40_sourceWord_relaxedWindow H I O A U L R ε δ henc hε hε1 hδ hδ1
  have hA1 : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  refine ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox, henc', hcounts, hsector, ?_⟩
  intro b hb
  exact clause40_thresholdSolutionBranch A Pw ε δ b hA1 hε.le hδ heval0 happrox hb

/-- The response polynomial of a completed pair has response parity given by its own natural
degree, whose parity agrees with the pair index. -/
theorem clause40_completedPair_ownDegreeParity {n : ℕ} {P Q : Polynomial ℂ}
    (h : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q) :
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity P.natDegree P ∧ P.natDegree % 2 = n % 2 := by
  have hP0 : P ≠ 0 := h.upper_ne_zero
  have hlead : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    intro hc
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp hc)
  have hc := h.parityP.coeff P.natDegree
  have hpow : (-1 : ℂ) ^ P.natDegree = (-1 : ℂ) ^ n := by
    refine mul_right_cancel₀ hlead ?_
    calc (-1 : ℂ) ^ P.natDegree * P.coeff P.natDegree
        = P.coeff P.natDegree * (-1 : ℂ) ^ P.natDegree := mul_comm _ _
      _ = (-1 : ℂ) ^ n * P.coeff P.natDegree := hc
  have hmod : P.natDegree % 2 = n % 2 := by
    have h1 := neg_one_pow_eq_pow_mod_two (R := ℂ) P.natDegree
    have h2 := neg_one_pow_eq_pow_mod_two (R := ℂ) n
    rw [h1, h2] at hpow
    rcases Nat.mod_two_eq_zero_or_one P.natDegree with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · omega
    · norm_num [hm, hn] at hpow
    · norm_num [hm, hn] at hpow
    · omega
  refine ⟨?_, hmod⟩
  change P.comp (-X) = C ((-1 : ℂ) ^ P.natDegree) * P
  calc P.comp (-X) = C ((-1 : ℂ) ^ n) * P := h.parityP
    _ = C ((-1 : ℂ) ^ P.natDegree) * P := by rw [hpow]

/-- The response polynomial of a completed pair satisfies the four conditions in
`QlsCor8Conditions`. -/
theorem clause40_cor8_four_conditions {n : ℕ} {P Q : Polynomial ℂ}
    (h : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q) : QlsCor8Conditions P := by
  obtain ⟨hpar, hmod⟩ := clause40_completedPair_ownDegreeParity h
  refine ⟨hpar, ?_, ?_, ?_⟩
  · intro x hx
    exact h.normSq_eval_le_one hx
  · intro x hx
    exact h.one_le_normSq_eval hx
  · intro heven y
    have hneven : n % 2 = 0 := by omega
    exact h.one_le_normSq_eval_imag hneven y

/-- For the stated error and threshold ranges, a bounded real polynomial has a complex
completion satisfying `QlsCor8Conditions` and a phase realization of length equal to its odd
natural degree. Every realization of that complex response has at least this length and the
same parity. -/
theorem clause40_cor8Bridge (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (P : Polynomial ℂ) (J k : ℕ) (Φ : List ℝ),
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      (∀ x : ℝ, (P.eval (x : ℂ)).re = Pw.eval x) ∧
      QlsCor8Conditions P ∧
      P.natDegree ≤ 2*J+1+2*3^k ∧
      P.natDegree % 2 = 1 ∧
      Φ.length = P.natDegree ∧
      sourcePhaseResponse Φ = P ∧
      (∀ Ψ : List ℝ, sourcePhaseResponse Ψ = P →
        P.natDegree ≤ Ψ.length ∧ Ψ.length % 2 = P.natDegree % 2) := by
  obtain ⟨Pw, J, k, _, _, hdeg, hpar, hbound, _, _⟩ :=
    clause40_relaxedWindowedReciprocal ε δ hε hε1 hδ hδ1
  obtain ⟨P, Q, hpair, _, hre⟩ :=
    Qatlib.Concepts.QsvtCore.LinearSystems.exists_completedPair_of_bounded
      (degree_le_of_natDegree_le hdeg) hpar hbound
  have hfour : QlsCor8Conditions P := clause40_cor8_four_conditions hpair
  have hP0 : P ≠ 0 := hpair.upper_ne_zero
  have hnodd : (2*J+1+2*3^k) % 2 = 1 := by omega
  have hodd : (-1 : ℂ) ^ (2*J+1+2*3^k) = -1 :=
    (Nat.odd_iff.mpr hnodd).neg_one_pow
  have hc0 : P.coeff 0 = 0 := by
    have hc := hpair.parityP.coeff 0
    rw [pow_zero, hodd] at hc
    have h1 : P.coeff 0 = -P.coeff 0 := by
      calc P.coeff 0 = P.coeff 0 * 1 := (mul_one _).symm
        _ = -1 * P.coeff 0 := hc
        _ = -(P.coeff 0) := by ring
    have h2 : P.coeff 0 + P.coeff 0 = 0 := by
      linear_combination h1
    have h3 : (2 : ℂ) * P.coeff 0 = 0 := by
      calc (2 : ℂ) * P.coeff 0 = P.coeff 0 + P.coeff 0 := by ring
        _ = 0 := h2
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (h3.trans (by ring))
  have hPpos : 0 < P.natDegree := by
    by_contra hcon
    have hz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hcon
    obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp hz
    have hxc : x = P.coeff 0 := by
      have hh := congrArg (fun p : Polynomial ℂ => p.coeff 0) hx
      simpa using! hh
    have hx0 : x = 0 := by rw [hxc]; exact hc0
    exact hP0 (by rw [← hx, hx0]; simp)
  have hPdeg : P.natDegree ≤ 2*J+1+2*3^k := by
    have h2 := hpair.degreeP
    rw [Polynomial.degree_eq_natDegree hP0] at h2
    exact WithBot.coe_le_coe.mp h2
  have hmod := (clause40_completedPair_ownDegreeParity hpair).2
  have hPmod : P.natDegree % 2 = 1 := by omega
  obtain ⟨Φ, hΦlen, hΦresp, hΦmin⟩ :=
    corollary8ComplexPhaseExistence P P.natDegree hPpos rfl hfour.parity
      hfour.inner hfour.outer hfour.imaginary
  exact ⟨Pw, P, J, k, Φ, hdeg, hbound, hre, hfour, hPdeg, hPmod, hΦlen, hΦresp, hΦmin⟩

/-- For the stated parameters, a completed complex response has a source word whose length
equals its degree, whose real part is the bounded real polynomial, and whose singular
transform encoding and compilation counts are as specified. -/
theorem clause40_cor8_sourceWord
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (Pw : Polynomial ℝ) (P : Polynomial ℂ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = P.natDegree ∧
      P.natDegree ≤ 2*J+1+2*3^k ∧
      sourcePhaseResponse Φ = P ∧
      (∀ x : ℝ, (P.eval (x : ℂ)).re = Pw.eval x) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (Φ.length, 2*(Φ.length/2), 2*((Φ.length+1)/2), Φ.length) := by
  obtain ⟨Pw, P, J, k, Φ, _, _, hre, _, hPdeg, hPmod, hΦlen, hΦresp, _⟩ :=
    clause40_cor8Bridge ε δ hε hε1 hδ hδ1
  have hre' : ∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = Pw.eval x := by
    intro x
    rw [hΦresp]
    exact hre x
  obtain ⟨hoddbranch, _, hcounts⟩ :=
    source_cpp_real_singular_transform_of_response H I O A U L R Pw Φ henc hre'
  refine ⟨Pw, P, J, k, Φ, hΦlen, hPdeg, hΦresp, hre, ?_, ?_⟩
  · exact hoddbranch (by rw [hΦlen]; exact hPmod)
  · exact hcounts

/-- Compiling a source real phase family from a projected unitary encoding yields a unitary word
with counts determined by the phase list length. -/
theorem clause40_cpp_word_unitary {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (henc : ProjectedUnitaryEncoding A U L R)
    (Φ : List ℝ) :
    cppEvaluate U (rangeProjector R) (rangeProjector L) (cppCompile (sourceRealFamily Φ))
      ∈ Matrix.unitaryGroup (Bool × (Bool × H)) ℂ ∧
    cppCounts (cppCompile (sourceRealFamily Φ)) =
      (Φ.length, 2*(Φ.length/2), 2*((Φ.length+1)/2), Φ.length) := by
  obtain ⟨hU, hL, hR, _⟩ := henc
  obtain ⟨hu, _, hc⟩ :=
    cpp_family_actual_compilation_and_counts Bool H U (rangeProjector R) (rangeProjector L)
      (sourceRealFamily Φ) hU (rangeProjector_isOrthogonalProjector hR)
      (rangeProjector_isOrthogonalProjector hL)
  exact ⟨hu, by simpa [sourceRealFamily] using! hc⟩

/-- The compiled source word acts on the clean family embedding as the selected family of phased
alternating words. -/
theorem clause40_cpp_word_clean_action {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (henc : ProjectedUnitaryEncoding A U L R)
    (Φ : List ℝ) :
    cppEvaluate U (rangeProjector R) (rangeProjector L) (cppCompile (sourceRealFamily Φ))
      * cppFamilyClean (J := Bool) (H := H)
      = cppFamilyClean (J := Bool) (H := H)
        * select (J := Bool) (I := H)
          (fun j => phasedAlternating U (rangeProjector R) (rangeProjector L) 1
            ((sourceRealFamily Φ).map (fun f => anglePhase (f j)))) := by
  obtain ⟨hU, hL, hR, _⟩ := henc
  exact cppCompile_clean U (rangeProjector R) (rangeProjector L)
    (rangeProjector_isOrthogonalProjector hR) (rangeProjector_isOrthogonalProjector hL)
    (sourceRealFamily Φ)

/-- The execution ledger records the phase length as word length, data calls, and phase macros,
the alternating projector access counts, twice the workspace dimension, and the sum of
projector accesses as bit time. -/
theorem clause40_execution_ledger (Φ : List ℝ) (w : ℕ) :
    qlsExecutionLedger Φ w =
      { wordLength := Φ.length
        dataCalls := Φ.length
        pAccesses := 2*(Φ.length/2)
        qAccesses := 2*((Φ.length+1)/2)
        phaseMacros := Φ.length
        peakWorkspace := 2*w
        bitTime := 2*(Φ.length/2) + 2*((Φ.length+1)/2) } := by
  have hc : cppCounts (cppCompile (sourceRealFamily Φ)) =
      (Φ.length, 2*(Φ.length/2), 2*((Φ.length+1)/2), Φ.length) := by
    simpa [sourceRealFamily] using! cppCompile_counts (sourceRealFamily Φ)
  simp [qlsExecutionLedger, hc]

/-- The execution ledger bit time is twice the phase word length. -/
theorem clause40_execution_ledger_bitTime (Φ : List ℝ) (w : ℕ) :
    (qlsExecutionLedger Φ w).bitTime = 2*Φ.length := by
  have h := clause40_execution_ledger Φ w
  have hbit : (qlsExecutionLedger Φ w).bitTime = 2*(Φ.length/2) + 2*((Φ.length+1)/2) := by
    rw [h]
  omega

/-- Under the stated error and threshold bounds, a constructed phase word has length `2 * J + 1
+ 2 * 3 ^ k` and the specified word, data, phase, workspace, bit time, and compilation
counts. -/
theorem clause40_endpoint_execution_ledger
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ (_Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (qlsExecutionLedger Φ (Fintype.card H)).wordLength = 2*J+1+2*3^k ∧
      (qlsExecutionLedger Φ (Fintype.card H)).dataCalls = 2*J+1+2*3^k ∧
      (qlsExecutionLedger Φ (Fintype.card H)).phaseMacros = 2*J+1+2*3^k ∧
      (qlsExecutionLedger Φ (Fintype.card H)).peakWorkspace = 2*Fintype.card H ∧
      (qlsExecutionLedger Φ (Fintype.card H)).bitTime = 2*(2*J+1+2*3^k) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) := by
  obtain ⟨Pw, J, k, Φ, hlen, _, _, _, _, _, _, hcounts, _, _⟩ :=
    clause40_endpoint_noEpsLeDelta H I O A U L R ε δ henc hε hε1 hδ hδ1
  have hled := clause40_execution_ledger Φ (Fintype.card H)
  have hbit := clause40_execution_ledger_bitTime Φ (Fintype.card H)
  refine ⟨Pw, J, k, Φ, hlen, ?_, ?_, ?_, ?_, ?_, hcounts⟩
  · rw [hled]
    exact hlen
  · rw [hled]
    exact hlen
  · rw [hled]
    exact hlen
  · rw [hled]
  · rw [hbit, hlen]

end Sector

end StageBQLSQSVT
end Qatlib.Concepts.QsvtCore.LinearSystems
