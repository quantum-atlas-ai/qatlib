/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41OriginalPseudoinverseStat
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomialGily
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.BlockEncoding.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Polynomial Matrix
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

section Singular
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

private noncomputable def sectorCoefficient (δ x : ℝ) : ℂ :=
  ((1 : ℝ) - thresholdIndicator 0 x + thresholdIndicator δ x : ℂ)

private theorem rightSector_eq (A : Matrix O I ℂ) (δ : ℝ) :
    ((1 : Matrix I I ℂ) - (rightThresholdProjection A 0 - rightThresholdProjection A δ))
      = basisColumns (rightSingularBasis A)
        * diagonal (fun i : Fin (Fintype.card I) => sectorCoefficient δ (matrixSingularValues A i))
        * (basisColumns (rightSingularBasis A))ᴴ := by
  have h1 : (1 : Matrix I I ℂ)
      = spectralDiagonal (rightSingularBasis A) (fun _ => (1 : ℂ)) := by
    simpa using! (spectralDiagonal_const (rightSingularBasis A) 1).symm
  have hr : ∀ τ : ℝ, rightThresholdProjection A τ
      = spectralDiagonal (rightSingularBasis A)
        (fun i : Fin (Fintype.card I) => (thresholdIndicator τ (matrixSingularValues A i) : ℂ)) :=
    fun τ => rfl
  have hf : ∀ i : Fin (Fintype.card I),
      ((1 : ℂ) - ((thresholdIndicator 0 (matrixSingularValues A i) : ℂ)
        - (thresholdIndicator δ (matrixSingularValues A i) : ℂ)))
      = sectorCoefficient δ (matrixSingularValues A i) := by
    intro i
    simp only [sectorCoefficient]
    push_cast
    ring
  rw [h1, hr 0, hr δ, spectralDiagonal_sub, spectralDiagonal_sub]
  refine Eq.trans (congrArg (spectralDiagonal (rightSingularBasis A)) (funext hf)) ?_
  rfl

private theorem leftSector_eq (A : Matrix O I ℂ) (δ : ℝ) :
    ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ))
      = basisColumns (leftSingularBasis A)
        * diagonal (fun j : Fin (Fintype.card O) => sectorCoefficient δ (matrixSingularValues A j))
        * (basisColumns (leftSingularBasis A))ᴴ := by
  have h1 : (1 : Matrix O O ℂ)
      = spectralDiagonal (leftSingularBasis A) (fun _ => (1 : ℂ)) := by
    simpa using! (spectralDiagonal_const (leftSingularBasis A) 1).symm
  have hl : ∀ τ : ℝ, leftThresholdProjection A τ
      = spectralDiagonal (leftSingularBasis A)
        (fun j : Fin (Fintype.card O) => (thresholdIndicator τ (matrixSingularValues A j) : ℂ)) :=
    fun τ => rfl
  have hf : ∀ j : Fin (Fintype.card O),
      ((1 : ℂ) - ((thresholdIndicator 0 (matrixSingularValues A j) : ℂ)
        - (thresholdIndicator δ (matrixSingularValues A j) : ℂ)))
      = sectorCoefficient δ (matrixSingularValues A j) := by
    intro j
    simp only [sectorCoefficient]
    push_cast
    ring
  rw [h1, hl 0, hl δ, spectralDiagonal_sub, spectralDiagonal_sub]
  refine Eq.trans (congrArg (spectralDiagonal (leftSingularBasis A)) (funext hf)) ?_
  rfl

private theorem leftSector_selfAdjoint (A : Matrix O I ℂ) (δ : ℝ) :
    (((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)))ᴴ
      = ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)) := by
  have hl : ∀ τ : ℝ, (leftThresholdProjection A τ)ᴴ = leftThresholdProjection A τ :=
    fun τ => (leftThresholdProjection_isOrthogonalProjector A τ).2
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hl 0, hl δ]

private theorem sectorCoefficient_diagonal_selfAdjoint (A : Matrix O I ℂ) (δ : ℝ) :
    (diagonal (fun i : Fin (Fintype.card I) => sectorCoefficient δ (matrixSingularValues A i)))ᴴ
      = diagonal (fun i : Fin (Fintype.card I) => sectorCoefficient δ (matrixSingularValues A i)) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Matrix.conjTranspose_apply, sectorCoefficient, Complex.conj_ofReal]
  · rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm h),
      Matrix.diagonal_apply_ne _ h, star_zero]

private theorem leftCompanion_gram_entries (A : Matrix O I ℂ) :
    ((basisColumns (leftSingularBasis A))ᴴ * leftSingularColumns A)
      = Matrix.of fun j i => inner ℂ (leftSingularBasis A j) (leftSingularVector A i) := by
  ext j i
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, leftSingularColumns,
    PiLp.inner_apply, mul_comm]

private theorem leftSector_mul_leftSingularColumns (A : Matrix O I ℂ) (δ : ℝ) :
    ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ))
      * leftSingularColumns A
      = leftSingularColumns A
        * diagonal (fun i : Fin (Fintype.card I) => sectorCoefficient δ (matrixSingularValues A i)) := by
  ext o i
  rw [leftSector_eq, Matrix.mul_assoc, Matrix.mul_assoc, leftCompanion_gram_entries]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
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
      rw [if_neg hb]
    · rw [if_pos rfl, hWk]
  · have hσ0 : matrixSingularValues A i = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (by omega)
    have h0 : leftSingularColumns A o i = 0 := by
      simp [leftSingularColumns, leftSingularVector_eq_zero A i hσ0]
    rw [leftSingularVector_eq_zero A i hσ0, h0]
    simp

private theorem sectorCoefficient_entry_bound {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2)
    {Pw : Polynomial ℝ} (heval0 : Pw.eval 0 = 0)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)
    {t : ℝ} (ht0 : 0 ≤ t) (htgap : t = 0 ∨ δ ≤ t) (ht1 : t ≤ 1) :
    ‖sectorCoefficient δ t * ((Pw.eval t : ℝ) : ℂ) * sectorCoefficient δ t
      - (δ/2 : ℂ) * ((t : ℂ)⁻¹) * sectorCoefficient δ t‖ ≤ ε := by
  have hδpos : 0 < δ := by nlinarith
  rcases htgap with rfl | hδt
  · have hind0 : thresholdIndicator 0 0 = 0 := by
      simp only [thresholdIndicator]
      rw [if_neg (show ¬((0 : ℝ)^2 < (0 : ℝ)^2) by norm_num)]
    have hindδ : thresholdIndicator δ 0 = 0 := by
      simp only [thresholdIndicator]
      rw [if_neg (show ¬(δ^2 < (0 : ℝ)^2) by nlinarith [sq_nonneg δ])]
    simp only [sectorCoefficient, hind0, hindδ]
    rw [heval0]
    simpa using! hε.le
  · by_cases hte : t = δ
    · rw [hte]
      have hind0 : thresholdIndicator 0 δ = 1 := by
        simp only [thresholdIndicator]
        rw [if_pos (show (0 : ℝ)^2 < δ^2 by nlinarith)]
      have hindδ : thresholdIndicator δ δ = 0 := by
        simp only [thresholdIndicator]
        rw [if_neg (show ¬(δ^2 < δ^2) by exact lt_irrefl _)]
      simp only [sectorCoefficient, hind0, hindδ]
      simpa using! hε.le
    · have hδlt : δ < t := by
        rcases eq_or_lt_of_le hδt with h | h
        · exact absurd h.symm hte
        · exact h
      have htpos : 0 < t := lt_of_lt_of_le hδpos hδt
      have hind0 : thresholdIndicator 0 t = 1 := by
        simp only [thresholdIndicator]
        rw [if_pos (show (0 : ℝ)^2 < t^2 by nlinarith [htpos])]
      have hindδ : thresholdIndicator δ t = 1 := by
        simp only [thresholdIndicator]
        rw [if_pos (show δ^2 < t^2 by nlinarith [hδlt, hδpos.le, htpos.le])]
      have h1 : ((δ : ℂ) / 2) * ((t : ℂ)⁻¹) = ((δ / 2 / t : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_div]
        field_simp
        norm_num
      simp only [sectorCoefficient, hind0, hindδ]
      norm_num
      rw [h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact happrox t ⟨hδt, ht1⟩

end Singular

theorem theorem41OriginalPseudoinverse : Theorem41OriginalPseudoinverse := by
  intro H I O _ _ _ _ _ _ A U L R ε δ henc hε hεδ hδ hgap
  obtain ⟨Pw, J, k, hbudget, h3k, hdeg, hpar, hbound, heval0, happrox⟩ :=
    theorem41WindowedPolynomial ε δ hε hεδ hδ
  have hdE : 2*J+1+2*3^k = 2*(J+3^k)+1 := by ring
  have hdiv : ∀ n : ℕ, (2*n+1)/2 = n := fun n => by omega
  have hdiv2 : ∀ n : ℕ, (2*n+1+1)/2 = n+1 := fun n => by omega
  have hmod : ∀ n : ℕ, (2*n+1)%2 = 1 := fun n => by omega
  obtain ⟨Φ, hlen, hodd, _, hcounts⟩ :=
    source_length_cpp_real_singular_transform H I O A U L R Pw (2*J+1+2*3^k) henc
      (by rw [hdE]; omega) (degree_le_of_natDegree_le hdeg) hpar hbound
  refine ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox,
    hodd (by rw [hdE]; exact hmod (J+3^k)), ?_, ?_⟩
  · rw [hcounts, show (2*J+1+2*3^k)/2 = J+3^k from by rw [hdE]; exact hdiv (J+3^k),
      show (2*J+1+2*3^k+1)/2 = J+3^k+1 from by rw [hdE]; exact hdiv2 (J+3^k),
      show (2*(J+3^k) : ℕ) = 2*J+2*3^k from by ring,
      show (2*(J+3^k+1) : ℕ) = 2*J+2+2*3^k from by ring]
  · show ‖((1 : Matrix I I ℂ) - (rightThresholdProjection A 0 - rightThresholdProjection A δ))
        * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
        * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ))
        - (δ/2 : ℂ) • (matrixPseudoinverse A
          * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)))‖
      ≤ ε
    have hA1 : ‖A‖ ≤ 1 := by
      rw [← henc.encoded]
      exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
        (unitary_norm_le_one henc.unitary)
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
    have hUL := congrArg Matrix.conjTranspose (leftSector_mul_leftSingularColumns A δ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, leftSector_selfAdjoint,
      sectorCoefficient_diagonal_selfAdjoint] at hUL
    have hRV : ∀ X : Matrix (Fin (Fintype.card I)) O ℂ,
        ((1 : Matrix I I ℂ) - (rightThresholdProjection A 0 - rightThresholdProjection A δ))
          * (basisColumns (rightSingularBasis A) * X)
        = basisColumns (rightSingularBasis A)
          * (diagonal (fun i : Fin (Fintype.card I) => sectorCoefficient δ (matrixSingularValues A i))
            * X) := by
      intro X
      rw [rightSector_eq, Matrix.mul_assoc,
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
    have hE : ((1 : Matrix I I ℂ) - (rightThresholdProjection A 0 - rightThresholdProjection A δ))
        * (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
        * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ))
        - (δ/2 : ℂ) • (matrixPseudoinverse A
          * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)))
        = basisColumns (rightSingularBasis A)
          * diagonal (fun i : Fin (Fintype.card I) =>
              sectorCoefficient δ (matrixSingularValues A i)
                * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
                * sectorCoefficient δ (matrixSingularValues A i)
              - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
                * sectorCoefficient δ (matrixSingularValues A i))
          * (leftSingularColumns A)ᴴ := by
      have hstep1 : ((1 : Matrix I I ℂ) - (rightThresholdProjection A 0 - rightThresholdProjection A δ))
          * ((oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
            * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)))
          - (δ/2 : ℂ) • (matrixPseudoinverse A
            * ((1 : Matrix O O ℂ) - (leftThresholdProjection A 0 - leftThresholdProjection A δ)))
          = basisColumns (rightSingularBasis A)
            * ((diagonal (fun i : Fin (Fintype.card I) =>
                  sectorCoefficient δ (matrixSingularValues A i))
                * (diagonal (fun i : Fin (Fintype.card I) =>
                  ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ))
                  * (diagonal (fun i : Fin (Fintype.card I) =>
                    sectorCoefficient δ (matrixSingularValues A i)) * (leftSingularColumns A)ᴴ)))
              - (δ/2 : ℂ) • (diagonal (fun i : Fin (Fintype.card I) =>
                  ((matrixSingularValues A i : ℂ)⁻¹))
                * (diagonal (fun i : Fin (Fintype.card I) =>
                  sectorCoefficient δ (matrixSingularValues A i)) * (leftSingularColumns A)ᴴ))) := by
        rw [hC, matrixPseudoinverse_eq]
        simp only [Matrix.mul_assoc]
        rw [hUL, ← Matrix.mul_smul, hRV, ← Matrix.mul_sub]
      rw [Matrix.mul_assoc, hstep1, ← Matrix.smul_mul, hsd, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.sub_mul,
        Matrix.diagonal_sub, ← Matrix.mul_assoc]
    have hentry : ∀ i : Fin (Fintype.card I),
        ‖sectorCoefficient δ (matrixSingularValues A i)
          * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
          * sectorCoefficient δ (matrixSingularValues A i)
          - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
            * sectorCoefficient δ (matrixSingularValues A i)‖ ≤ ε := by
      intro i
      have hgap' : matrixSingularValues A i = 0 ∨ δ ≤ matrixSingularValues A i := by
        by_cases h : matrixSingularValues A i = 0
        · exact Or.inl h
        · exact Or.inr (hgap i h)
      exact sectorCoefficient_entry_bound hε hεδ hδ heval0 happrox
        (matrixSingularValues_nonneg A i) hgap'
        ((matrixSingularValues_le_spectralNorm A i).trans hA1)
    have hdiag : ‖diagonal (fun i : Fin (Fintype.card I) =>
        sectorCoefficient δ (matrixSingularValues A i)
          * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
          * sectorCoefficient δ (matrixSingularValues A i)
        - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
          * sectorCoefficient δ (matrixSingularValues A i))‖ ≤ ε := by
      rw [Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg hε.le).2 hentry
    have hVn : ‖basisColumns (rightSingularBasis A)‖ ≤ 1 := basisColumns_norm_le _
    have hUn : ‖(leftSingularColumns A)ᴴ‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact leftSingularColumns_norm_le A
    rw [hE]
    have h1 : ‖basisColumns (rightSingularBasis A)
        * diagonal (fun i : Fin (Fintype.card I) =>
            sectorCoefficient δ (matrixSingularValues A i)
              * ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ)
              * sectorCoefficient δ (matrixSingularValues A i)
            - (δ/2 : ℂ) * ((matrixSingularValues A i : ℂ)⁻¹)
              * sectorCoefficient δ (matrixSingularValues A i))‖ ≤ ε := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      exact (mul_le_mul hVn hdiag (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)
    exact (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul h1 hUn (norm_nonneg _) hε.le).trans_eq (mul_one ε))

end Qatlib.Concepts.QsvtCore.LinearSystems
