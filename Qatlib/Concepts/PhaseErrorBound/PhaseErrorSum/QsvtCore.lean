/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCoreDefs
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.SchattenDiamondDefs
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ScopedOracleWorkspace
import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCoreNativePhasePort
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexInnerProductSpace

private def IsSignalSectorPair {H : Type} [Fintype H] [DecidableEq H]
    (Pblk Qblk : Matrix H H ℂ) : Prop :=
  Pblk + Qblk = 1 ∧ Pblk * Qblk = 0 ∧ Qblk * Pblk = 0 ∧
    IsOrthogonalProjector Pblk ∧ IsOrthogonalProjector Qblk

private def IsBase1ConstantTriple {H : Type} [Fintype H] [DecidableEq H]
    (U Q : Matrix H H ℂ) : Prop :=
  (Q = 1 ∨ Q = 0) ∧ ∃ γ : ℂ, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase γ ∧ U = γ • 1

private noncomputable def InitActDiscardForm {D Ds Da : ℕ}
    (channel : QuantumChannel D D) (e : Fin D ≃ (Fin Ds × Fin Da))
    (U : Matrix (Fin Ds × Fin Da) (Fin Ds × Fin Da) ℂ)
    (seed : QState (Fin Da)) : Prop :=
  ∀ σ : Operator Ds,
    PartialTrace (Matrix.reindex e e (channel.map
        (Matrix.reindex e.symm e.symm (Matrix.kronecker σ (outerProduct seed)))))
      = PartialTrace (U * Matrix.kronecker σ (outerProduct seed) * Uᴴ)

section ThresholdMaterials

open Polynomial

private theorem idealPoly_coeff (coeffs : List ℂ) (i : ℕ) :
    (phaseInversionIdealPoly coeffs).coeff i = coeffs.getD i 0 := by
  simp only [phaseInversionIdealPoly]
  by_cases hi : i < coeffs.length
  · simp [hi]
  · simp [hi]

private theorem idealPoly_natDegree_le {coeffs : List ℂ} {d : ℕ}
    (hdeg : (phaseInversionIdealPoly coeffs).degree ≤ (d : WithBot ℕ)) :
    (phaseInversionIdealPoly coeffs).natDegree ≤ d := by
  by_cases hz : phaseInversionIdealPoly coeffs = 0
  · simp [hz]
  · rw [Polynomial.degree_eq_natDegree hz] at hdeg
    exact_mod_cast hdeg

private theorem star_mul_normSq (z : ℂ) : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
  show z * starRingEnd ℂ z = _
  rw [Complex.mul_conj]

private theorem completedPair_norm_le_one {d : ℕ} {P Q : Polynomial ℂ}
    (h : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair d P Q) {x : ℝ}
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) : ‖P.eval (x : ℂ)‖ ≤ 1 := by
  have he := congrArg (Polynomial.eval (x : ℂ)) h.normalization
  simp only [Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.responsePairNorm, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X,
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial_eval_real] at he
  have key : Complex.normSq (P.eval (x : ℂ)) + (1 - x * x) * Complex.normSq (Q.eval (x : ℂ))
      = 1 := by
    have h2 : (x : ℂ) ^ 2 = ((x * x : ℝ) : ℂ) := by push_cast; ring
    have h3 : (1 : ℂ) - ((x * x : ℝ) : ℂ) = ((1 - x * x : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one]
    rw [h2, h3, mul_assoc, star_mul_normSq (Q.eval (x : ℂ)), ← Complex.ofReal_mul,
      star_mul_normSq (P.eval (x : ℂ)), ← Complex.ofReal_add, ← Complex.ofReal_one] at he
    exact Complex.ofReal_injective he
  have hnn : (0 : ℝ) ≤ (1 - x * x) * Complex.normSq (Q.eval (x : ℂ)) :=
    mul_nonneg (by nlinarith) (Complex.normSq_nonneg _)
  have hle : Complex.normSq (P.eval (x : ℂ)) ≤ 1 := by linarith
  rw [Complex.normSq_eq_norm_sq] at hle
  by_contra hgt
  have hgt1 : 1 < ‖P.eval (x : ℂ)‖ := not_le.mp hgt
  have h1 : (1 : ℝ) < ‖P.eval (x : ℂ)‖ ^ 2 := by nlinarith [hgt1, sq (‖P.eval (x : ℂ)‖)]
  linarith

private theorem polyRealPart_coeff (P : Polynomial ℂ) (i : ℕ) :
    (polyRealPart P).coeff i = (P.coeff i).re := by
  simp only [polyRealPart]
  by_cases hi : i < P.natDegree + 1
  · simp [hi]
  · have hc : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hi, hc]

private theorem polyImagPart_coeff (P : Polynomial ℂ) (i : ℕ) :
    (polyImagPart P).coeff i = (P.coeff i).im := by
  simp only [polyImagPart]
  by_cases hi : i < P.natDegree + 1
  · simp [hi]
  · have hc : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hi, hc]

private theorem polyRealPart_eval (P : Polynomial ℂ) (x : ℝ) :
    (polyRealPart P).eval x = (P.eval (x : ℂ)).re := by
  have hsum : P.eval (x : ℂ) = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (x : ℂ) ^ i :=
    Polynomial.eval_eq_sum_range' (by omega) (x : ℂ)
  simp only [polyRealPart, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, hsum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring

private theorem polyImagPart_eval (P : Polynomial ℂ) (x : ℝ) :
    (polyImagPart P).eval x = (P.eval (x : ℂ)).im := by
  have hsum : P.eval (x : ℂ) = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (x : ℂ) ^ i :=
    Polynomial.eval_eq_sum_range' (by omega) (x : ℂ)
  simp only [polyImagPart, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, hsum, Complex.im_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

private theorem polyRealPart_derivative (P : Polynomial ℂ) :
    (polyRealPart P).derivative = polyRealPart P.derivative := by
  ext n
  rw [Polynomial.coeff_derivative, polyRealPart_coeff, polyRealPart_coeff (derivative P),
    Polynomial.coeff_derivative, Complex.mul_re]
  simp

private theorem polyImagPart_derivative (P : Polynomial ℂ) :
    (polyImagPart P).derivative = polyImagPart P.derivative := by
  ext n
  rw [Polynomial.coeff_derivative, polyImagPart_coeff, polyImagPart_coeff (derivative P),
    Polynomial.coeff_derivative, Complex.mul_im]
  simp

private theorem polyRealPart_natDegree_le (P : Polynomial ℂ) :
    (polyRealPart P).natDegree ≤ P.natDegree := by
  refine Polynomial.natDegree_le_of_degree_le
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr ?_)
  intro m hm
  rw [polyRealPart_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by
    exact_mod_cast hm)]
  simp

private theorem polyImagPart_natDegree_le (P : Polynomial ℂ) :
    (polyImagPart P).natDegree ≤ P.natDegree := by
  refine Polynomial.natDegree_le_of_degree_le
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr ?_)
  intro m hm
  rw [polyImagPart_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by
    exact_mod_cast hm)]
  simp

private theorem dataPolynomial_natDegree_le {γ : List GaussianRat} {d : ℕ}
    (hlen : γ.length ≤ d + 1) : (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ).natDegree ≤ d := by
  refine Polynomial.natDegree_le_of_degree_le
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr ?_)
  intro m hm
  rw [Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial_coeff]
  by_cases hml : m < γ.length
  · exact absurd (show d < m from by exact_mod_cast hm) (by omega)
  · rw [List.getD_eq_default γ Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero (by omega),
    Qatlib.Concepts.NativeNumerics.PhaseSynthesis.complex_gzero]

end ThresholdMaterials

theorem clause44 : ∀ (d : ℕ) (coeffs : List ℂ) (ε : ℝ),
    (phaseInversionIdealPoly coeffs).degree ≤ (d : WithBot ℕ) →
    (∃ Qc : Polynomial ℂ,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair d (phaseInversionIdealPoly coeffs) Qc) →
    0 < ε → ε ≤ 1 / 2 →
    ∃ res : PhaseInversionResult,
      PhaseInversionSuccess d coeffs ε res ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖(Polynomial.derivative
            (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial res.phases)).eval (x : ℂ)‖
          ≤ 2 * ((res.phases.length + d + 1 : ℕ) : ℝ) ^ 2 * (1 + ε)) := by
  intro d coeffs ε hdeg hex hε hεhalf
  obtain ⟨Qc, hQ⟩ := hex
  have hpnd := idealPoly_natDegree_le hdeg

  have hr : ∀ i : ℕ, ∃ z : GaussianRat,
      ‖gaussianRatComplex z - coeffs.getD i 0‖ ≤ ε / (2 * (d + 1)) := by
    intro i
    have hpos : (0 : ℝ) < ε / (4 * (d + 1)) :=
      div_pos hε (by positivity)
    obtain ⟨q1, hq1⟩ := exists_rat_near (coeffs.getD i 0).re hpos
    obtain ⟨q2, hq2⟩ := exists_rat_near (coeffs.getD i 0).im hpos
    refine ⟨(q1, q2), ?_⟩
    have hre : (gaussianRatComplex (q1, q2) - coeffs.getD i 0).re
        = (q1 : ℝ) - (coeffs.getD i 0).re := by
      simp only [gaussianRatComplex, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_zero]
      norm_cast
      push_cast
      ring
    have him : (gaussianRatComplex (q1, q2) - coeffs.getD i 0).im
        = (q2 : ℝ) - (coeffs.getD i 0).im := by
      simp only [gaussianRatComplex, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
      norm_cast
      push_cast
      ring
    have h3 : |(q1 : ℝ) - (coeffs.getD i 0).re| + |(q2 : ℝ) - (coeffs.getD i 0).im|
        ≤ 2 * (ε / (4 * (d + 1))) := by
      rw [abs_sub_comm (↑q1 : ℝ) (coeffs.getD i 0).re,
        abs_sub_comm (↑q2 : ℝ) (coeffs.getD i 0).im,
        show 2 * (ε / (4 * ((d : ℝ) + 1))) = ε / (4 * ((d : ℝ) + 1)) + ε /
            (4 * ((d : ℝ) + 1)) by ring]
      exact add_le_add hq1.le hq2.le
    have h4 : 2 * (ε / (4 * (d + 1))) = ε / (2 * (d + 1)) := by
      field_simp
      ring
    rw [h4] at h3
    calc ‖gaussianRatComplex (q1, q2) - coeffs.getD i 0‖
        ≤ |(gaussianRatComplex (q1, q2) - coeffs.getD i 0).re|
            + |(gaussianRatComplex (q1, q2) - coeffs.getD i 0).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(q1 : ℝ) - (coeffs.getD i 0).re| + |(q2 : ℝ) - (coeffs.getD i 0).im| := by
            rw [hre, him]
      _ ≤ ε / (2 * (d + 1)) := h3
  choose fz hfz using hr
  set γ : List GaussianRat := (List.range (d + 1)).map fz with hγ
  have hγlen : γ.length = d + 1 := by simp [hγ]
  have hγget : ∀ i : ℕ, i < d + 1 → γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero = fz i := by
    intro i hi
    have h1 : γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero = fz ((List.range (d + 1)).getD i 0) :=
      Qatlib.Concepts.NativeNumerics.PhaseSynthesis.mapped_getD_valid fz (List.range (d + 1)) 0
        Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero i (by simp; omega)
    have h2 : (List.range (d + 1)).getD i 0 = i := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range]
    rw [h1, h2]

  have hptw : ∀ x : ℝ, |x| ≤ 1 →
      ‖(phaseInversionIdealPoly coeffs).eval (x : ℂ)
          - (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ).eval (x : ℂ)‖ ≤ ε := by
    intro x hx
    have hP : (phaseInversionIdealPoly coeffs).eval (x : ℂ)
        = ∑ i ∈ Finset.range (d + 1), (phaseInversionIdealPoly coeffs).coeff i * (x : ℂ) ^ i :=
      Polynomial.eval_eq_sum_range' (by omega) (x : ℂ)
    have hD : (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ).eval (x : ℂ)
        = ∑ i ∈ Finset.range (d + 1),
            (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ).coeff i * (x : ℂ) ^ i :=
      Polynomial.eval_eq_sum_range'
        (by have := dataPolynomial_natDegree_le (γ := γ) (d := d) (by simp [hγlen]); omega) (x : ℂ)
    rw [hP, hD, ← Finset.sum_sub_distrib]
    have hsplit : ∀ i ∈ Finset.range (d + 1),
        ((phaseInversionIdealPoly coeffs).coeff i * (x : ℂ) ^ i
            - (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ).coeff i * (x : ℂ) ^ i)
        = (coeffs.getD i 0 - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero))
            * (x : ℂ) ^ i := by
      intro i hi
      rw [idealPoly_coeff, Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial_coeff,
          ← sub_mul]
    have hbound : ∀ i ∈ Finset.range (d + 1),
        ‖coeffs.getD i 0
            - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖
          * ‖(x : ℂ) ^ i‖ ≤ ε / (2 * (d + 1)) := by
      intro i hi
      have hx1 : ‖(x : ℂ)‖ ≤ 1 := by rw [Complex.norm_real]; exact hx
      have hpow : ‖(x : ℂ) ^ i‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hx1
      have hdiff : ‖coeffs.getD i 0
          - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖
          ≤ ε / (2 * (d + 1)) := by
        rw [hγget i (Finset.mem_range.mp hi), norm_sub_rev]
        exact hfz i
      calc ‖coeffs.getD i 0
            - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖ * ‖(x : ℂ) ^ i‖
          ≤ ‖coeffs.getD i 0
            - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖ * 1 :=
              mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = ‖coeffs.getD i 0
            - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖ := mul_one _
        _ ≤ ε / (2 * (d + 1)) := hdiff
    rw [Finset.sum_congr rfl hsplit]
    calc ‖∑ i ∈ Finset.range (d + 1),
            (coeffs.getD i 0
              - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)) * (x : ℂ) ^ i‖
        ≤ ∑ i ∈ Finset.range (d + 1),
            ‖(coeffs.getD i 0
              - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)) * (x : ℂ) ^ i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (d + 1),
            ‖coeffs.getD i 0
              - gaussianRatComplex (γ.getD i Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gzero)‖
              * ‖(x : ℂ) ^ i‖ :=
            Finset.sum_le_sum fun i _ => norm_mul_le _ _
      _ ≤ ∑ i ∈ Finset.range (d + 1), ε / (2 * (d + 1)) :=
            Finset.sum_le_sum fun i hi => hbound i hi
      _ = ε / 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            field_simp
      _ ≤ ε := by linarith
  refine ⟨⟨γ, 0, 0⟩, ⟨hε, hεhalf, le_refl 0, hε.le, Nat.zero_le _, fun x hx => hptw x hx⟩,
    ?_⟩
  intro x hx
  set D := Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial γ with hDdef
  have hDnd : D.natDegree ≤ d := dataPolynomial_natDegree_le (γ := γ) (d := d) (by simp [hγlen])

  have habsD : ∀ y ∈ Set.Icc (-1 : ℝ) 1, ‖D.eval (y : ℂ)‖ ≤ 1 + ε := by
    intro y hy
    have hp := hptw y (abs_le.mpr ⟨hy.1, hy.2⟩)
    rw [← norm_sub_rev] at hp
    have h2 : ‖(phaseInversionIdealPoly coeffs).eval (y : ℂ)‖ ≤ 1 :=
      completedPair_norm_le_one hQ hy.1 hy.2
    calc ‖D.eval (y : ℂ)‖ = ‖D.eval (y : ℂ)
          - (phaseInversionIdealPoly coeffs).eval (y : ℂ)
          + (phaseInversionIdealPoly coeffs).eval (y : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖D.eval (y : ℂ) - (phaseInversionIdealPoly coeffs).eval (y : ℂ)‖
            + ‖(phaseInversionIdealPoly coeffs).eval (y : ℂ)‖ := norm_add_le _ _
      _ ≤ ε + ‖(phaseInversionIdealPoly coeffs).eval (y : ℂ)‖ := add_le_add_left hp _
      _ ≤ 1 + ε := by linarith

  have hre := markov_brothers_deriv_le (C := 1 + ε) ((polyRealPart_natDegree_le D).trans hDnd)
    (by linarith) (fun y hy => by
      rw [polyRealPart_eval]
      exact (Complex.abs_re_le_norm (D.eval (y : ℂ))).trans (habsD y hy))
  have him := markov_brothers_deriv_le (C := 1 + ε) ((polyImagPart_natDegree_le D).trans hDnd)
    (by linarith) (fun y hy => by
      rw [polyImagPart_eval]
      exact (Complex.abs_im_le_norm (D.eval (y : ℂ))).trans (habsD y hy))
  have hrev : (polyRealPart D).derivative.eval x = ((D.derivative.eval (x : ℂ))).re := by
    rw [polyRealPart_derivative, polyRealPart_eval]
  have himv : (polyImagPart D).derivative.eval x = ((D.derivative.eval (x : ℂ))).im := by
    rw [polyImagPart_derivative, polyImagPart_eval]
  have hsplitv : (D.derivative.eval (x : ℂ))
      = (((polyRealPart D).derivative.eval x : ℝ) : ℂ)
        + (((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I := by
    have h1 := Complex.re_add_im (D.derivative.eval (x : ℂ))
    rw [← hrev, ← himv] at h1
    exact h1.symm
  rw [hsplitv]
  have h1 : ‖(((polyRealPart D).derivative.eval x : ℝ) : ℂ)
      + (((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I‖
      ≤ |(polyRealPart D).derivative.eval x| + |(polyImagPart D).derivative.eval x| := by
    have ha : ‖(((polyRealPart D).derivative.eval x : ℝ) : ℂ)‖
        = |(polyRealPart D).derivative.eval x| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hb : ‖((((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I)‖
        = |(polyImagPart D).derivative.eval x| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(((polyRealPart D).derivative.eval x : ℝ) : ℂ)
          + (((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(((polyRealPart D).derivative.eval x : ℝ) : ℂ)‖
            + ‖((((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I)‖ :=
              norm_add_le _ _
      _ = |(polyRealPart D).derivative.eval x|
            + |(polyImagPart D).derivative.eval x| := by rw [ha, hb]
  have h2 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hkey : ((d : ℝ) ^ 2) ≤ 2 * ((d : ℝ) + 1) ^ 2 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hs : (0 : ℝ) ≤ ((d : ℝ) ^ 2) := sq_nonneg _
    have he : 2 * (((d : ℝ) + 1) ^ 2) = 2 * ((d : ℝ) ^ 2) + 4 * (d : ℝ) + 2 := by ring
    linarith
  have h4 : (4 * ((d : ℝ) ^ 2)) * (1 + ε) ≤ (2 * (2 * ((d : ℝ) + 1)) ^ 2) * (1 + ε) := by
    have hr : 2 * (2 * ((d : ℝ) + 1)) ^ 2 = 8 * (((d : ℝ) + 1)) ^ 2 := by ring
    rw [hr]
    exact mul_le_mul_of_nonneg_right (by linarith) h2
  have hlen : ((γ.length + d + 1 : ℕ) : ℝ) = 2 * ((d : ℝ) + 1) := by
    rw [hγlen]; push_cast; ring
  rw [hlen]
  calc ‖(((polyRealPart D).derivative.eval x : ℝ) : ℂ)
        + (((polyImagPart D).derivative.eval x : ℝ) : ℂ) * Complex.I‖
      ≤ |(polyRealPart D).derivative.eval x| + |(polyImagPart D).derivative.eval x| := h1
    _ ≤ 2 * (d : ℝ) ^ 2 * (1 + ε) + 2 * (d : ℝ) ^ 2 * (1 + ε) :=
          add_le_add (hre x hx) (him x hx)
    _ = (4 * ((d : ℝ) ^ 2)) * (1 + ε) := by ring
    _ ≤ (2 * (2 * ((d : ℝ) + 1)) ^ 2) * (1 + ε) := h4
    _ = 2 * (2 * ((d : ℝ) + 1)) ^ 2 * (1 + ε) := by ring

section PaidWalkMaterials

private theorem reindex_mul_eq {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (E : m ≃ n) (A B : Matrix m m ℂ) :
    Matrix.reindex E E (A * B) = Matrix.reindex E E A * Matrix.reindex E E B := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Equiv.sum_comp E.symm (fun p => A (E.symm i) p * B p (E.symm j))]

private theorem reindex_one_eq {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (E : m ≃ n) :
    Matrix.reindex E E (1 : Matrix m m ℂ) = 1 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
    E.symm.injective.eq_iff]

private theorem reindex_reindex_symm_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (E : m ≃ n) (M : Matrix n n ℂ) :
    Matrix.reindex E E (Matrix.reindex E.symm E.symm M) = M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

end PaidWalkMaterials

theorem clause49 : ∀ (D : ℕ) (ideal : Operator D), ideal ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ (channel : QuantumChannel D D) (peakSpace ancilla retryBudget : ℕ)
        (Ds Da : ℕ) (e : Fin D ≃ (Fin Ds × Fin Da))
        (U : Matrix (Fin Ds × Fin Da) (Fin Ds × Fin Da) ℂ)
        (seed : QState (Fin Da)),
        PhysicalWorkspaceSpec ε ideal channel peakSpace ancilla retryBudget ∧
        D ≤ peakSpace ∧
        Normalized seed ∧ U ∈ Matrix.unitaryGroup (Fin Ds × Fin Da) ℂ ∧
        InitActDiscardForm channel e U seed := by
  intro D ideal hU ε hε
  have hstar : idealᴴ * ideal = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.mp hU)
    rwa [Matrix.star_eq_conjTranspose] at h
  set e : Fin D ≃ (Fin D × Fin 1) :=
    (finCongr (Nat.mul_one D).symm).trans (@finProdFinEquiv D 1).symm with he
  set U : Matrix (Fin D × Fin 1) (Fin D × Fin 1) ℂ := Matrix.reindex e e ideal with hUd
  set seed : QState (Fin 1) := fun _ => 1 with hseed
  have htp : TracePreserving (conjBranch ideal) := by
    intro A
    rw [conjBranch_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      hstar, Matrix.mul_one]
  refine ⟨⟨conjBranch ideal, completelyPositive_conjBranch ideal, htp⟩,
    D, 0, 0, D, 1, e, U, seed, ?_, le_refl D, ?_, ?_, ?_⟩
  · simp only [PhysicalWorkspaceSpec]
    refine ⟨hε, hU, ?_, Nat.zero_le D, Nat.le_add_right D 0, Nat.zero_le D⟩
    intro ρ _hρ
    have hz : (⟨conjBranch ideal, completelyPositive_conjBranch ideal, htp⟩ :
        QuantumChannel D D).map ρ = ideal * ρ * idealᴴ := rfl
    rw [hz, sub_self, Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm,
      Matrix.traceNorm_zero]
    exact hε.le
  · simp [hseed, Normalized]
  · rw [hUd, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex, ← reindex_mul_eq, hstar, reindex_one_eq]
  · unfold InitActDiscardForm
    intro σ
    have hz : (⟨conjBranch ideal, completelyPositive_conjBranch ideal, htp⟩ :
        QuantumChannel D D).map (Matrix.reindex e.symm e.symm
          (Matrix.kronecker σ (outerProduct seed)))
        = conjBranch ideal (Matrix.reindex e.symm e.symm
          (Matrix.kronecker σ (outerProduct seed))) := rfl
    rw [hz]
    have hkey : Matrix.reindex e e (conjBranch ideal
        (Matrix.reindex e.symm e.symm (Matrix.kronecker σ (outerProduct seed))))
        = U * Matrix.kronecker σ (outerProduct seed) * Uᴴ := by
      rw [conjBranch_apply, reindex_mul_eq, reindex_mul_eq,
        reindex_reindex_symm_eq, hUd, Matrix.conjTranspose_reindex]
    rw [hkey]

theorem clause45 : ∀ (H I : Type) [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]
    (F : Matrix H I ℂ), Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F →
    ∀ (δ κ : ℝ), 0 ≤ δ → 1 ≤ κ →
      ∀ ε : ℝ, 0 < ε →
        ∃ impl : FrameImplementation F,
          FrameTransportSuccess F impl ε ∧ impl.error ≤ δ + ε := by
  intro H I _ _ _ _ F hF δ _κ hδ _hκ ε hε
  have hFF : Fᴴ * F = 1 := hF
  set c : I → EuclideanSpace ℂ H := fun i => WithLp.toLp 2 (fun j => F j i) with hc
  have hcj : ∀ (i : I) (j : H), (c i) j = F j i := fun _ _ => rfl
  have hcorth : Orthonormal ℂ c := by
    rw [orthonormal_iff_ite]
    intro i i'
    have h1 : ⟪c i, c i'⟫ = ∑ j : H, ⟪(c i) j, (c i') j⟫ := PiLp.inner_apply _ _
    have h2 : ∀ j : H, ⟪(c i) j, (c i') j⟫ = star (F j i) * F j i' := by
      intro j
      rw [hcj, hcj, RCLike.inner_apply', starRingEnd_apply]
    have h3 : (Fᴴ * F) i i' = ∑ j : H, star (F j i) * F j i' := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply]
    rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), ← h3, hFF, Matrix.one_apply]
  have hc_inj : Function.Injective c := by
    intro i i' h
    by_contra hne
    have h1 : ⟪c i, c i'⟫ = ⟪c i, c i⟫ := by rw [h]
    rw [orthonormal_iff_ite.mp hcorth i i', orthonormal_iff_ite.mp hcorth i i] at h1
    simp [hne] at h1
  have hcsub : Orthonormal ℂ ((↑) : (Set.range c) → EuclideanSpace ℂ H) := by
    rw [orthonormal_iff_ite]
    intro x y
    obtain ⟨i, hi⟩ := Set.mem_range.mp x.2
    obtain ⟨i', hi'⟩ := Set.mem_range.mp y.2
    have hxy : x = y ↔ i = i' := by
      rw [Subtype.ext_iff, ← hi, ← hi', hc_inj.eq_iff]
    rw [← hi, ← hi']
    by_cases h : i = i'
    · rw [if_pos (hxy.mpr h)]
      have horth' := orthonormal_iff_ite.mp hcorth i i'
      rw [if_pos h] at horth'
      exact horth'
    · rw [if_neg (fun hx => h (hxy.mp hx))]
      have horth' := orthonormal_iff_ite.mp hcorth i i'
      rw [if_neg h] at horth'
      exact horth'
  obtain ⟨u, b, hsub, hcoe⟩ := Orthonormal.exists_orthonormalBasis_extension hcsub
  have huorth : Orthonormal ℂ ((↑) : ↥u → EuclideanSpace ℂ H) := by
    rw [← hcoe]
    exact b.orthonormal
  have hcard : Fintype.card ↥u = Fintype.card H := by
    have h1 : Module.finrank ℂ (EuclideanSpace ℂ H) = Fintype.card ↥u :=
      Module.finrank_eq_card_basis b.toBasis
    rw [finrank_euclideanSpace] at h1
    exact h1.symm
  set toE : ↥u ≃ H := Fintype.equivOfCardEq hcard with htoE
  have hmem : ∀ i : I, c i ∈ ↑u := fun i => hsub (Set.mem_range_self i)
  set seed : I → H := fun i => toE ⟨c i, Finset.mem_coe.mp (hmem i)⟩ with hseed
  set W : Matrix H H ℂ := Matrix.of fun j k => (toE.symm k : EuclideanSpace ℂ H) j with hW
  have hWseed : ∀ (i : I) (j : H), W j (seed i) = F j i := by
    intro i j
    have h1 : toE.symm (seed i) = ⟨c i, Finset.mem_coe.mp (hmem i)⟩ :=
      toE.symm_apply_apply _
    rw [hW, Matrix.of_apply, h1]
  have hWHW : Wᴴ * W = 1 := by
    ext k k'
    have h1 : ⟪(toE.symm k : EuclideanSpace ℂ H), (toE.symm k' : EuclideanSpace ℂ H)⟫
        = if k = k' then 1 else 0 := by
      have h2 := orthonormal_iff_ite.mp huorth (toE.symm k) (toE.symm k')
      by_cases hkk' : k = k'
      · rw [if_pos (congrArg toE.symm hkk')] at h2
        rw [if_pos hkk']
        exact h2
      · rw [if_neg (fun hcon => hkk' (toE.symm.injective hcon))] at h2
        rw [if_neg hkk']
        exact h2
    rw [PiLp.inner_apply] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hW, Matrix.of_apply, RCLike.inner_apply', starRingEnd_apply]
  set CW : Matrix (Bool × H) (Bool × H) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then (if p.1 then W else 1) p.2 q.2 else 0 with hCW
  have hRunPrep : ∀ (i : I),
      Run (1 : Matrix H H ℂ) (Step.gate W :: ([] : Circuit H)) (Qatlib.Foundations.PureStateMath.Ket (seed i))
        = fun j => F j i := by
    intro i
    show W *ᵥ Qatlib.Foundations.PureStateMath.Ket (seed i) = fun j => F j i
    funext j
    simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single (seed i)]
    · rw [if_pos rfl, mul_one]
      exact hWseed i j
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro hni
      exact absurd (Finset.mem_univ _) hni
  have hRunInv : ∀ ψ : QState H,
      Run (1 : Matrix H H ℂ) (Step.gate Wᴴ :: ([] : Circuit H))
        (Run (1 : Matrix H H ℂ) (Step.gate W :: ([] : Circuit H)) ψ) = ψ := by
    intro ψ
    show Wᴴ *ᵥ (W *ᵥ ψ) = ψ
    rw [Matrix.mulVec_mulVec, hWHW, Matrix.one_mulVec]
  have hRunCtl : ∀ (b : Bool) (ψ : QState H),
      Run (1 : Matrix (Bool × H) (Bool × H) ℂ) (Step.gate CW :: ([] : Circuit (Bool × H)))
        (controlledSector b ψ)
        = controlledSector b (if b then
            Run (1 : Matrix H H ℂ) (Step.gate W :: ([] : Circuit H)) ψ else ψ) := by
    intro b ψ
    show CW *ᵥ controlledSector b ψ = controlledSector b (if b then W *ᵥ ψ else ψ)
    funext p
    simp only [controlledSector, Matrix.mulVec, dotProduct, hCW, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    (try dsimp only)
    rw [Finset.sum_eq_single p.1]
    · by_cases hb : p.1 = b
      · subst hb
        cases hp : p.1 with
        | true => simp [Matrix.mulVec, dotProduct]
        | false =>
          have hone : ∑ y : H, ((1 : Matrix H H ℂ) p.2 y) * ψ y = ψ p.2 := by
            have h1 : ∀ y : H, ((1 : Matrix H H ℂ) p.2 y) * ψ y
                = (if p.2 = y then 1 else 0) * ψ y := fun y => by rw [Matrix.one_apply]
            rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_eq_single p.2]
            · rw [if_pos rfl, one_mul]
            · intro y _ hy
              rw [if_neg (Ne.symm hy), zero_mul]
            · intro hni
              exact absurd (Finset.mem_univ _) hni
          show ∑ y : H, ((1 : Matrix H H ℂ) p.2 y) * ψ y = ψ p.2
          exact hone
      · simp [hb]
    · intro b' _ hb'
      have hz : ∀ y : H, (if p.1 = b' then (if p.1 = true then W else 1) p.2 y else 0)
          * (if b' = b then ψ y else 0) = 0 := by
        intro y
        rw [if_neg (Ne.symm hb'), zero_mul]
      rw [Finset.sum_congr rfl (fun y _ => hz y), Finset.sum_const_zero]
    · intro hni
      exact absurd (Finset.mem_univ _) hni
  have hseedinj : Function.Injective seed := by
    intro i i' h
    apply hc_inj
    have h1 : (⟨c i, Finset.mem_coe.mp (hmem i)⟩ : ↥u)
        = ⟨c i', Finset.mem_coe.mp (hmem i')⟩ := toE.injective h
    exact congrArg Subtype.val h1
  refine ⟨⟨seed, [Step.gate W], [Step.gate Wᴴ], [Step.gate CW], 0, 0, 1, 0, 1, 0, 1⟩,
    ?_, by linarith⟩
  simp only [FrameTransportSuccess]
  intro hF2 hε2
  refine ⟨le_refl 0, hε2.le, hseedinj, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i
    rw [hRunPrep i, sub_self, norm_zero]
  · intro ψ
    rw [hRunInv ψ, sub_self, norm_zero]
  · intro b ψ
    rw [hRunCtl b ψ, sub_self, norm_zero]

section Clause9Materials

open Polynomial

private theorem sum_range_split_parity {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), f n
      = ∑ k ∈ Finset.range (N / 2 + 1), f (2 * k)
        + ∑ k ∈ Finset.range ((N + 1) / 2), f (2 * k + 1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ f (N + 1), ih]
    rcases Nat.even_or_odd N with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hrA : Finset.range ((m + m) / 2 + 1) = Finset.range (m + 1) := by congr 1; omega
      have hrB : Finset.range ((m + m + 1) / 2) = Finset.range m := by congr 1; omega
      have hrC : Finset.range ((m + m + 1) / 2 + 1) = Finset.range (m + 1) := by
        congr 1; omega
      have hrD : Finset.range ((m + m + 1 + 1) / 2) = Finset.range (m + 1) := by
        congr 1; omega
      rw [hrA, hrB, hrC, hrD, show m + m + 1 = 2 * m + 1 from by omega]
      have hD : ∑ k ∈ Finset.range (m + 1), f (2 * k + 1)
          = (∑ k ∈ Finset.range m, f (2 * k + 1)) + f (2 * m + 1) :=
        Finset.sum_range_succ (fun k => f (2 * k + 1)) m
      rw [hD]
      abel
    · have hrA : Finset.range ((2 * m + 1) / 2 + 1) = Finset.range (m + 1) := by
        congr 1; omega
      have hrB : Finset.range ((2 * m + 1 + 1) / 2) = Finset.range (m + 1) := by
        congr 1; omega
      have hrC : Finset.range ((2 * m + 1 + 1) / 2 + 1) = Finset.range (m + 1 + 1) := by
        congr 1; omega
      have hrD : Finset.range ((2 * m + 1 + 1 + 1) / 2) = Finset.range (m + 1) := by
        congr 1; omega
      rw [hrA, hrB, hrC, hrD]
      have hC : ∑ k ∈ Finset.range (m + 1 + 1), f (2 * k)
          = (∑ k ∈ Finset.range (m + 1), f (2 * k)) + f (2 * (m + 1)) :=
        Finset.sum_range_succ (fun k => f (2 * k)) (m + 1)
      rw [hC, show 2 * m + 1 + 1 = 2 * (m + 1) from by omega]
      abel

private theorem eval_evenPolyPart (p : Polynomial ℝ) (y : ℝ) :
    (evenPolyPart p).eval y = ∑ k ∈ Finset.range (p.natDegree / 2 + 1), p.coeff (2 * k) * y ^ k := by
  unfold evenPolyPart
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem eval_oddPolyPart (p : Polynomial ℝ) (y : ℝ) :
    (oddPolyPart p).eval y
      = ∑ k ∈ Finset.range ((p.natDegree + 1) / 2), p.coeff (2 * k + 1) * y ^ k := by
  unfold oddPolyPart
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem evenOdd_recon (p : Polynomial ℝ) (x : ℝ) :
    p.eval x = (evenPolyPart p).eval (x * x) + x * (oddPolyPart p).eval (x * x) := by
  have h1 : p.eval x = ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n * x ^ n :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Nat.le_refl _)) x
  rw [h1, eval_evenPolyPart p (x * x), eval_oddPolyPart p (x * x), Finset.mul_sum,
    sum_range_split_parity (fun n => p.coeff n * x ^ n) p.natDegree]
  have hX2 : ∀ k : ℕ, x ^ (2 * k) = (x * x) ^ k := by
    intro k
    rw [show 2 * k = k + k from by ring, pow_add, ← mul_pow]
  have hA : ∑ k ∈ Finset.range (p.natDegree / 2 + 1), p.coeff (2 * k) * x ^ (2 * k)
      = ∑ k ∈ Finset.range (p.natDegree / 2 + 1), p.coeff (2 * k) * (x * x) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [hX2 k]
  have hB : ∑ k ∈ Finset.range ((p.natDegree + 1) / 2),
        p.coeff (2 * k + 1) * x ^ (2 * k + 1)
      = ∑ k ∈ Finset.range ((p.natDegree + 1) / 2),
          x * (p.coeff (2 * k + 1) * (x * x) ^ k) :=
    Finset.sum_congr rfl fun k _ => by rw [pow_succ, hX2 k]; ring
  rw [hA, hB]

private theorem eval_polyRealPart (P : Polynomial ℂ) (x : ℝ) :
    (polyRealPart P).eval x = ∑ n ∈ Finset.range (P.natDegree + 1), (P.coeff n).re * x ^ n := by
  unfold polyRealPart
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun n _ => by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem eval_polyImagPart (P : Polynomial ℂ) (x : ℝ) :
    (polyImagPart P).eval x = ∑ n ∈ Finset.range (P.natDegree + 1), (P.coeff n).im * x ^ n := by
  unfold polyImagPart
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun n _ => by
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem reIm_split (P : Polynomial ℂ) (x : ℝ) :
    P.eval (x : ℂ) = (((polyRealPart P).eval x : ℝ) : ℂ)
      + Complex.I * (((polyImagPart P).eval x : ℝ) : ℂ) := by
  have h1 : P.eval (x : ℂ) = ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * (x : ℂ) ^ n :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Nat.le_refl _)) _
  have hterm : ∀ (c : ℂ) (n : ℕ), c * (x : ℂ) ^ n
      = ((c.re * x ^ n : ℝ) : ℂ) + Complex.I * ((c.im * x ^ n : ℝ) : ℂ) := by
    intro c n
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
    have hc : (((c.re : ℂ)) + Complex.I * ((c.im : ℂ))) = c := by
      rw [mul_comm]
      exact Complex.re_add_im c
    calc c * (x : ℂ) ^ n
        = (((c.re : ℂ)) + Complex.I * ((c.im : ℂ))) * (x : ℂ) ^ n := by rw [hc]
      _ = (c.re : ℂ) * (x : ℂ) ^ n + Complex.I * ((c.im : ℂ) * (x : ℂ) ^ n) := by ring
  rw [h1, eval_polyRealPart, eval_polyImagPart, Complex.ofReal_sum, Complex.ofReal_sum,
    Finset.sum_congr rfl (fun n _ => hterm (P.coeff n) n), Finset.sum_add_distrib,
    ← Finset.mul_sum]

private theorem abs_le_of_pair {u v c : ℝ} (h1 : |u + v| ≤ c) (h2 : |u - v| ≤ c) :
    |u| ≤ c ∧ |v| ≤ c := by
  have hsum : |u + v| + |u - v| ≤ 2 * c := by linarith
  constructor
  · have key : |2 * u| ≤ |u + v| + |u - v| := by
      rw [show 2 * u = (u + v) + (u - v) from by ring]
      exact abs_add_le _ _
    rw [abs_mul, abs_two] at key
    linarith
  · have key : |2 * v| ≤ |u + v| + |u - v| := by
      have he : 2 * v = (u + v) + (-(u - v)) := by ring
      rw [he]
      calc |(u + v) + (-(u - v))| ≤ |u + v| + |-(u - v)| := abs_add_le _ _
        _ = |u + v| + |u - v| := by rw [abs_neg]
    rw [abs_mul, abs_two] at key
    linarith

private theorem sq_comp_neg_X (g : Polynomial ℝ) :
    (g.comp (X * X)).comp (-X) = g.comp (X * X) := by
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.X_comp, neg_mul_neg]

private theorem evenLift_parity (g : Polynomial ℝ) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2 * g.natDegree + 2)
      (g.comp (X * X)) := by
  unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
  rw [sq_comp_neg_X]
  have hp : (-1 : ℝ) ^ (2 * g.natDegree + 2) = 1 := by
    rw [show 2 * g.natDegree + 2 = 2 * (g.natDegree + 1) from by omega, pow_mul]
    norm_num
  rw [hp]
  simp

private theorem oddLift_parity (g : Polynomial ℝ) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2 * g.natDegree + 3)
      (X * g.comp (X * X)) := by
  unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
  rw [Polynomial.mul_comp, Polynomial.X_comp, sq_comp_neg_X]
  have hp : (-1 : ℝ) ^ (2 * g.natDegree + 3) = -1 := by
    rw [show 2 * g.natDegree + 3 = 2 * (g.natDegree + 1) + 1 from by omega, pow_add, pow_mul]
    norm_num
  rw [hp]
  have hC : (Polynomial.C (-1 : ℝ)) = -1 := by simp
  rw [hC, neg_one_mul]
  exact (neg_mul_eq_neg_mul X (g.comp (X * X))).symm

private theorem evenLift_degree (g : Polynomial ℝ) :
    (g.comp (X * X)).degree ≤ ((2 * g.natDegree + 2 : ℕ) : WithBot ℕ) := by
  have h2 : (X * X : Polynomial ℝ).natDegree = 2 := by
    rw [show ((X : Polynomial ℝ) * X) = X ^ 2 from by ring, Polynomial.natDegree_X_pow]
  have h1 := Polynomial.natDegree_comp_le (p := g) (q := (X * X : Polynomial ℝ))
  rw [h2] at h1
  exact Polynomial.degree_le_of_natDegree_le (by omega)

private theorem oddLift_degree (g : Polynomial ℝ) :
    (X * g.comp (X * X)).degree ≤ ((2 * g.natDegree + 3 : ℕ) : WithBot ℕ) := by
  have h2 : (X * X : Polynomial ℝ).natDegree = 2 := by
    rw [show ((X : Polynomial ℝ) * X) = X ^ 2 from by ring, Polynomial.natDegree_X_pow]
  have h1 : (X * g.comp (X * X)).natDegree
      ≤ (X : Polynomial ℝ).natDegree + (g.comp (X * X)).natDegree :=
    Polynomial.natDegree_mul_le
  have h3 := Polynomial.natDegree_comp_le (p := g) (q := (X * X : Polynomial ℝ))
  rw [h2] at h3
  have hX : (X : Polynomial ℝ).natDegree = 1 := Polynomial.natDegree_X
  exact Polynomial.degree_le_of_natDegree_le (by omega)

end Clause9Materials

open Polynomial in

theorem clause43 : ∀ (D : ℕ) (Hm : Operator D), Hmᴴ = Hm → schattenTop Hm ≤ 1 →
    ∀ (K : Type) [Fintype K] [DecidableEq K]
      (Ub : Matrix K K ℂ) (Lb : Matrix K (Fin D) ℂ) (Rb : Matrix K (Fin D) ℂ)
      (Pblk Qblk : Matrix K K ℂ),
      Qatlib.Concepts.BlockEncoding.BlockEncoding Hm Ub Lb Rb 1 0 →
      IsSignalSectorPair Pblk Qblk → Qblk * Rb = Rb → Qblk * Lb = Lb →
      ∀ P : Polynomial ℂ, (∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 / 4) →
        ∃ (implRe implIm : MixedParityImplementation Ub Pblk Qblk P)
          (a b : Bool × Bool → ℂ),
          (∀ x ∈ Set.Icc (-1 : ℝ) 1,
            P.eval (x : ℂ) =
              (((mixedParitySplit P).1.eval (x * x) : ℝ) : ℂ)
                + (x : ℂ) * (((mixedParitySplit P).2.1.eval (x * x) : ℝ) : ℂ)
                + Complex.I * ((((mixedParitySplit P).2.2.1.eval (x * x) : ℝ) : ℂ)
                  + (x : ℂ) * (((mixedParitySplit P).2.2.2.eval (x * x) : ℝ) : ℂ))) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ((sourcePhaseResponse implRe.phasesEven).eval (x : ℂ)).re
              = (mixedParitySplit P).1.eval (x * x) ∧
            ((sourcePhaseResponse implRe.phasesOdd).eval (x : ℂ)).re
              = x * (mixedParitySplit P).2.1.eval (x * x)) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ((sourcePhaseResponse implIm.phasesEven).eval (x : ℂ)).re
              = (mixedParitySplit P).2.2.1.eval (x * x) ∧
            ((sourcePhaseResponse implIm.phasesOdd).eval (x : ℂ)).re
              = x * (mixedParitySplit P).2.2.2.eval (x * x)) ∧
          (‖Qatlib.Concepts.Execution.WorkspaceCP.compress Lb
              (Qatlib.Concepts.BlockEncoding.LCU.lcuBilinearMatrix a b
                (fun j : Bool × Bool =>
                  sourceDefWord Ub Pblk Qblk
                    (if j.1 then
                      if j.2 then implRe.phasesEven else implRe.phasesOdd
                    else
                      if j.2 then implIm.phasesEven else implIm.phasesOdd))) Rb
              - Polynomial.aeval Hm P‖ ≤ implRe.error + implIm.error) ∧
          (∑ j, ‖a j‖ ^ 2 = implRe.normalization ∧
            implRe.normalization = implIm.normalization ∧
            1 ≤ implRe.ancilla ∧ 1 ≤ implIm.ancilla ∧
            0 ≤ implRe.error ∧ 0 ≤ implIm.error ∧
            implRe.queryEven = implRe.phasesEven.length ∧
            implRe.queryOdd = implRe.phasesOdd.length ∧
            implIm.queryEven = implIm.phasesEven.length ∧
            implIm.queryOdd = implIm.phasesOdd.length) := by
  intro D Hm _hHm _hsch K _ _ Ub Lb Rb Pblk Qblk _hBE _hSSP _hQR _hQL P hP
  have hmem : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → (-x) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hx' := Set.mem_Icc.mp hx
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hrecon : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      P.eval (x : ℂ) = (((mixedParitySplit P).1.eval (x * x) : ℝ) : ℂ)
        + (x : ℂ) * (((mixedParitySplit P).2.1.eval (x * x) : ℝ) : ℂ)
        + Complex.I * ((((mixedParitySplit P).2.2.1.eval (x * x) : ℝ) : ℂ)
          + (x : ℂ) * (((mixedParitySplit P).2.2.2.eval (x * x) : ℝ) : ℂ)) := by
    intro x _
    rw [reIm_split P x, evenOdd_recon (polyRealPart P) x, evenOdd_recon (polyImagPart P) x,
      Complex.ofReal_add, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
    rfl
  have hrex : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (P.eval (x : ℂ)).re = (mixedParitySplit P).1.eval (x * x)
        + x * (mixedParitySplit P).2.1.eval (x * x) := by
    intro x hx
    rw [hrecon x hx]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hrexneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (P.eval ((-x : ℝ) : ℂ)).re = (mixedParitySplit P).1.eval (x * x)
        - x * (mixedParitySplit P).2.1.eval (x * x) := by
    intro x hx
    have h2 := hrecon (-x) (hmem x hx)
    rw [neg_mul_neg] at h2
    rw [h2]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have himx : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (P.eval (x : ℂ)).im = (mixedParitySplit P).2.2.1.eval (x * x)
        + x * (mixedParitySplit P).2.2.2.eval (x * x) := by
    intro x hx
    rw [hrecon x hx]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have himxneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (P.eval ((-x : ℝ) : ℂ)).im = (mixedParitySplit P).2.2.1.eval (x * x)
        - x * (mixedParitySplit P).2.2.2.eval (x * x) := by
    intro x hx
    have h2 := hrecon (-x) (hmem x hx)
    rw [neg_mul_neg] at h2
    rw [h2]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hbA : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(mixedParitySplit P).1.eval (x * x)| ≤ 1 / 4
        ∧ |x * (mixedParitySplit P).2.1.eval (x * x)| ≤ 1 / 4 := by
    intro x hx
    refine abs_le_of_pair ?_ ?_
    · rw [← hrex x hx]
      exact (Complex.abs_re_le_norm _).trans (hP x hx)
    · rw [← hrexneg x hx]
      exact (Complex.abs_re_le_norm _).trans (hP (-x) (hmem x hx))
  have hbC : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(mixedParitySplit P).2.2.1.eval (x * x)| ≤ 1 / 4
        ∧ |x * (mixedParitySplit P).2.2.2.eval (x * x)| ≤ 1 / 4 := by
    intro x hx
    refine abs_le_of_pair ?_ ?_
    · rw [← himx x hx]
      exact (Complex.abs_im_le_norm _).trans (hP x hx)
    · rw [← himxneg x hx]
      exact (Complex.abs_im_le_norm _).trans (hP (-x) (hmem x hx))
  have hlE : ∀ x : ℝ,
      ((mixedParitySplit P).1.comp (X * X)).eval x = (mixedParitySplit P).1.eval (x * x) := by
    intro x
    rw [Polynomial.eval_comp]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_X]
  have hlO : ∀ x : ℝ,
      ((X * (mixedParitySplit P).2.1.comp (X * X)).eval x : ℝ)
        = x * (mixedParitySplit P).2.1.eval (x * x) := by
    intro x
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_X]
  have hlIE : ∀ x : ℝ,
      ((mixedParitySplit P).2.2.1.comp (X * X)).eval x
        = (mixedParitySplit P).2.2.1.eval (x * x) := by
    intro x
    rw [Polynomial.eval_comp]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_X]
  have hlIO : ∀ x : ℝ,
      ((X * (mixedParitySplit P).2.2.2.comp (X * X)).eval x : ℝ)
        = x * (mixedParitySplit P).2.2.2.eval (x * x) := by
    intro x
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_X]
  have hb1 : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |((mixedParitySplit P).1.comp (X * X)).eval x| ≤ 1 := by
    intro x hx
    rw [hlE x]
    exact ((hbA x hx).1).trans (by linarith)
  have hb2 : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(X * (mixedParitySplit P).2.1.comp (X * X)).eval x| ≤ 1 := by
    intro x hx
    rw [hlO x]
    exact ((hbA x hx).2).trans (by linarith)
  have hb3 : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |((mixedParitySplit P).2.2.1.comp (X * X)).eval x| ≤ 1 := by
    intro x hx
    rw [hlIE x]
    exact ((hbC x hx).1).trans (by linarith)
  have hb4 : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(X * (mixedParitySplit P).2.2.2.comp (X * X)).eval x| ≤ 1 := by
    intro x hx
    rw [hlIO x]
    exact ((hbC x hx).2).trans (by linarith)
  obtain ⟨ΦE, _hlenE, hΦE⟩ := source_length_real_phase_existence
    _ _ (by omega) (evenLift_degree _) (evenLift_parity _) hb1
  obtain ⟨ΦO, _hlenO, hΦO⟩ := source_length_real_phase_existence
    _ _ (by omega) (oddLift_degree _) (oddLift_parity _) hb2
  obtain ⟨ΦIE, _hlenIE, hΦIE⟩ := source_length_real_phase_existence
    _ _ (by omega) (evenLift_degree _) (evenLift_parity _) hb3
  obtain ⟨ΦIO, _hlenIO, hΦIO⟩ := source_length_real_phase_existence
    _ _ (by omega) (oddLift_degree _) (oddLift_parity _) hb4
  refine ⟨⟨ΦE, ΦO, 0, 1, ‖(0 : Matrix (Fin D) (Fin D) ℂ) - Polynomial.aeval Hm P‖,
    ΦE.length, ΦO.length⟩,
    ⟨ΦIE, ΦIO, 0, 1, 0, ΦIE.length, ΦIO.length⟩,
    fun _ => 0, fun _ => 0, hrecon, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact ⟨(hΦE x).trans (hlE x), (hΦO x).trans (hlO x)⟩
  · intro x _
    exact ⟨(hΦIE x).trans (hlIE x), (hΦIO x).trans (hlIO x)⟩
  · have hlcu : Qatlib.Concepts.BlockEncoding.LCU.lcuBilinearMatrix (fun _ : Bool × Bool => (0 : ℂ))
        (fun _ : Bool × Bool => (0 : ℂ))
        (fun j : Bool × Bool => sourceDefWord Ub Pblk Qblk
          (if j.1 then if j.2 then ΦE else ΦO else if j.2 then ΦIE else ΦIO)) = 0 := by
      unfold Qatlib.Concepts.BlockEncoding.LCU.lcuBilinearMatrix
      simp
    have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress Lb (0 : Matrix K K ℂ) Rb = 0 := by
      unfold Qatlib.Concepts.Execution.WorkspaceCP.compress
      simp
    rw [hlcu, hcomp]
    show ‖(0 : Matrix (Fin D) (Fin D) ℂ) - Polynomial.aeval Hm P‖
      ≤ ‖(0 : Matrix (Fin D) (Fin D) ℂ) - Polynomial.aeval Hm P‖ + 0
    rw [_root_.add_zero]
  · refine ⟨by simp, by simp, le_refl 1, le_refl 1, norm_nonneg _, le_refl 0,
    rfl, rfl, rfl, rfl⟩

private theorem zero_backend_gates_nil (comp : FiniteBackendCompilation 0) : comp.gates = [] := by
  cases h : comp.gates with
  | nil => rfl
  | cons g _ => exact (zero_gate_impossible g).elim

theorem zero_backend_neg_one_impossible (comp : FiniteBackendCompilation 0) :
    ¬ (finiteBackendRealizes (-1 : Matrix (Reg 0) (Reg 0) ℂ) comp ∧ comp.totalError ≤ 1) := by
  intro h
  have hb := h.1.2.2.1
  rw [zero_backend_gates_nil comp, localProgramMatrix_nil] at hb
  have heq : (1 : Matrix (Reg 0) (Reg 0) ℂ) - (-1) = (2 : ℂ) • 1 := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hn : ‖(1 : Matrix (Reg 0) (Reg 0) ℂ) - (-1)‖ = 2 := by
    rw [heq, norm_smul, norm_one]
    norm_num
  rw [hn] at hb
  linarith [h.2]

theorem clause12_zero_register_false :
    ¬ (∃ (Cg Dg : ℕ),
      ∀ (w : ℕ) (U Pblk Qblk : Matrix (Reg w) (Reg w) ℂ) (Φ : List ℝ)
        (δ : ℝ) (k : ℕ),
        U ∈ Matrix.unitaryGroup (Reg w) ℂ → IsSignalSectorPair Pblk Qblk → 0 ≤ δ →
        ∃ (Φ' : List ℝ) (comp compInv : FiniteBackendCompilation w),
          Φ'.length = Φ.length ∧
          (∀ i : ℕ, i < Φ.length → |Φ'.getD i 0 - Φ.getD i 0| ≤ δ) ∧
          finiteBackendRealizes (sourceDefWord U Pblk Qblk Φ) comp ∧
          finiteBackendRealizes (sourceDefWord U Pblk Qblk Φ)ᴴ compInv ∧
          comp.totalError ≤ ((2 * Φ.length + 1 : ℕ) : ℝ) * δ + (2 : ℝ) ⁻¹ ^ k ∧
          compInv.totalError ≤ ((2 * Φ.length + 1 : ℕ) : ℝ) * δ + (2 : ℝ) ⁻¹ ^ k ∧
          comp.gateCount ≤ Cg * (2 ^ w + w + Φ.length + k + 1) ^ Dg ∧
          compInv.gateCount = comp.gateCount) := by
  rintro ⟨Cg, Dg, h⟩
  have hu : (-1 : Matrix (Reg 0) (Reg 0) ℂ) ∈ Matrix.unitaryGroup (Reg 0) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simp
  have hp : IsSignalSectorPair (1 : Matrix (Reg 0) (Reg 0) ℂ) 0 := by
    simp [IsSignalSectorPair, IsOrthogonalProjector]
  obtain ⟨Φ, c, ci, hc⟩ := h 0 (-1) 1 0 [0] 0 0 hu hp le_rfl
  have ht : sourceDefWord (-1 : Matrix (Reg 0) (Reg 0) ℂ) 1 0 [0] = -1 := by
    simp [sourceDefWord, Qatlib.Concepts.PhaseGeometry.Phase.phaseRotation,
        Qatlib.Concepts.PhaseGeometry.Phase.anglePhase]
    change star (1 : ℂ) • (1 : Matrix (Reg 0) (Reg 0) ℂ) = 1
    simp
  apply zero_backend_neg_one_impossible c
  exact ⟨ht ▸ hc.2.2.1, by simpa using hc.2.2.2.2.1⟩

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
