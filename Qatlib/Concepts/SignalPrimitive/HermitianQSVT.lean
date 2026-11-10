/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
import Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def hermitianResponseWord {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    (F : Matrix H I ℂ) (d : ℕ) (base : ℂ) (zs : List ℂ) : List (AdjointStep (Bool×H)) :=
  if d%2=1 then compileRealPartQSVT (rangeProjector F) (rangeProjector F) base zs
  else (compileRealPartQSVT (rangeProjector F) (rangeProjector F) base zs).map swapQueries

theorem hermitian_odd_polynomial_factor {p : Polynomial ℝ} {d : ℕ}
    (hp : HasRealParity d p) (hd : d%2=1) :
    ∃ q : Polynomial ℝ,p=X*q.comp (X^2) := by
  have ho : Odd d := Nat.odd_iff.mpr hd
  have hodd : p.comp (-X)= -p := by
    simpa only [HasRealParity,ho.neg_one_pow,Polynomial.C_neg,Polynomial.C_1,neg_one_mul] using hp
  have hc : p.coeff 0=0 := by
    have h := congrArg (fun q : Polynomial ℝ => q.eval 0) hodd
    simp only [Polynomial.eval_comp,Polynomial.eval_neg,Polynomial.eval_X,neg_zero,← Polynomial.coeff_zero_eq_eval_zero] at h
    linarith
  have hdiv : X*p.divX=p := by
    simpa only [hc,Polynomial.C_0,add_zero] using (Polynomial.X_mul_divX_add p)
  have heven : p.divX.comp (-X)=p.divX := by
    apply mul_left_cancel₀ (show (-X : Polynomial ℝ)≠0 by simp)
    calc
      (-X)*p.divX.comp (-X)=(X*p.divX).comp (-X) := by simp only [mul_comp,X_comp]
      _=p.comp (-X) := congrArg (fun q : Polynomial ℝ => q.comp (-X)) hdiv
      _= -p := hodd
      _=(-X)*p.divX := by rw [neg_mul,hdiv]
  refine ⟨contract 2 p.divX,?_⟩
  rw [comp_square_contract_of_even heven]
  exact hdiv.symm

theorem hermitian_dilation_polynomial_odd {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (p : Polynomial ℝ) (d : ℕ)
    (hp : HasRealParity d p) (hd : d%2=1) :
    (aeval (hermitianDilation A) (p.map Complex.ofRealHom)).toBlocks₁₂=
      aeval A (p.map Complex.ofRealHom) := by
  have ha : Aᴴ=A := hA
  obtain ⟨q,hq⟩ := hermitian_odd_polynomial_factor hp hd
  have hm : p.map Complex.ofRealHom=oddSingularPolynomial (q.map Complex.ofRealHom) := by
    rw [hq]
    simp only [Polynomial.map_mul,Polynomial.map_X,Polynomial.map_comp,Polynomial.map_pow,
      oddSingularPolynomial,evenSingularPolynomial]
  rw [hm,aeval_oddSingularPolynomial]
  simp only [Matrix.toBlocks_fromBlocks₁₂,oddSingularPolynomial,evenSingularPolynomial,
    Polynomial.aeval_mul,Polynomial.aeval_X,Polynomial.aeval_comp,Polynomial.aeval_X_pow,
    ha,pow_two]

theorem hermitian_dilation_polynomial_even {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (p : Polynomial ℝ) (d : ℕ)
    (hp : HasRealParity d p) (hd : d%2=0) :
    (aeval (hermitianDilation A) (p.map Complex.ofRealHom)).toBlocks₂₂=
      aeval A (p.map Complex.ofRealHom) := by
  have ha : Aᴴ=A := hA
  have he : Even d := Nat.even_iff.mpr hd
  have heven : p.comp (-X)=p := by
    simpa only [HasRealParity,he.neg_one_pow,Polynomial.C_1,one_mul] using hp
  let q := contract 2 p
  have hq : q.comp (X^2)=p := comp_square_contract_of_even heven
  have hm : p.map Complex.ofRealHom=evenSingularPolynomial (q.map Complex.ofRealHom) := by
    rw [← hq]
    simp only [Polynomial.map_comp,Polynomial.map_pow,Polynomial.map_X,evenSingularPolynomial]
  rw [hm,aeval_evenSingularPolynomial]
  simp only [Matrix.toBlocks_fromBlocks₂₂,evenSingularPolynomial,Polynomial.aeval_comp,
    Polynomial.aeval_X_pow,Polynomial.aeval_mul,Polynomial.aeval_X,ha,pow_two]

theorem hermitian_encoding_spectrum_interval {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (i : Fin (Fintype.card I)) : orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hn : ‖A‖ ≤ 1 := by
    rw [← h.encoded]
    exact (compress_norm_le h.left_isometry h.right_isometry U).trans
        (unitary_norm_le_one h.unitary)
  have hv := Matrix.l2_opNorm_mulVec A (orderedHermitianBasis hA i)
  change ‖A.toEuclideanLin (orderedHermitianBasis hA i)‖ ≤ ‖A‖*‖orderedHermitianBasis hA i‖ at hv
  rw [orderedHermitianBasis_action,norm_smul,(orderedHermitianBasis hA).norm_eq_one,
    mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at hv
  exact abs_le.mp (hv.trans hn)

theorem hermitianResponseWord_counts {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    (F : Matrix H I ℂ) (d : ℕ) (base : ℂ) (zs : List ℂ) (hn : zs.length=d) :
    adjointQueryCount (hermitianResponseWord F d base zs)=d ∧
      adjointGateCount (hermitianResponseWord F d base zs)=d+1 := by
  have h := counts_compileRealPartQSVT (rangeProjector F) (rangeProjector F) base zs
  unfold hermitianResponseWord
  split_ifs
  · simpa only [hn] using h
  · simpa only [adjointQueryCount_swapQueries,adjointGateCount_swapQueries,hn] using h

theorem hermitian_same_word_actual_qsvt_frobenius_stability : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ)
    (p : Polynomial ℝ) (d : ℕ) (L : ℝ),
  A.IsHermitian → B.IsHermitian → ProjectedUnitaryEncoding A U F F → ProjectedUnitaryEncoding B V F F →
  p.degree≤(d:WithBot ℕ) → HasRealParity d p → (∀ x∈Set.Icc (-1:ℝ) 1,|p.eval x|≤1) → 0≤ L →
  (∀ x∈Set.Icc (-1:ℝ) 1,∀ y∈Set.Icc (-1:ℝ) 1,|p.eval x-p.eval y|≤ L*|x-y|) →
  ∃ (base : ℂ) (zs : List ℂ),IsPhase base ∧ (∀ z∈zs,IsPhase z) ∧ zs.length= d ∧
    (∀ x : ℝ,((responseP base zs).eval (x:ℂ)).re= p.eval x) ∧
    let cs:= hermitianResponseWord F d base zs;
    ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
      (evaluate (parallelOracle U) cs) (averageFrame F) (averageFrame F) ∧
    ProjectedUnitaryEncoding (aeval B (p.map Complex.ofRealHom))
      (evaluate (parallelOracle V) cs) (averageFrame F) (averageFrame F) ∧
    adjointQueryCount cs= d ∧ adjointGateCount cs= d+1 ∧
    spectralFrobenius (compress (averageFrame F) (evaluate (parallelOracle U) cs) (averageFrame F)-
      compress (averageFrame F) (evaluate (parallelOracle V) cs) (averageFrame F))≤ L*spectralFrobenius (A-B) := by
  intro H I _ _ _ _ A B U V F p d L hA hB hAU hBV hpdeg hpar hbounded hL hLip
  obtain ⟨base,zs,hbase,hzs,hn,hpoly,hresponse⟩ := exists_phases_of_bounded hpdeg hpar hbounded
  have hreal : realPartPolynomial (responseP base zs)=p.map Complex.ofRealHom := by
    unfold realPartPolynomial
    change (2 : ℂ)⁻¹ •
        (responseP base zs+Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs))=_
    rw [hpoly,Polynomial.C_mul',smul_smul]
    norm_num
  have hactual (X : Matrix I I ℂ) (W : Matrix H H ℂ) (hX : X.IsHermitian)
      (hXW : ProjectedUnitaryEncoding X W F F) :
      ProjectedUnitaryEncoding (aeval X (p.map Complex.ofRealHom))
        (evaluate (parallelOracle W) (hermitianResponseWord F d base zs))
          (averageFrame F) (averageFrame F) := by
    unfold hermitianResponseWord
    split_ifs with hodd
    · rw [evaluate_compileRealPartQSVT]
      have h := realPartQSVT_odd_projectedEncoding hXW hbase zs hzs (by simpa only [hn] using hodd)
      rw [hreal,hermitian_dilation_polynomial_odd X hX p d hpar hodd] at h
      exact h
    · have heven : d%2=0 := by omega
      rw [evaluate_swapQueries,parallelOracle_adjoint,evaluate_compileRealPartQSVT]
      have h :=
          realPartQSVT_even_right_projectedEncoding hXW hbase zs hzs
          (by simpa only [hn] using heven)
      rw [hreal,hermitian_dilation_polynomial_even X hX p d hpar heven] at h
      exact h
  have hEA := hactual A U hA hAU
  have hEB := hactual B V hB hBV
  have hcounts := hermitianResponseWord_counts F d base zs hn
  refine ⟨base,zs,hbase,hzs,hn,hresponse,hEA,hEB,hcounts.1,hcounts.2,?_⟩
  rw [hEA.encoded,hEB.encoded]
  have h := hermitian_spectral_function_frobenius_stability I A B hA hB
    (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) L hL (fun i j => ?_)
  · rw [hermitian_spectral_polynomial_evaluation I A hA p,
      hermitian_spectral_polynomial_evaluation I B hB p] at h
    exact h
  · simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
      hLip _ (hermitian_encoding_spectrum_interval A hA U F hAU i)
        _ (hermitian_encoding_spectrum_interval B hB V F hBV j)

theorem hermitian_same_word_actual_perturbed_postselection : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ)
    (p : Polynomial ℝ) (d : ℕ) (L : ℝ) (ψ : QState I),
  A.IsHermitian → B.IsHermitian → ProjectedUnitaryEncoding A U F F → ProjectedUnitaryEncoding B V F F →
  p.degree≤(d:WithBot ℕ) → HasRealParity d p → (∀ x∈Set.Icc (-1:ℝ) 1,|p.eval x|≤1) → 0≤ L →
  (∀ x∈Set.Icc (-1:ℝ) 1,∀ y∈Set.Icc (-1:ℝ) 1,|p.eval x-p.eval y|≤ L*|x-y|) → Normalized ψ →
  let T:= aeval A (p.map Complex.ofRealHom);
  let η:= L*spectralFrobenius (A-B);
  η<‖stateVector (T*ᵥψ)‖ →
  ∃ (base : ℂ) (zs : List ℂ),IsPhase base ∧ (∀ z∈zs,IsPhase z) ∧ zs.length= d ∧
    (∀ x : ℝ,((responseP base zs).eval (x:ℂ)).re= p.eval x) ∧
    let cs:= hermitianResponseWord F d base zs;
    let W:= evaluate (parallelOracle V) cs;
    (‖stateVector (T*ᵥψ)‖-η)^2≤ postselectionProbability W (averageFrame F) (averageFrame F) ψ ∧
    (∃ φ : QState I,postselectionOutput W (averageFrame F) (averageFrame F) ψ= some φ ∧
      IsNormalizedApplication T ψ φ (2*η/‖stateVector (T*ᵥψ)‖)) ∧
    adjointQueryCount cs= d ∧ adjointGateCount cs= d+1 := by
  intro H I _ _ _ _ A B U V F p d L ψ hA hB hAU hBV hpdeg hpar hbounded hL hLip hψ
  (try dsimp only)
  intro hgap
  obtain ⟨base,zs,hbase,hzs,hn,hresponse,hEA,hEB,hqueries,hgates,hFrob⟩ :=
    hermitian_same_word_actual_qsvt_frobenius_stability H I A B U V F p d L
      hA hB hAU hBV hpdeg hpar hbounded hL hLip
  have hη : 0 ≤ L*spectralFrobenius (A-B) := mul_nonneg hL (spectralFrobenius_nonneg _)
  have herr : ‖aeval A (p.map Complex.ofRealHom)-
      compress (averageFrame F) (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
        (averageFrame F)‖ ≤ L*spectralFrobenius (A-B) := by
    have h := (spectral_operator_norm_le_frobenius
      (compress (averageFrame F) (evaluate (parallelOracle U) (hermitianResponseWord F d base zs))
        (averageFrame F)-
       compress (averageFrame F) (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
        (averageFrame F))).trans hFrob
    simpa only [hEA.encoded] using h
  have hblock : BlockEncoding (aeval A (p.map Complex.ofRealHom))
      (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
      (averageFrame F) (averageFrame F) 1 (L*spectralFrobenius (A-B)) :=
    ⟨hEB.unitary,hEB.left_isometry,hEB.right_isometry,by norm_num,hη,
      by simpa only [one_smul] using herr⟩
  refine ⟨base,zs,hbase,hzs,hn,hresponse,?_,?_,hqueries,hgates⟩
  · simpa only [div_one] using
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hblock hψ hgap.le
  · exact (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap hblock hψ hgap).2

end Qatlib.Concepts.SignalPrimitive.HermitianQSVT
