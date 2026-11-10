/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond

namespace Qatlib.Concepts.SchattenDiamond.DiamondSdp

open Matrix Qatlib
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable def measurementSuccess {ι : Type} [Fintype ι] [DecidableEq ι]
    (M ρ σ : Matrix ι ι ℂ) : ℝ :=
  ((M * ρ).trace.re + ((1 - M) * σ).trace.re) / 2

theorem tensorLeft_trace_sub_eq_zero {D E r : ℕ} {T S : Operator D →ₗ[ℂ] Operator E}
    (hT : TracePreserving T) (hS : TracePreserving S)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.trace (tensorLeft (T - S) X) = 0 := by
  rw [Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_tensorLeft_map_sub, Matrix.trace_sub,
    Qatlib.Concepts.ReferenceError.RefTraceError.tensorLeft_trace_map T hT X,
    Qatlib.Concepts.ReferenceError.RefTraceError.tensorLeft_trace_map S hS X, sub_self]

theorem measurementSuccess_eq_half_add_centered {ι : Type} [Fintype ι] [DecidableEq ι]
    {M ρ σ : Matrix ι ι ℂ} (hσ : Matrix.trace σ = 1) (hΔ : Matrix.trace (ρ - σ) = 0) :
    measurementSuccess M ρ σ = 1/2 + ((M - (1/2 : ℂ) • 1) * (ρ - σ)).trace.re / 2 := by
  have hexp : measurementSuccess M ρ σ = 1/2 + (M * (ρ - σ)).trace.re / 2 := by
    simp only [measurementSuccess, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_sub, Complex.add_re, Complex.sub_re, hσ, Complex.one_re]
    ring
  have hsmul : ((1/2 : ℂ) • 1) * (ρ - σ) = (1/2 : ℂ) • (ρ - σ) := by
    rw [smul_mul_assoc, Matrix.one_mul]
  have hcenter : ((M - (1/2 : ℂ) • 1) * (ρ - σ)).trace.re
      = (M * (ρ - σ)).trace.re := by
    rw [Matrix.sub_mul, Matrix.trace_sub, hsmul, Matrix.trace_smul, hΔ, smul_zero, sub_zero]
  rw [hexp, hcenter]

private lemma opNorm_mem_unitaryGroup_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : Matrix ι ι ℂ} (hV : V ∈ Matrix.unitaryGroup ι ℂ) : ‖V‖ ≤ 1 := by
  have hU : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hV
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hU] at h
  have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    rw [show (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ => (1 : ℂ)) from
        Matrix.diagonal_one.symm, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun _ => by simp
  nlinarith [norm_nonneg V]

private lemma opNorm_conj_diagonal_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ)
    (hν : ∀ j, |ν j| ≤ 1/2) :
    ‖V * Matrix.diagonal (fun j => (ν j : ℂ)) * Vᴴ‖ ≤ 1/2 := by
  have hVn : ‖V‖ ≤ 1 := opNorm_mem_unitaryGroup_le_one hV
  have hVctn : ‖Vᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hVn
  have hD : ‖Matrix.diagonal (fun j => (ν j : ℂ))‖ ≤ 1/2 := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j => ?_
    rw [Complex.norm_real]
    exact hν j
  calc ‖V * Matrix.diagonal (fun j => (ν j : ℂ)) * Vᴴ‖
      ≤ ‖V‖ * (‖Matrix.diagonal (fun j => (ν j : ℂ))‖ * ‖Vᴴ‖) := by
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        calc ‖V * Matrix.diagonal (fun j => (ν j : ℂ))‖ * ‖Vᴴ‖
            ≤ (‖V‖ * ‖Matrix.diagonal (fun j => (ν j : ℂ))‖) * ‖Vᴴ‖ :=
              mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
          _ = ‖V‖ * (‖Matrix.diagonal (fun j => (ν j : ℂ))‖ * ‖Vᴴ‖) := by ring
    _ ≤ 1 * (1/2 * 1) := by gcongr
    _ = 1/2 := by ring

theorem opNorm_centered_effect_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef) :
    ‖M - (1/2 : ℂ) • 1‖ ≤ 1/2 := by
  have hHer : M.IsHermitian := hM.1
  obtain ⟨V, μ, hVmem, hspect⟩ : ∃ V : Matrix ι ι ℂ, ∃ μ : ι → ℝ,
      V ∈ Matrix.unitaryGroup ι ℂ ∧
      M = V * Matrix.diagonal (fun j => (μ j : ℂ)) * Vᴴ :=
    ⟨hHer.eigenvectorUnitary, hHer.eigenvalues, hHer.eigenvectorUnitary.2, by
      simpa [Function.comp_def, Matrix.star_eq_conjTranspose] using hHer.spectral_theorem⟩
  have hVV : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hVmem
  have hVHV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hVmem
  have hdiag : Vᴴ * M * V = Matrix.diagonal (fun j => (μ j : ℂ)) := by
    rw [hspect]
    have hassoc : Vᴴ * (V * Matrix.diagonal (fun j => (μ j : ℂ)) * Vᴴ) * V
        = (Vᴴ * V) * Matrix.diagonal (fun j => (μ j : ℂ)) * (Vᴴ * V) := by noncomm_ring
    rw [hassoc, hVHV, Matrix.one_mul, Matrix.mul_one]
  have hMdiag : (Vᴴ * M * V).PosSemidef := hM.conjTranspose_mul_mul_same V
  rw [hdiag, Matrix.posSemidef_diagonal_iff] at hMdiag
  have hμpos : ∀ j, 0 ≤ μ j := by
    intro j
    have h0 := hMdiag j
    rw [Complex.le_def] at h0
    simp at h0
    linarith
  have hconj : Vᴴ * (1 - M) * V
      = Matrix.diagonal (fun j => (1 - (μ j : ℂ))) := by
    have h0 : Vᴴ * (1 - M) * V
        = 1 - Matrix.diagonal (fun j => (μ j : ℂ)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hdiag]
      congr 1
      calc Vᴴ * 1 * V = Vᴴ * V := by rw [Matrix.mul_one]
        _ = 1 := hVHV
    rw [h0, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  have hCdiag : (Vᴴ * (1 - M) * V).PosSemidef := hMc.conjTranspose_mul_mul_same V
  rw [hconj, Matrix.posSemidef_diagonal_iff] at hCdiag
  have hμle : ∀ j, μ j ≤ 1 := by
    intro j
    have h0 := hCdiag j
    rw [Complex.le_def] at h0
    simp at h0
    linarith
  have hkey : (1/2 : ℂ) • (1 : Matrix ι ι ℂ) = V * ((1/2 : ℂ) • 1) * Vᴴ := by
    rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hVV]
  have hhalf : (1/2 : ℂ) • (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ => (1/2 : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hcenter : M - (1/2 : ℂ) • 1
      = V * Matrix.diagonal (fun j => ((μ j - 1/2 : ℝ) : ℂ)) * Vᴴ := by
    rw [hspect, hkey, ← Matrix.sub_mul, ← Matrix.mul_sub, hhalf, Matrix.diagonal_sub]
    congr 1
    funext j
    push_cast
    ring
  rw [hcenter]
  exact opNorm_conj_diagonal_le V hVmem (fun j => μ j - 1/2)
    (fun j => abs_le.mpr ⟨by linarith [hμpos j, hμle j], by linarith [hμpos j, hμle j]⟩)

theorem abs_trace_centered_effect_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {M Δ : Matrix ι ι ℂ} (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef) :
    |((M - (1/2 : ℂ) • 1) * Δ).trace.re| ≤ Matrix.traceNorm Δ / 2 := by
  calc |((M - (1/2 : ℂ) • 1) * Δ).trace.re|
      ≤ ‖((M - (1/2 : ℂ) • 1) * Δ).trace‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm ((M - (1/2 : ℂ) • 1) * Δ) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M - (1/2 : ℂ) • 1‖ * Matrix.traceNorm Δ :=
          Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1/2 * Matrix.traceNorm Δ :=
          mul_le_mul_of_nonneg_right (opNorm_centered_effect_le hM hMc)
            (Matrix.traceNorm_nonneg _)
    _ = Matrix.traceNorm Δ / 2 := by ring

theorem measurementSuccess_le_half_add_quarter {ι : Type} [Fintype ι] [DecidableEq ι]
    {M ρ σ : Matrix ι ι ℂ} (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef)
    (hσ : Matrix.trace σ = 1) (hΔ : Matrix.trace (ρ - σ) = 0) :
    measurementSuccess M ρ σ ≤ 1/2 + Matrix.traceNorm (ρ - σ) / 4 := by
  rw [measurementSuccess_eq_half_add_centered hσ hΔ]
  have h := abs_trace_centered_effect_le hM hMc (Δ := ρ - σ)
  rcases abs_le.mp h with ⟨h1, h2⟩
  linarith

theorem measurementSuccess_le_half_add_diamond {D E r : ℕ}
    {T S : Operator D →ₗ[ℂ] Operator E}
    (hT : TracePreserving T) (hS : TracePreserving S)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hX : X.PosSemidef) (hXtr : Matrix.trace X = 1)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ)
    (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (T - S) ≤ ENNReal.ofReal δ) :
    measurementSuccess M (tensorLeft T X) (tensorLeft S X) ≤ 1/2 + δ / 4 := by
  have hσ : Matrix.trace (tensorLeft S X) = 1 := by
    rw [Qatlib.Concepts.ReferenceError.RefTraceError.tensorLeft_trace_map S hS X, hXtr]
  have hΔ0 : Matrix.trace (tensorLeft T X - tensorLeft S X) = 0 := by
    rw [← Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_tensorLeft_map_sub,
      tensorLeft_trace_sub_eq_zero hT hS]
  have hXn : Matrix.traceNorm X = 1 := by
    have h := hX.traceNorm_eq_trace
    rw [hXtr] at h
    exact Complex.ofReal_injective (by simpa using h)
  have hn : measurementSuccess M (tensorLeft T X) (tensorLeft S X)
      ≤ 1/2 + Matrix.traceNorm (tensorLeft T X - tensorLeft S X) / 4 := by
    exact measurementSuccess_le_half_add_quarter hM hMc hσ hΔ0
  have hle := Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_apply (T - S) r X
  rw [hXn, ENNReal.ofReal_one, mul_one] at hle
  have hδle : Matrix.traceNorm (tensorLeft T X - tensorLeft S X) ≤ δ := by
    rw [← Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_tensorLeft_map_sub]
    exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp (hle.trans hδ)
  linarith

noncomputable def binaryEffectPOVM {E : ℕ} (M : Operator E)
    (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef) : POVM Bool (Fin E) where
  mats b := if b then ⟨M, hM.1⟩ else ⟨1 - M, hMc.1⟩
  nonneg b := by
    cases b
    · exact HermitianMat.zero_le_iff.mpr hMc
    · exact HermitianMat.zero_le_iff.mpr hM
  normalized := by
    apply Subtype.ext
    simp [HermitianMat.mat_add, HermitianMat.mat_one]

noncomputable def discriminationLaw {E F : ℕ} (I : Instrument Bool E F)
    (ρ σ : Operator E) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    FinDist (Bool × Bool) where
  prob z := (1 / 2 : ℝ) * instrumentProb I (if z.1 then ρ else σ) z.2
  nonneg z := mul_nonneg (by norm_num)
    (instrumentProb_nonneg I (by cases z.1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact (by assumption : IsDensityOperator _).1) z.2)
  sum_one := by
    have hr := sum_instrumentProb_isDensityOperator I hρ
    have hs := sum_instrumentProb_isDensityOperator I hσ
    simp only [Fintype.sum_bool] at hr hs
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    linarith

theorem discriminationLaw_label {E F : ℕ} (I : Instrument Bool E F)
    (ρ σ : Operator E) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (b : Bool) :
    (∑ o, (discriminationLaw I ρ σ hρ hσ).prob (b, o)) = 1 / 2 := by
  change (∑ o, (1 / 2 : ℝ) * instrumentProb I (if b then ρ else σ) o) = _
  rw [← Finset.mul_sum, sum_instrumentProb_isDensityOperator I
    (show IsDensityOperator (if b then ρ else σ) by cases b <;> assumption), mul_one]

theorem discriminationLaw_success {E : ℕ} (M : Operator E)
    (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef)
    (ρ σ : Operator E) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    Qatlib.Concepts.ProbabilityCore.Concentration.eventMass
      (discriminationLaw (Instrument.ofPOVM (binaryEffectPOVM M hM hMc)) ρ σ hρ hσ)
      (fun z => z.1 = z.2) = measurementSuccess M ρ σ := by
  simp [Qatlib.Concepts.ProbabilityCore.Concentration.eventMass, discriminationLaw, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, instrumentProb_ofPOVM, binaryEffectPOVM,
    measurementSuccess, HermitianMat.mat_one, HermitianMat.mat_sub]
  ring

theorem discriminationLaw_success_le_diamond {D E : ℕ}
    (T S : QuantumChannel D E) (X : Operator D) (hX : IsDensityOperator X)
    (M : Operator E) (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : finiteDiamondNorm (T.map - S.map) ≤ ENNReal.ofReal δ) :
    Qatlib.Concepts.ProbabilityCore.Concentration.eventMass
      (discriminationLaw (Instrument.ofPOVM (binaryEffectPOVM M hM hMc)) (T.map X) (S.map X)
        ⟨T.completelyPositive.positive hX.1, (T.tracePreserving X).trans hX.2⟩
        ⟨S.completelyPositive.positive hX.1, (S.tracePreserving X).trans hX.2⟩)
      (fun z => z.1 = z.2) ≤ 1 / 2 + δ / 4 := by
  rw [discriminationLaw_success]
  have hρ : Matrix.trace (T.map X) = 1 := (T.tracePreserving X).trans hX.2
  have hσ : Matrix.trace (S.map X) = 1 := (S.tracePreserving X).trans hX.2
  have hzero : Matrix.trace (T.map X - S.map X) = 0 := by
    rw [Matrix.trace_sub, hρ, hσ, sub_self]
  have hs := measurementSuccess_le_half_add_quarter hM hMc hσ hzero
  have hXn : Matrix.traceNorm X = 1 := by
    have h := hX.1.traceNorm_eq_trace
    rw [hX.2] at h
    exact Complex.ofReal_injective (by simpa using h)
  have hn := finiteDiamondNorm_apply (T.map - S.map) 1
    (Matrix.reindex (Equiv.prodUnique (Fin D) (Fin 1)).symm
      (Equiv.prodUnique (Fin D) (Fin 1)).symm X)
  have hre : tensorLeft (T.map - S.map)
      (Matrix.reindex (Equiv.prodUnique (Fin D) (Fin 1)).symm
        (Equiv.prodUnique (Fin D) (Fin 1)).symm X)
      = Matrix.reindex (Equiv.prodUnique (Fin E) (Fin 1)).symm
        (Equiv.prodUnique (Fin E) (Fin 1)).symm (T.map X - S.map X) := by
    ext a b
    rfl
  rw [hre, diamond_traceNorm_reindex, diamond_traceNorm_reindex, hXn,
    ENNReal.ofReal_one, mul_one] at hn
  have hb := (ENNReal.ofReal_le_ofReal_iff hδ0).mp (hn.trans hδ)
  linarith

private theorem trace_relabel {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    using e.symm.sum_comp (fun i => A i i)

private theorem density_relabel {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (e : ι ≃ Fin K) (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A = 1) :
    IsDensityOperator (Matrix.reindex e e A) :=
  ⟨hA.submatrix e.symm, (trace_relabel e A).trans htr⟩

private theorem complement_relabel {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (e : ι ≃ Fin K) (M : Matrix ι ι ℂ) (hMc : (1 - M).PosSemidef) :
    (1 - Matrix.reindex e e M).PosSemidef := by
  have heq : (1 : Operator K) - Matrix.reindex e e M = Matrix.reindex e e (1 - M) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  rw [heq]
  exact hMc.submatrix e.symm

noncomputable def referenceDiscriminationLaw {D E r : ℕ}
    (T S : QuantumChannel D E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hX : X.PosSemidef) (hXtr : Matrix.trace X = 1)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ)
    (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef) : FinDist (Bool × Bool) :=
  let e : (Fin E × Fin r) ≃ Fin (E * r) := finProdFinEquiv
  discriminationLaw (Instrument.ofPOVM (binaryEffectPOVM
      (Matrix.reindex e e M) (hM.submatrix e.symm) (complement_relabel e M hMc)))
    (Matrix.reindex e e (tensorLeft T.map X)) (Matrix.reindex e e (tensorLeft S.map X))
    (density_relabel e _ (tensorLeft_posSemidef T.completelyPositive hX)
      (by rw [tensorLeft_trace_map T.map T.tracePreserving, hXtr]))
    (density_relabel e _ (tensorLeft_posSemidef S.completelyPositive hX)
      (by rw [tensorLeft_trace_map S.map S.tracePreserving, hXtr]))

theorem referenceDiscriminationLaw_success_le {D E r : ℕ}
    (T S : QuantumChannel D E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hX : X.PosSemidef) (hXtr : Matrix.trace X = 1)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ)
    (hM : M.PosSemidef) (hMc : (1 - M).PosSemidef)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : finiteDiamondNorm (T.map - S.map) ≤ ENNReal.ofReal δ) :
    Qatlib.Concepts.ProbabilityCore.Concentration.eventMass (referenceDiscriminationLaw T S X hX hXtr M hM hMc)
      (fun z => z.1 = z.2) ≤ 1 / 2 + δ / 4 := by
  unfold referenceDiscriminationLaw
  rw [discriminationLaw_success]
  let e : (Fin E × Fin r) ≃ Fin (E * r) := finProdFinEquiv
  have ht (C : QuantumChannel D E) :
      Matrix.trace (Matrix.reindex e e (tensorLeft C.map X)) = 1 := by
    rw [trace_relabel, tensorLeft_trace_map C.map C.tracePreserving, hXtr]
  have hz : Matrix.trace (Matrix.reindex e e (tensorLeft T.map X) -
      Matrix.reindex e e (tensorLeft S.map X)) = 0 := by
    rw [Matrix.trace_sub, ht T, ht S, sub_self]
  have hq := measurementSuccess_le_half_add_quarter (hM.submatrix e.symm)
    (complement_relabel e M hMc) (ht S) hz
  have heq : Matrix.reindex e e (tensorLeft T.map X) - Matrix.reindex e e (tensorLeft S.map X)
      = Matrix.reindex e e (tensorLeft (T.map - S.map) X) := by
    rw [diamond_tensorLeft_map_sub]
    rfl
  rw [heq, diamond_traceNorm_reindex] at hq
  have hn := finiteDiamondNorm_apply (T.map - S.map) r X
  have hXn : Matrix.traceNorm X = 1 := by
    have h := hX.traceNorm_eq_trace
    rw [hXtr] at h
    exact Complex.ofReal_injective (by simpa using h)
  rw [hXn, ENNReal.ofReal_one, mul_one] at hn
  have hb := (ENNReal.ofReal_le_ofReal_iff hδ0).mp (hn.trans hδ)
  exact hq.trans (by linarith)

end Qatlib.Concepts.SchattenDiamond.DiamondSdp
