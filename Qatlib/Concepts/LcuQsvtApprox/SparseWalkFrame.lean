/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared

/-!
# Polynomial synthesis and spectral walk frames

This module assembles completed-pair phase synthesis, repository-convention amplitude
approximation, and explicit walk frames for scaled Hermitian contractions.
`walk_frame_of_spectral` uses the defect square root `√(1 - T^2)` to build an involutory unitary
dilation, and sparsity bounds make this available for `LqSparseOracle`.

The sparse-walk consumers provide eigenvector decompositions and eigenvectorwise simulation
estimates with corrected truncation lengths. The constructions connect the signal-processing and
qubitization frameworks of [LowChuang2017] and [LowChuang2019]; the frame-existence statements
specify matrices without oracle implementation costs.

## Main statements

* `clause9_clause1b`: synthesize completed polynomial pairs with an operation bound.
* `clause9_clause2`: obtain amplitude, success-mass, and first-column error bounds.
* `walk_frame_of_spectral`: construct a walk frame for a scaled Hermitian contraction.
* `clause9_clause3` and `g9`: collect sparse-frame, eigenphase, and approximation results.

## References

* [Low and Chuang, 2017][LowChuang2017]
* [Low and Chuang, 2019][LowChuang2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.SparseSim
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix Polynomial
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SignalPrimitive.SparseSim

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared in
open Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame in
open Qatlib.Concepts.QueryWordCore.AdjointCircuits in
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing in
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in
open Qatlib.Concepts.NonNormalSpec.ResolventWord in
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis in
open Matrix Polynomial in
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared in
open Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame Qatlib.Concepts.QspSimulation.SparseWalk in
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel Qatlib.Concepts.SignalPrimitive.SparseSim in

/-- The repository amplitude definitions `lcRepoAmp` and `lqRepoAmpWord` coincide. -/
private theorem lcRepoAmp_eq_lqRepoAmpWord (γ₀ γ₁ : ℝ) (qs : List ℝ) (x : ℝ) :
    lcRepoAmp γ₀ γ₁ qs x = lqRepoAmpWord γ₀ γ₁ qs x :=
  rfl

/-- A polynomial pair has a length-`n` unit-phase response realization exactly when it satisfies
`Th3Pair n`. -/
theorem clause9_clause1a :
    (∀ (n : ℕ) (P Q : Polynomial ℂ),
      (∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
        zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q) ↔
      Th3Pair n P Q) := by
  intro n P Q
  exact (Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.completedPair_iff_response).symm

/-- Completed polynomial pairs are synthesized with the stated operation bound, phase validity,
list length, and exact response identities. -/
theorem clause9_clause1b :
    (∀ (n : ℕ) (P Q : Polynomial ℂ), Th3Pair n P Q →
      (lqSynthWithCount n P Q).1 = synthesizePair n P Q ∧
        (lqSynthWithCount n P Q).2 ≤ lqSynthOpCount n ∧
        (synthesizePair n P Q).2.length = n ∧
        IsPhase (synthesizePair n P Q).1 ∧
        (∀ z ∈ (synthesizePair n P Q).2, IsPhase z) ∧
        responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 = P ∧
        responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 = Q) := by
  intro n P Q h
  have h' : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q := h
  obtain ⟨hb, hzs, hp, hq⟩ :=
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.synthesizePair_correct h'
  exact ⟨rfl, lqSynthCount_le_of_completed n P Q h',
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.synthesizePair_length n P Q, hb, hzs, hp, hq⟩

/-- Under the even-degree, parity, boundedness, and endpoint hypotheses, constructs a repository
word whose amplitude equals `A(x) + i * √(1 - x^2) * Qt(x)`. -/
theorem clause9_clause1c :
    (∀ (d : ℕ) (A Qt : Polynomial ℝ), Even d → 0 < d →
      A.comp (-X) = A → Qt.comp (-X) = -Qt →
      A.degree ≤ (d : WithBot ℕ) → Qt.degree < (d : WithBot ℕ) →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) →
      A.eval 1 = 1 →
      ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = d ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          lqRepoAmpWord γ₀ γ₁ psis x =
            realEval A (Complex.ofReal x) +
              Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) *
                realEval Qt (Complex.ofReal x)) := by
  intro d A Qt hd hpos hA hQt hAdeg hQtdeg hineq hA1
  obtain ⟨γ₀, γ₁, psis, hlen, hamp⟩ :=
    achievableSufficiencyRestricted d A Qt hd hpos hA hQt hAdeg hQtdeg hineq hA1
  refine ⟨γ₀, γ₁, psis, hlen, ?_⟩
  intro x hx
  rw [← lcRepoAmp_eq_lqRepoAmpWord]
  exact hamp x hx

/-- The normalized Hadamard matrix is Hermitian. -/
private theorem lqHad_conjTranspose : lqHad.conjTranspose = lqHad := by
  ext i j
  simp only [lqHad, Matrix.conjTranspose_apply, Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

/-- The normalized Hadamard matrix squares to the identity. -/
private theorem lqHad_sq : lqHad * lqHad = 1 := by
  have hM : !![(1 : ℂ), 1; 1, -(1 : ℂ)] * !![(1 : ℂ), 1; 1, -(1 : ℂ)]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = ((2 : ℝ)⁻¹) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [lqHad, smul_mul_smul, hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h2, Complex.ofReal_inv, Complex.ofReal_ofNat]

/-- The normalized Hadamard matrix is unitary. -/
private theorem lqHad_unitary : lqHad ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, lqHad_conjTranspose]
  exact lqHad_sq

/-- A product fold of unitary matrices with a unitary initial accumulator remains unitary. -/
private theorem foldl_unitary : ∀ (l : List (Matrix (Fin 2) (Fin 2) ℂ))
    (a : Matrix (Fin 2) (Fin 2) ℂ), a ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    (∀ M ∈ l, M ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
    l.foldl (· * ·) a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro l
  induction l with
  | nil => intro a ha hl; exact ha
  | cons M rest ih =>
    intro a ha hl
    have hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := hl M (List.mem_cons_self)
    have hrest : ∀ M' ∈ rest, M' ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      fun M' h' => hl M' (List.mem_cons_of_mem M h')
    exact ih (a * M) (Submonoid.mul_mem _ ha hM) hrest

/-- The repository-convention word is unitary when `x` lies in `[-1, 1]`. -/
private theorem lqRepoWord_unitary (γ₀ γ₁ : ℝ) (qs : List ℝ) {x : ℝ}
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    lqRepoWord γ₀ γ₁ qs x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hsm : (SignalMatrix x).conjTranspose ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    have h : SignalMatrix x * star (SignalMatrix x) = 1 :=
      (Matrix.mem_unitaryGroup_iff).mp (signalMatrix_unitary hx1 hx2)
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rwa [Matrix.star_eq_conjTranspose] at h
  have hfold : ((qs.map fun q => (SignalMatrix x).conjTranspose * PhaseRotation q).foldl
      (· * ·) 1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    refine foldl_unitary _ 1 ?_ ?_
    · simp
    · intro M hM
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hM
      exact Submonoid.mul_mem _ hsm (phaseRotation_unitary q)
  simp only [lqRepoWord]
  have u0 : lqHad * PhaseRotation γ₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ lqHad_unitary (phaseRotation_unitary γ₀)
  have u1 : lqHad * PhaseRotation γ₀
        * (qs.map fun q => (SignalMatrix x).conjTranspose * PhaseRotation q).foldl (· * ·) 1
        ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ u0 hfold
  have u2 : lqHad * PhaseRotation γ₀
        * (qs.map fun q => (SignalMatrix x).conjTranspose * PhaseRotation q).foldl (· * ·) 1
        * (SignalMatrix x).conjTranspose
        ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ u1 hsm
  have u3 : lqHad * PhaseRotation γ₀
        * (qs.map fun q => (SignalMatrix x).conjTranspose * PhaseRotation q).foldl (· * ·) 1
        * (SignalMatrix x).conjTranspose * PhaseRotation γ₁
        ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ u2 (phaseRotation_unitary γ₁)
  exact Submonoid.mul_mem _ u3 lqHad_unitary

/-- The squared norms of the two entries in a unitary matrix's first column sum to one. -/
private theorem unitary_col_normSq (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Complex.normSq (U 0 0) + Complex.normSq (U 1 0) = 1 := by
  have h1 : (star U * U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
      ((Matrix.mem_unitaryGroup_iff').mp hU)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Fin.sum_univ_two] at h1
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h1
  have e0 : (Complex.normSq (U 0 0) : ℂ) = star (U 0 0) * U 0 0 := by
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  have e1 : (Complex.normSq (U 1 0) : ℂ) = star (U 1 0) * U 1 0 := by
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  rw [← e0, ← e1] at h1
  exact_mod_cast h1

/-- Under the stated polynomial approximation hypotheses, constructs a length-`N` repository
word with amplitude error at most `8 * ε`, success-mass lower bounds, and a first-column
error bound. -/
theorem clause9_clause2 :
    (∀ (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ),
      Even N → 0 < N →
      (∀ θ : ℝ, h (-θ) = -h θ) → (∀ θ : ℝ, h (θ + 2 * Real.pi) = h θ) →
      A.comp (-X) = A → Qt.comp (-X) = -Qt →
      A.degree ≤ (N : WithBot ℕ) → Qt.degree < (N : WithBot ℕ) →
      (0 < ε → ε ≤ 1 / 16 →
        (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
          ‖realEval A (Real.cos (θ / 2) : ℂ) +
              Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
                realEval Qt (Real.cos (θ / 2) : ℂ) -
              Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) →
        ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = N ∧
          ∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ‖lqRepoAmpWord γ₀ γ₁ psis x -
                Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ≤ 8 * ε ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ (1 - 8 * ε) ^ 2 ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ 1 - 16 * ε ∧
            Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0 -
                lqIdealOp h (2 * Real.arccos x) 0 0) +
              Complex.normSq (lqRepoWord γ₀ γ₁ psis x 1 0)
              ≤ (8 * ε + 4 * Real.sqrt ε) ^ 2)) := by
  intro N h A Qt ε hN hposN hodd hper hAeven hQtodd hAdeg hQtdeg hεpos hε16 happrox
  obtain ⟨γ₀, γ₁, psis, hlen, happ⟩ := qspCompilationRestricted N h A Qt ε hN hposN hodd hper
    hAeven hQtodd hAdeg hQtdeg hεpos hε16 happrox
  refine ⟨γ₀, γ₁, psis, hlen, ?_⟩
  intro x hx
  obtain ⟨hamp, hsucc, hsucc2⟩ := happ x hx
  have hamp1 : ‖lqRepoAmpWord γ₀ γ₁ psis x
      - Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ≤ 8 * ε := by
    rwa [lcRepoAmp_eq_lqRepoAmpWord] at hamp
  have hamp2 : (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
      + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
      ≥ (1 - 8 * ε) ^ 2 := by
    rwa [lcRepoAmp_eq_lqRepoAmpWord] at hsucc
  have hamp3 : (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
      + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
      ≥ 1 - 16 * ε := by
    rwa [lcRepoAmp_eq_lqRepoAmpWord] at hsucc2
  refine ⟨hamp1, hamp2, hamp3, ?_⟩

  have hU : lqRepoWord γ₀ γ₁ psis x ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    lqRepoWord_unitary γ₀ γ₁ psis hx.1 hx.2
  have hcol := unitary_col_normSq (lqRepoWord γ₀ γ₁ psis x) hU
  have h00 : lqRepoWord γ₀ γ₁ psis x 0 0 = lqRepoAmpWord γ₀ γ₁ psis x := rfl
  have hideal : lqIdealOp h (2 * Real.arccos x) 0 0
      = Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ)) := by
    simp [lqIdealOp, Matrix.diagonal_apply_eq]
  have hterm1 : Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0
      - lqIdealOp h (2 * Real.arccos x) 0 0) ≤ (8 * ε) ^ 2 := by
    rw [hideal, h00, Complex.normSq_eq_norm_sq]
    have hms := mul_self_le_mul_self (norm_nonneg _) hamp1
    have eL : ‖lqRepoAmpWord γ₀ γ₁ psis x
          - Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖
        * ‖lqRepoAmpWord γ₀ γ₁ psis x
          - Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖
        = ‖lqRepoAmpWord γ₀ γ₁ psis x
          - Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ^ 2 := (sq _).symm
    have eR : (8 * ε) * (8 * ε) = (8 * ε) ^ 2 := (sq _).symm
    rw [eL, eR] at hms
    exact hms
  have hterm2 : Complex.normSq (lqRepoWord γ₀ γ₁ psis x 1 0) ≤ 16 * ε := by
    have hnn : Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0)
        = (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
          + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im := by
      rw [h00]
      rfl
    have hsum : Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0)
        + Complex.normSq (lqRepoWord γ₀ γ₁ psis x 1 0) = 1 := hcol
    linarith
  have hsqε : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hεpos.le
  have hexp : (8 * ε + 4 * Real.sqrt ε) ^ 2
      = 64 * ε * ε + 64 * ε * Real.sqrt ε + 16 * ε := by
    calc (8 * ε + 4 * Real.sqrt ε) ^ 2
        = (8 * ε) ^ 2 + 2 * (8 * ε) * (4 * Real.sqrt ε) + (4 * Real.sqrt ε) ^ 2 := by ring
      _ = 64 * ε * ε + 64 * ε * Real.sqrt ε + 16 * (Real.sqrt ε * Real.sqrt ε) := by ring
      _ = 64 * ε * ε + 64 * ε * Real.sqrt ε + 16 * ε := by rw [hsqε]
  have h1 : Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0
      - lqIdealOp h (2 * Real.arccos x) 0 0) ≤ 64 * ε * ε := by
    have h8 : (8 * ε) ^ 2 = 64 * ε * ε := by ring
    linarith
  have hnn2 : 0 ≤ 64 * ε * Real.sqrt ε :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg ε)
  linarith

/-- Every row of the sparse oracle matrix has at most `d` nonzero entries. -/
private theorem lqSparse_row_card {n d : ℕ} {b : ℝ} (O : LqSparseOracle n d b) :
    ∀ o : Fin (2 ^ n), (Finset.univ.filter (fun i : Fin (2 ^ n) => O.H o i ≠ 0)).card ≤ d := by
  intro o
  have hsub : Finset.univ.filter (fun i : Fin (2 ^ n) => O.H o i ≠ 0)
      ⊆ ((O.entries o).map Prod.fst).toFinset := by
    intro i hi
    have hi' : O.H o i ≠ 0 := by
      simpa [Finset.mem_filter] using! hi
    have hmem : (i, O.H o i) ∈ O.entries o := O.entries_complete o i hi'
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨(i, O.H o i), hmem, rfl⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map]
  exact O.row_bound o

/-- Every column of the Hermitian sparse oracle matrix has at most `d` nonzero entries. -/
private theorem lqSparse_col_card {n d : ℕ} {b : ℝ} (O : LqSparseOracle n d b) :
    ∀ i : Fin (2 ^ n), (Finset.univ.filter (fun o : Fin (2 ^ n) => O.H o i ≠ 0)).card ≤ d := by
  intro i
  have hcong : ∀ o : Fin (2 ^ n), O.H o i = star (O.H i o) := by
    intro o
    have hEq : O.H.conjTranspose = O.H := O.hermitian
    have h := congrArg (fun M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ => M i o) hEq
    simp only [Matrix.conjTranspose_apply] at h
    have hs : star (star (O.H o i)) = star (O.H i o) := congrArg (fun z : ℂ => star z) h
    rw [star_star] at hs
    exact hs
  have hsub : Finset.univ.filter (fun o : Fin (2 ^ n) => O.H o i ≠ 0)
      ⊆ ((O.entries i).map Prod.fst).toFinset := by
    intro o ho
    have ho' : O.H o i ≠ 0 := by
      simpa [Finset.mem_filter] using! ho
    have hio : O.H i o ≠ 0 := by
      intro hh
      apply ho'
      rw [hcong, hh, star_zero]
    have hmem : (o, O.H i o) ∈ O.entries i := O.entries_complete i o hio
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨(o, O.H i o), hmem, rfl⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map]
  exact O.row_bound i

/-- For positive sparsity and entry bounds, scaling the sparse oracle matrix by `1 / (d * b)`
gives operator norm at most one. -/
private theorem lqSparse_scaled_opNorm_le_one {n d : ℕ} {b : ℝ}
    (O : LqSparseOracle n d b) (hd : 0 < d) (hb : 0 < b) :
    ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • O.H‖ ≤ 1 := by
  have hrow := lqSparse_row_card O
  have hcol := lqSparse_col_card O
  have hconsumer := sparse_overlap_derived_sparse_entry_norm_consumer
    (Fin (2 ^ n)) (Fin (2 ^ n)) O.H d b hb hd hrow hcol O.entry_bound
  have hnorm : ‖O.H‖ ≤ (d : ℝ) * b := hconsumer.2
  have hdb : (0 : ℝ) < (d : ℝ) * b := mul_pos (by exact_mod_cast hd) hb
  have hsmul : ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • O.H‖
      = ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ)‖ * ‖O.H‖ := norm_smul _ _
  rw [hsmul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdb)]
  rw [← div_eq_inv_mul]
  exact (div_le_one hdb).mpr hnorm

/-- Bounds the corrected truncation degree and twice its predecessor in terms of scaled time,
error tolerance, and logarithmic expressions. -/
theorem clause9_clause4 :
    (∀ (d : ℕ) (b t ε : ℝ), 0 < d → 0 < b → 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
      3 * (t * (d : ℝ) * b) ≤ (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          8 * (Real.log (32 / (ε / 8)) /
            Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) + 2) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          2 * (3 * (t * (d : ℝ) * b) + 3 * Real.log (32 / (ε / 8)) + 8)) := by
  intro d b t ε hd hb htpos hεpos hε12
  have hτ : 0 ≤ t * (d : ℝ) * b := by positivity
  have hε8 : 0 < ε / 8 := by positivity
  have hε81 : ε / 8 ≤ 1 := by
    have h : ε ≤ 1 / 2 := hε12
    have h2 : ε / 8 ≤ 1 / 16 := by linarith
    have h3 : (1 : ℝ) / 16 ≤ 1 := by norm_num
    linarith
  obtain ⟨hlo, hadd, hlog⟩ := lcCorrectedQ_bounds (t * (d : ℝ) * b) (ε / 8) hτ hε8 hε81
  refine ⟨hlo, ?_, ?_⟩
  · set r := Real.log (32 / (ε / 8))
      / Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) with hr
    have hlog' : (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ≤ 4 * (r + 2) := by
      rw [hr]
      exact hlog
    exact (by nlinarith :
      (2 : ℝ) * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤ 8 * (r + 2))
  · set L := Real.log (32 / (ε / 8)) with hL
    have hadd' : (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ)
        ≤ 3 * (t * (d : ℝ) * b) + 3 * L + 8 := by
      rw [hL]
      exact hadd
    exact (by nlinarith :
      (2 : ℝ) * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1)
        ≤ 2 * (3 * (t * (d : ℝ) * b) + 3 * L + 8))

/-- A supplied scaled sparse walk frame yields normalized walk eigenvectors with the stated
eigenphases and an eigenvectorwise simulation word with error at most `ε` and success mass
at least `1 - 2 * ε`. -/
theorem clause9_clause3_from_frame :
    ∀ (n d : ℕ) (b : ℝ), 0 < d → 0 < b → ∀ (O : LqSparseOracle n d b),
      ∀ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S →
        (∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
          ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
            ∃ (wp wm : Fin 2 × Fin (2 ^ n) → ℂ) (ap am : ℝ),
              (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
              (|((d : ℝ) * b)⁻¹ * ev| < 1 → (∑ j, star (wp j) * wm j = 0)) ∧
              (∃ V : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ,
                V ∈ Matrix.unitaryGroup _ ℂ ∧
                V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧
                V *ᵥ wp =
                  Complex.exp (Complex.I * ((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))) • wp ∧
                V *ᵥ wm =
                  -(Complex.exp (Complex.I * (-((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))))) • wm) ∧
              ((L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
                (Complex.exp (Complex.I * (ap : ℂ)) • wp +
                  Complex.exp (Complex.I * (am : ℂ)) • wm))) ∧
        (∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
          ∃ phis : List ℝ,
            phis.length = 2 * (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) - 1) ∧
            ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
              ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
                (∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i -
                    Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i‖ ^ 2) ≤ ε ^ 2 ∧
                1 - 2 * ε ≤ ∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i‖ ^ 2) := by
  intro n d b hd hb O L R S hframe
  have hc0 : (0 : ℝ) < ((d : ℝ) * b)⁻¹ :=
    inv_pos.mpr (mul_pos (by exact_mod_cast hd) hb)
  have hnorm : ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • O.H‖ ≤ 1 :=
    lqSparse_scaled_opNorm_le_one O hd hb
  have hrow := lqSparse_row_card O
  have hcol := lqSparse_col_card O
  obtain ⟨hL, hR, hLR, hSU, hSst, hSq, hSL⟩ := hframe
  have hG6 := sparseWalkEigenphasesRestricted (Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n))
    O.H (((d : ℝ) * b)⁻¹) hc0 hnorm L R S hL hR hLR hSU hSst hSq hSL
  have hG7 := sparseSimulationCorrectedRestricted (Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n))
    O.H d b O.hermitian hd hb hrow hcol O.entry_bound
    L R S hL hR hLR hSU hSst hSq hSL
  exact ⟨hG6, hG7⟩

open scoped ComplexOrder MatrixOrder

/-- The left walk frame embedding into the zero sector of a two-dimensional label register. -/
def lqWalkL {m : ℕ} : Matrix (Fin 2 × Fin m) (Fin m) ℂ :=
  Matrix.of fun w i => if w.1 = 0 ∧ w.2 = i then (1 : ℂ) else 0

/-- The right walk frame formed by stacking the matrices `T` and `N`. -/
def lqWalkR {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin 2 × Fin m) (Fin m) ℂ :=
  Matrix.of fun w i => if w.1 = 0 then T w.2 i else N w.2 i

/-- The block matrix with blocks `T`, `N`, `N`, and `-T`. -/
def lqWalkS {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Matrix.of fun w w' =>
    if w.1 = 0 ∧ w'.1 = 0 then T w.2 w'.2
    else if w.1 = 0 ∧ w'.1 = 1 then N w.2 w'.2
    else if w.1 = 1 ∧ w'.1 = 0 then N w.2 w'.2
    else -(T w.2 w'.2)

/-- The zero-sector left walk frame is an isometry. -/
theorem lqWalkL_isometry {m : ℕ} : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (lqWalkL (m := m)) := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, lqWalkL,
    Matrix.of_apply]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- For Hermitian `T` and `N` satisfying `N^2 = 1 - T^2`, the stacked right walk frame is an
isometry. -/
theorem lqWalkR_isometry {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hN : N.conjTranspose = N)
    (hNN : N * N = 1 - T * T) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (lqWalkR T N) := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, lqWalkR,
    Matrix.of_apply]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have e1 : (∑ x : Fin m, star (if (0 : Fin 2) = 0 then T x i else N x i)
      * (if (0 : Fin 2) = 0 then T x j else N x j))
      = (∑ x, star (T x i) * T x j) := by
    congr 1 with x
  have e2 : (∑ x : Fin m, star (if (1 : Fin 2) = 0 then T x i else N x i)
      * (if (1 : Fin 2) = 0 then T x j else N x j))
      = (∑ x, star (N x i) * N x j) := by
    congr 1 with x
  rw [e1, e2]
  have f1 : (∑ x, star (T x i) * T x j) = (T.conjTranspose * T) i j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have f2 : (∑ x, star (N x i) * N x j) = (N.conjTranspose * N) i j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [f1, f2, hT, hN, hNN]
  have hadd : (T * T + ((1 : Matrix (Fin m) (Fin m) ℂ) - T * T)) = 1 := by
    rw [add_comm, sub_add_cancel]
  rw [← Matrix.add_apply, hadd, Matrix.one_apply]

/-- The overlap of the left and right walk frames equals `T`. -/
theorem lqWalkL_dot_R {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) :
    (lqWalkL (m := m)).conjTranspose * lqWalkR T N = T := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    lqWalkL, lqWalkR]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have e1 : (∑ x : Fin m, star (if (0 : Fin 2) = 0 ∧ x = i then (1 : ℂ) else 0)
      * (if (0 : Fin 2) = 0 then T x j else N x j))
      = ∑ x, (if x = i then (1 : ℂ) else 0) * T x j := by
    congr 1 with x
    simp
  have e2 : (∑ x : Fin m, star (if (1 : Fin 2) = 0 ∧ x = i then (1 : ℂ) else 0)
      * (if (1 : Fin 2) = 0 then T x j else N x j)) = (0 : ℂ) := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp
  rw [e1]
  have hsum : (∑ x : Fin m, (if x = i then (1 : ℂ) else 0) * T x j) + (0 : ℂ)
      = ∑ x : Fin m, (if x = i then (1 : ℂ) else 0) * T x j := by
    rw [add_zero]
  have hfinal : (∑ x : Fin m, (if x = i then (1 : ℂ) else 0) * T x j) = T i j := by
    have h : ∀ x : Fin m, (if x = i then (1 : ℂ) else 0) * T x j
        = (if i = x then T x j else 0) := by
      intro x
      by_cases hx : x = i
      · simp [hx]
      · have : ¬ i = x := Ne.symm hx
        simp [hx, this]
    have hcong : (∑ x : Fin m, (if x = i then (1 : ℂ) else 0) * T x j)
        = ∑ x : Fin m, (if i = x then T x j else 0) :=
      Finset.sum_congr rfl fun x _ => h x
    rw [hcong, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  rw [e2, hsum, hfinal]

/-- The zero-zero block of `lqWalkS T N` is `T`. -/
theorem lqWalkS_apply_00 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) :
    lqWalkS T N (0, p) (0, q) = T p q := by simp [lqWalkS, Matrix.of_apply]

/-- The zero-one block of `lqWalkS T N` is `N`. -/
theorem lqWalkS_apply_01 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) :
    lqWalkS T N (0, p) (1, q) = N p q := by simp [lqWalkS, Matrix.of_apply]

/-- The one-zero block of `lqWalkS T N` is `N`. -/
theorem lqWalkS_apply_10 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) :
    lqWalkS T N (1, p) (0, q) = N p q := by simp [lqWalkS, Matrix.of_apply]

/-- The one-one block of `lqWalkS T N` is `-T`. -/
theorem lqWalkS_apply_11 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) :
    lqWalkS T N (1, p) (1, q) = -(T p q) := by simp [lqWalkS, Matrix.of_apply]

/-- The block walk matrix is Hermitian when `T` and `N` are Hermitian. -/
theorem lqWalkS_conjTranspose {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hN : N.conjTranspose = N) :
    (lqWalkS T N).conjTranspose = lqWalkS T N := by
  ext w w'
  obtain ⟨a, p⟩ := w
  obtain ⟨a', q⟩ := w'
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;>
    rcases ha' with rfl | rfl <;>
    simp only [Matrix.conjTranspose_apply, lqWalkS_apply_00, lqWalkS_apply_01,
      lqWalkS_apply_10, lqWalkS_apply_11]
  · have hs : star (T q p) = T p q := by rw [← Matrix.conjTranspose_apply, hT]
    exact hs
  · have hs : star (N q p) = N p q := by rw [← Matrix.conjTranspose_apply, hN]
    exact hs
  · have hs : star (N q p) = N p q := by rw [← Matrix.conjTranspose_apply, hN]
    exact hs
  · have hs : star (T q p) = T p q := by rw [← Matrix.conjTranspose_apply, hT]
    simp [hs]

/-- The block walk matrix squares to the identity when `N^2 = 1 - T^2` and `T` commutes with
`N`. -/
theorem lqWalkS_sq {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ)
    (_hT : T.conjTranspose = T) (_hN : N.conjTranspose = N)
    (hNN : N * N = 1 - T * T) (hTN : Commute T N) :
    lqWalkS T N * lqWalkS T N = 1 := by
  ext w w'
  obtain ⟨a, p⟩ := w
  obtain ⟨a', q⟩ := w'
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    simp only [Matrix.mul_apply, Matrix.one_apply]
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (0, p) (0, k) * lqWalkS T N (0, k) (0, q))
        = ∑ k, T p k * T k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_00]
    have e2 : (∑ k, lqWalkS T N (0, p) (1, k) * lqWalkS T N (1, k) (0, q))
        = ∑ k, N p k * N k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_01, lqWalkS_apply_10]
    rw [e1, e2]
    have f1 : (∑ k, T p k * T k q) = (T * T) p q := by rw [Matrix.mul_apply]
    have f2 : (∑ k, N p k * N k q) = (N * N) p q := by rw [Matrix.mul_apply]
    rw [f1, f2, hNN, ← Matrix.add_apply]
    have hadd : (T * T + ((1 : Matrix (Fin m) (Fin m) ℂ) - T * T)) = 1 := by
      rw [add_comm, sub_add_cancel]
    rw [hadd, Matrix.one_apply]
    by_cases hpq : p = q <;> simp [hpq]
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (0, p) (0, k) * lqWalkS T N (0, k) (1, q))
        = ∑ k, T p k * N k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_00, lqWalkS_apply_01]
    have e2 : (∑ k, lqWalkS T N (0, p) (1, k) * lqWalkS T N (1, k) (1, q))
        = -∑ k, N p k * T k q := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_01, lqWalkS_apply_11]
      ring
    rw [e1, e2]
    have f1 : (∑ k, T p k * N k q) = (T * N) p q := by rw [Matrix.mul_apply]
    have f2 : (∑ k, N p k * T k q) = (N * T) p q := by rw [Matrix.mul_apply]
    have hcomm : (T * N) p q = (N * T) p q :=
      congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M p q) hTN
    have h0 : (∑ k, T p k * N k q) - ∑ k, N p k * T k q = 0 := by
      rw [f1, f2, hcomm]; ring
    have h0' : (∑ k, T p k * N k q) + -∑ k, N p k * T k q = 0 := by
      rw [← sub_eq_add_neg]; exact h0
    rw [h0']
    simp
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (1, p) (0, k) * lqWalkS T N (0, k) (0, q))
        = ∑ k, N p k * T k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_10, lqWalkS_apply_00]
    have e2 : (∑ k, lqWalkS T N (1, p) (1, k) * lqWalkS T N (1, k) (0, q))
        = -∑ k, T p k * N k q := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_11, lqWalkS_apply_10]
      ring
    rw [e1, e2]
    have f1 : (∑ k, N p k * T k q) = (N * T) p q := by rw [Matrix.mul_apply]
    have f2 : (∑ k, T p k * N k q) = (T * N) p q := by rw [Matrix.mul_apply]
    have hcomm : (T * N) p q = (N * T) p q :=
      congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M p q) hTN
    have h0 : (∑ k, N p k * T k q) - ∑ k, T p k * N k q = 0 := by
      rw [f1, f2, hcomm]; ring
    have h0' : (∑ k, N p k * T k q) + -∑ k, T p k * N k q = 0 := by
      rw [← sub_eq_add_neg]; exact h0
    rw [h0']
    simp
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (1, p) (0, k) * lqWalkS T N (0, k) (1, q))
        = ∑ k, N p k * N k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_10, lqWalkS_apply_01]
    have e2 : (∑ k, lqWalkS T N (1, p) (1, k) * lqWalkS T N (1, k) (1, q))
        = ∑ k, T p k * T k q := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lqWalkS_apply_11]
      ring
    rw [e1, e2]
    have f1 : (∑ k, N p k * N k q) = (N * N) p q := by rw [Matrix.mul_apply]
    have f2 : (∑ k, T p k * T k q) = (T * T) p q := by rw [Matrix.mul_apply]
    rw [f2, f1, hNN, ← Matrix.add_apply]
    rw [sub_add_cancel, Matrix.one_apply]
    by_cases hpq : p = q <;> simp [hpq]

/-- The zero sector of the right walk frame is `T`. -/
theorem lqWalkR_apply_0 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p j : Fin m) :
    lqWalkR T N (0, p) j = T p j := by simp [lqWalkR, Matrix.of_apply]

/-- The one sector of the right walk frame is `N`. -/
theorem lqWalkR_apply_1 {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (p j : Fin m) :
    lqWalkR T N (1, p) j = N p j := by simp [lqWalkR, Matrix.of_apply]

/-- The block walk matrix sends the left walk frame to the right walk frame. -/
theorem lqWalkS_mul_L {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) :
    lqWalkS T N * lqWalkL = lqWalkR T N := by
  ext w j
  obtain ⟨a, p⟩ := w
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · show (∑ z : Fin 2 × Fin m, lqWalkS T N (0, p) z * lqWalkL z j) = T p j
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (0, p) (0, k) * lqWalkL ((0 : Fin 2), k) j)
        = T p j := by
      have h : ∀ k, lqWalkS T N (0, p) (0, k) * lqWalkL ((0 : Fin 2), k) j
          = T p k * (if k = j then (1 : ℂ) else 0) := by
        intro k
        simp [lqWalkS, lqWalkL, Matrix.of_apply]
      have hcong : (∑ k, lqWalkS T N (0, p) (0, k) * lqWalkL ((0 : Fin 2), k) j)
          = ∑ k, T p k * (if k = j then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun k _ => h k
      rw [hcong]
      have hite : ∀ k, T p k * (if k = j then (1 : ℂ) else 0)
          = (if j = k then T p k else 0) := by
        intro k
        by_cases hk : j = k
        · subst hk; simp
        · have hk' : ¬ (k = j) := fun e => hk e.symm
          simp [hk, hk']
      have hcong2 : (∑ k, T p k * (if k = j then (1 : ℂ) else 0))
          = ∑ k, (if j = k then T p k else 0) :=
        Finset.sum_congr rfl fun k _ => hite k
      rw [hcong2, Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
    have e2 : (∑ k, lqWalkS T N (0, p) (1, k) * lqWalkL ((1 : Fin 2), k) j) = (0 : ℂ) := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [lqWalkS, lqWalkL, Matrix.of_apply]
    rw [e1, e2, add_zero]
  · show (∑ z : Fin 2 × Fin m, lqWalkS T N (1, p) z * lqWalkL z j) = N p j
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have e1 : (∑ k, lqWalkS T N (1, p) (0, k) * lqWalkL ((0 : Fin 2), k) j) = N p j := by
      have h : ∀ k, lqWalkS T N (1, p) (0, k) * lqWalkL ((0 : Fin 2), k) j
          = N p k * (if k = j then (1 : ℂ) else 0) := by
        intro k
        simp [lqWalkS, lqWalkL, Matrix.of_apply]
      have hcong : (∑ k, lqWalkS T N (1, p) (0, k) * lqWalkL ((0 : Fin 2), k) j)
          = ∑ k, N p k * (if k = j then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun k _ => h k
      rw [hcong]
      have hite : ∀ k, N p k * (if k = j then (1 : ℂ) else 0)
          = (if j = k then N p k else 0) := by
        intro k
        by_cases hk : j = k
        · subst hk; simp
        · have hk' : ¬ (k = j) := fun e => hk e.symm
          simp [hk, hk']
      have hcong2 : (∑ k, N p k * (if k = j then (1 : ℂ) else 0))
          = ∑ k, (if j = k then N p k else 0) :=
        Finset.sum_congr rfl fun k _ => hite k
      rw [hcong2, Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
    have e2 : (∑ k, lqWalkS T N (1, p) (1, k) * lqWalkL ((1 : Fin 2), k) j) = (0 : ℂ) := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [lqWalkS, lqWalkL, Matrix.of_apply]
    rw [e1, e2, add_zero]

/-- The block walk matrix is unitary for commuting Hermitian `T` and `N` satisfying `N^2 = 1 -
T^2`. -/
theorem lqWalkS_unitary {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hN : N.conjTranspose = N)
    (hNN : N * N = 1 - T * T) (hTN : Commute T N) :
    lqWalkS T N ∈ Matrix.unitaryGroup (Fin 2 × Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, lqWalkS_conjTranspose T N hT hN]
  exact lqWalkS_sq T N hT hN hNN hTN

/-- A Hermitian matrix may be moved between the two arguments of the conjugate-linear
dot-product pairing. -/
theorem walkT_adjoint_dotProduct {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (x y : Fin m → ℂ) :
    star x ⬝ᵥ (T *ᵥ y) = star (T *ᵥ x) ⬝ᵥ y := by
  show ∑ i, star (x i) * (∑ j, T i j * y j)
      = ∑ j, star (∑ i, T j i * x i) * y j
  have hL : ∀ i, star (x i) * (∑ j, T i j * y j)
      = ∑ j, star (x i) * (T i j * y j) := fun i => Finset.mul_sum _ _ _
  have hR : ∀ j, star (∑ i, T j i * x i) * y j
      = ∑ i, star (T j i * x i) * y j := by
    intro j
    rw [star_sum, Finset.sum_mul]
  simp only [hL, hR, star_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hij : star (T j i) = T i j := by
    rw [← Matrix.conjTranspose_apply, hT]
  rw [hij]
  ring

/-- The conjugate self-dot-product is the complex cast of the sum of squared component norms. -/
theorem walkDotProduct_star_self {m : ℕ} (v : Fin m → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  show (∑ i, star (v i) * v i) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The Euclidean norm of a matrix-vector product is bounded by the operator norm times the
vector norm. -/
theorem walkOpNorm_mulVec {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) :
    ‖toEuclidean_fromVec (T *ᵥ x)‖ ≤ ‖T‖ * ‖toEuclidean_fromVec x‖ := by
  have h := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) T)
    (toEuclidean_fromVec x)
  have heq : ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) T)
      (toEuclidean_fromVec x) = toEuclidean_fromVec (T *ᵥ x) := by
    simp only [toEuclidean_fromVec]
    exact Matrix.toEuclideanCLM_toLp T x
  rw [heq] at h
  have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) T‖ = ‖T‖ := by
    symm
    exact l2OpNorm_eq_operatorSpectralNorm T
  rw [hnorm] at h
  exact h

/-- For a Hermitian contraction `T`, the defect matrix `1 - T^2` is positive semidefinite. -/
theorem walkP_posSemidef {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hnorm : ‖T‖ ≤ 1) :
    Matrix.PosSemidef (1 - T * T) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (n := Fin m) ?_ ?_
  · show (1 - T * T).conjTranspose = 1 - T * T
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hT]
  · intro x
    have hsplit : ((1 : Matrix (Fin m) (Fin m) ℂ) - T * T) *ᵥ x
        = x - (T * T) *ᵥ x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hprod : (T * T) *ᵥ x = T *ᵥ (T *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    have hdp : star x ⬝ᵥ ((1 - T * T) *ᵥ x)
        = star x ⬝ᵥ x - star x ⬝ᵥ ((T * T) *ᵥ x) := by
      rw [hsplit, dotProduct_sub]
    have hadj : star x ⬝ᵥ ((T * T) *ᵥ x) = star (T *ᵥ x) ⬝ᵥ (T *ᵥ x) := by
      rw [hprod, walkT_adjoint_dotProduct T hT]
    have hx : star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := walkDotProduct_star_self x
    have hTx : star (T *ᵥ x) ⬝ᵥ (T *ᵥ x)
        = ((∑ i, ‖(T *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := walkDotProduct_star_self _
    have hsum : ∑ i, ‖(T *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
      have h1 := norm_toEuclidean_fromVec_sq (T *ᵥ x)
      have h2 := norm_toEuclidean_fromVec_sq x
      have hop := walkOpNorm_mulVec T x
      have hsq : ‖toEuclidean_fromVec (T *ᵥ x)‖ ^ 2
          ≤ (‖T‖ * ‖toEuclidean_fromVec x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
      rw [mul_pow] at hsq
      have hsq2 : ‖T‖ ^ 2 * ‖toEuclidean_fromVec x‖ ^ 2
          ≤ 1 * ‖toEuclidean_fromVec x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hnorm) (sq_nonneg _)
      have h := hsq.trans hsq2
      linarith
    rw [hdp, hadj, hx, hTx, ← Complex.ofReal_sub, Complex.zero_le_real]
    exact sub_nonneg.mpr hsum

/-- For a Hermitian contraction, the functional-calculus square root of `1 - T^2` squares to `1
- T^2`. -/
theorem walkN_mul_self {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hnorm : ‖T‖ ≤ 1) :
    CFC.sqrt (1 - T * T) * CFC.sqrt (1 - T * T) = 1 - T * T := by
  have hP : Matrix.PosSemidef (1 - T * T) := walkP_posSemidef T hT hnorm
  exact CFC.sqrt_mul_sqrt_self _ hP.nonneg

/-- The functional-calculus square root of `1 - T^2` is Hermitian. -/
theorem walkN_conjTranspose {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ) :
    (CFC.sqrt (1 - T * T)).conjTranspose = CFC.sqrt (1 - T * T) := by
  have h : IsSelfAdjoint (CFC.sqrt (1 - T * T : Matrix (Fin m) (Fin m) ℂ)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [← Matrix.star_eq_conjTranspose]
  exact h

/-- A Hermitian contraction commutes with the functional-calculus square root of its defect
matrix. -/
theorem walkN_commute {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.conjTranspose = T) (hnorm : ‖T‖ ≤ 1) :
    Commute T (CFC.sqrt (1 - T * T)) := by
  have hP : Matrix.PosSemidef (1 - T * T) := walkP_posSemidef T hT hnorm
  have hP0 : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ 1 - T * T := hP.nonneg
  have hPT : Commute (1 - T * T) T := by
    show (1 - T * T) * T = T * (1 - T * T)
    rw [mul_sub, sub_mul, one_mul, mul_one, mul_assoc]
  have h : Commute (cfcₙ Real.sqrt (1 - T * T)) T := Commute.cfcₙ_real hPT _
  have h2 : Commute (CFC.sqrt (1 - T * T)) T := by
    rwa [← CFC.sqrt_eq_real_sqrt _ hP0] at h
  exact h2.symm

/-- Every real-scaled Hermitian contraction possesses a doubled-space walk frame with overlap
equal to the scaled matrix. -/
theorem walk_frame_of_spectral {m : ℕ} (c : ℝ) (H : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.conjTranspose = H) (hnorm : ‖((c : ℝ) : ℂ) • H‖ ≤ 1) :
    ∃ (L R : Matrix (Fin 2 × Fin m) (Fin m) ℂ)
      (S : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ),
      LqWalkFrame c H L R S := by
  set T : Matrix (Fin m) (Fin m) ℂ := ((c : ℝ) : ℂ) • H with hTdef
  have hT : T.conjTranspose = T := by
    rw [hTdef, Matrix.conjTranspose_smul]
    simp [Complex.conj_ofReal, hH]
  have hTnorm : ‖T‖ ≤ 1 := by rw [hTdef]; exact hnorm
  set N : Matrix (Fin m) (Fin m) ℂ := CFC.sqrt (1 - T * T) with hNdef
  have hNN : N * N = 1 - T * T := by
    rw [hNdef]; exact walkN_mul_self T hT hTnorm
  have hNherm : N.conjTranspose = N := by
    rw [hNdef]; exact walkN_conjTranspose T
  have hTN : Commute T N := by
    rw [hNdef]; exact walkN_commute T hT hTnorm
  refine ⟨lqWalkL, lqWalkR T N, lqWalkS T N, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lqWalkL_isometry
  · exact lqWalkR_isometry T N hT hNherm hNN
  · rw [← hTdef]; exact lqWalkL_dot_R T N
  · exact lqWalkS_unitary T N hT hNherm hNN hTN
  · exact lqWalkS_conjTranspose T N hT hNherm
  · exact lqWalkS_sq T N hT hNherm hNN hTN
  · exact lqWalkS_mul_L T N

/-- For positive sparse-oracle bounds, constructs a scaled walk frame with the stated walk
eigenphases, eigenvector decomposition, and eigenvectorwise simulation guarantees
[LowChuang2017]. -/
theorem clause9_clause3 :
    (∀ (n d : ℕ) (b : ℝ), 0 < d → 0 < b → ∀ O : LqSparseOracle n d b,
      ∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S ∧
        (∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
          ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
            ∃ (wp wm : Fin 2 × Fin (2 ^ n) → ℂ) (ap am : ℝ),
              (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
              (|((d : ℝ) * b)⁻¹ * ev| < 1 → (∑ j, star (wp j) * wm j = 0)) ∧
              (∃ V : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ,
                V ∈ Matrix.unitaryGroup _ ℂ ∧
                V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧
                V *ᵥ wp =
                  Complex.exp (Complex.I * ((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))) • wp ∧
                V *ᵥ wm =
                  -(Complex.exp (Complex.I * (-((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))))) • wm) ∧
              ((L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
                (Complex.exp (Complex.I * (ap : ℂ)) • wp +
                  Complex.exp (Complex.I * (am : ℂ)) • wm))) ∧
        (∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
          ∃ phis : List ℝ,
            phis.length = 2 * (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) - 1) ∧
            ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
              ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
                (∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i -
                    Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i‖ ^ 2) ≤ ε ^ 2 ∧
                1 - 2 * ε ≤ ∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i‖ ^ 2)) := by
  intro n d b hd hb O
  obtain ⟨L, R, S, hframe⟩ := walk_frame_of_spectral (((d : ℝ) * b)⁻¹ : ℝ) O.H
    O.hermitian (lqSparse_scaled_opNorm_le_one O hd hb)
  obtain ⟨h6, h7⟩ := clause9_clause3_from_frame n d b hd hb O L R S hframe
  exact ⟨L, R, S, hframe, h6, h7⟩

/-- Collects completed-pair characterization and synthesis, repository-word approximation,
sparse spectral walk-frame existence and eigenvectorwise simulation, and corrected
truncation-length bounds [LowChuang2017]. -/
theorem g9 :
    (∀ (n : ℕ) (P Q : Polynomial ℂ),
      (∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
        zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q) ↔
      Th3Pair n P Q)
  ∧ (∀ (n : ℕ) (P Q : Polynomial ℂ), Th3Pair n P Q →
      (lqSynthWithCount n P Q).1 = synthesizePair n P Q ∧
        (lqSynthWithCount n P Q).2 ≤ lqSynthOpCount n ∧
        (synthesizePair n P Q).2.length = n ∧
        IsPhase (synthesizePair n P Q).1 ∧
        (∀ z ∈ (synthesizePair n P Q).2, IsPhase z) ∧
        responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 = P ∧
        responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 = Q)
  ∧ (∀ (d : ℕ) (A Qt : Polynomial ℝ), Even d → 0 < d →
      A.comp (-X) = A → Qt.comp (-X) = -Qt →
      A.degree ≤ (d : WithBot ℕ) → Qt.degree < (d : WithBot ℕ) →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) →
      A.eval 1 = 1 →
      ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = d ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          lqRepoAmpWord γ₀ γ₁ psis x =
            realEval A (Complex.ofReal x) +
              Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) *
                realEval Qt (Complex.ofReal x))
  ∧ (∀ (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ),
      Even N → 0 < N →
      (∀ θ : ℝ, h (-θ) = -h θ) → (∀ θ : ℝ, h (θ + 2 * Real.pi) = h θ) →
      A.comp (-X) = A → Qt.comp (-X) = -Qt →
      A.degree ≤ (N : WithBot ℕ) → Qt.degree < (N : WithBot ℕ) →
      (0 < ε → ε ≤ 1 / 16 →
        (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
          ‖realEval A (Real.cos (θ / 2) : ℂ) +
              Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
                realEval Qt (Real.cos (θ / 2) : ℂ) -
              Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) →
        ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = N ∧
          ∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ‖lqRepoAmpWord γ₀ γ₁ psis x -
                Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ≤ 8 * ε ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ (1 - 8 * ε) ^ 2 ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ 1 - 16 * ε ∧
            Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0 -
                lqIdealOp h (2 * Real.arccos x) 0 0) +
              Complex.normSq (lqRepoWord γ₀ γ₁ psis x 1 0)
              ≤ (8 * ε + 4 * Real.sqrt ε) ^ 2))
  ∧ (∀ (n d : ℕ) (b : ℝ), 0 < d → 0 < b → ∀ O : LqSparseOracle n d b,
      ∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S ∧
        (∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
          ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
            ∃ (wp wm : Fin 2 × Fin (2 ^ n) → ℂ) (ap am : ℝ),
              (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
              (|((d : ℝ) * b)⁻¹ * ev| < 1 → (∑ j, star (wp j) * wm j = 0)) ∧
              (∃ V : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ,
                V ∈ Matrix.unitaryGroup _ ℂ ∧
                V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧
                V *ᵥ wp =
                  Complex.exp (Complex.I * ((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))) • wp ∧
                V *ᵥ wm =
                  -(Complex.exp (Complex.I * (-((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))))) • wm) ∧
              ((L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
                (Complex.exp (Complex.I * (ap : ℂ)) • wp +
                  Complex.exp (Complex.I * (am : ℂ)) • wm))) ∧
        (∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
          ∃ phis : List ℝ,
            phis.length = 2 * (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) - 1) ∧
            ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
              ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
                (∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i -
                    Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i‖ ^ 2) ≤ ε ^ 2 ∧
                1 - 2 * ε ≤ ∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i‖ ^ 2))
  ∧ (∀ (d : ℕ) (b t ε : ℝ), 0 < d → 0 < b → 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
      3 * (t * (d : ℝ) * b) ≤ (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          8 * (Real.log (32 / (ε / 8)) /
            Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) + 2) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          2 * (3 * (t * (d : ℝ) * b) + 3 * Real.log (32 / (ε / 8)) + 8)) :=
  ⟨clause9_clause1a, clause9_clause1b, clause9_clause1c, clause9_clause2, clause9_clause3, clause9_clause4⟩
end Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame
