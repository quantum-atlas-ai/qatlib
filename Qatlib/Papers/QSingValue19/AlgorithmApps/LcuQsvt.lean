/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSingValue19.AlgorithmApps.LcuQsvtDefs
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtModulusTransport
import Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Papers.HamLCUSim12.Multiproduct
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Transport
open Qatlib.Concepts.QsvtCore.HamiltonianSim
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Qatlib
open scoped BigOperators Classical Matrix.Norms.L2Operator
set_option warningAsError false

section G1

theorem quasicommutatorConstant_pos : 0 < quasicommutatorConstant := by
  unfold quasicommutatorConstant
  norm_num

private theorem schurBound_frozen_constant :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis.lipUnion eigL eigR f L →
      ∀ K : Matrix I J ℂ,
        ‖(Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis.ddMat eigL eigR f).hadamard K‖ ≤
          quasicommutatorConstant * (1 + Real.log ((Finset.univ.image eigL).card : ℝ)) * L * ‖K‖ := by
  intro I J _ _ _ _ eigL eigR f L hL hf K
  refine Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis.schurBound_of_weakSchatten
    (c₁ := quasicommutatorConstant) quasicommutatorConstant_pos ?_ I J eigL eigR f L hL hf K
  intro J I _ _ _ _ μ ν f L hL hf a b q
  exact Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition.ddMat_hadamard_vecMulVec_sv_bound hL hf a b q

theorem clause1_quasicommutator_constant :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
      (S : Matrix I J ℂ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      hermitianPairScalarLipschitz A hA B hB f L →
      ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ ≤
        quasicommutatorConstant * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖ := by
  intro I J _ _ _ _ A hA B hB S f L hL hf
  let UA := basisColumns (orderedHermitianBasis hA)
  let UB := basisColumns (orderedHermitianBasis hB)
  have hcoord :=
    Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Transport.coordinates_quasicommutator_eq_ddMat_hadamard
      A hA B hB S f
  have hK : ‖Matrix.conjTranspose UA * (A * S - S * B) * UB‖ = ‖A * S - S * B‖ :=
    hermitian_pair_coordinates_norm A hA B hB (A * S - S * B)
  have hX : ‖Matrix.conjTranspose UA * (hermitianFunction A hA f * S - S * hermitianFunction B hB f) * UB‖ =
      ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ :=
    hermitian_pair_coordinates_norm A hA B hB _
  have hmain := schurBound_frozen_constant (Fin (Fintype.card I)) (Fin (Fintype.card J))
    (orderedHermitianValues hA) (orderedHermitianValues hB) f L hL
    (Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Transport.lipUnion_of_hermitianPairScalarLipschitz hf)
    (Matrix.conjTranspose UA * (A * S - S * B) * UB)
  rw [← hX, hcoord]
  calc
    ‖(Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis.ddMat (orderedHermitianValues hA)
        (orderedHermitianValues hB) f).hadamard (Matrix.conjTranspose UA * (A * S - S * B) * UB)‖
        ≤ quasicommutatorConstant * (1 + Real.log ((Finset.univ.image
          (orderedHermitianValues hA)).card : ℝ)) * L * ‖Matrix.conjTranspose UA * (A * S - S * B) * UB‖ := hmain
    _ ≤ quasicommutatorConstant * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖ := by
        rw [hK]
        have hlog := orderedHermitian_log_spectrum_card_le A hA
        have h0 : 0 ≤ quasicommutatorConstant * L * ‖A * S - S * B‖ :=
          mul_nonneg (mul_nonneg quasicommutatorConstant_pos.le hL) (norm_nonneg _)
        calc quasicommutatorConstant * (1 + Real.log ((Finset.univ.image
                (orderedHermitianValues hA)).card : ℝ)) * L * ‖A * S - S * B‖
            = (quasicommutatorConstant * L * ‖A * S - S * B‖) * (1 + Real.log
                ((Finset.univ.image (orderedHermitianValues hA)).card : ℝ)) := by ring
          _ ≤ (quasicommutatorConstant * L * ‖A * S - S * B‖) * hermitianRankLogWeight A.rank :=
              mul_le_mul_of_nonneg_left hlog h0
          _ = quasicommutatorConstant * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖ := by ring

theorem clause1_operator_stability_constant :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (L : ℝ),
      0 ≤ L → hermitianPairScalarLipschitz A hA B hB f L →
      ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
        quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ :=
  hermitianFunction_min_rank_stability_of_quasicommutator_bound quasicommutatorConstant
    (fun I _ _ A hA B hB S f L hL hf =>
      clause1_quasicommutator_constant I I A hA B hB S f L hL hf)

theorem clause1_hermitian_function_printed {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hadeq : printedRobustnessAdequacy ‖A - B‖ (min A.rank B.rank)) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hδne : ‖A - B‖ ≠ 0 := ne_of_gt hδpos
  have hωδ : 0 ≤ ω ‖A - B‖ :=
    Qatlib.Concepts.QsvtCore.ApproxToolkit.modulus_nonneg hω (norm_nonneg _)
  have hL : 0 ≤ ω ‖A - B‖ / ‖A - B‖ := div_nonneg hωδ (le_of_lt hδpos)
  have hpair :=
    Qatlib.Concepts.QsvtCore.ApproxToolkit.linearSweep_pair_lipschitz
      A B hA hB f ω hω hδpos
  have hstab := clause1_operator_stability_constant I A B hA hB
    (linearSweep ‖A - B‖ (clampResponse f)) (ω ‖A - B‖ / ‖A - B‖) hL hpair
  have hmid : ‖hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
      hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f))‖ ≤
        quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖ := by
    have h1 : (ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖ = ω ‖A - B‖ := by
      rw [div_mul_cancel₀ _ hδne]
    calc
      _ ≤ quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) *
          (ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖ := hstab
      _ = quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) *
          ((ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖) := by ring
      _ = quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖ := by
        rw [h1]
  have h3 := Qatlib.Concepts.QsvtCore.ApproxToolkit.modulus_main_of_middle
    A B hA hB hA1 hB1 f ω hω hδpos
    (quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖) hmid
  have h3' : ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      (2 + quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖ := by
    have hsum : 2 * ω ‖A - B‖ + (quasicommutatorConstant * hermitianRankLogWeight
        (min A.rank B.rank) * ω ‖A - B‖) =
        (2 + quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖ := by
      ring
    exact h3.trans (le_of_eq hsum)
  unfold printedRobustnessAdequacy at hadeq
  have hmul : (2 + quasicommutatorConstant * hermitianRankLogWeight (min A.rank B.rank)) *
      ω ‖A - B‖ ≤ modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ :=
    mul_le_mul_of_nonneg_right hadeq hωδ
  exact h3'.trans hmul

theorem clause1_odd_printed_robustness {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hodd : IsOddFunction f)
    (hadeq : printedRobustnessAdequacy ‖A - B‖
      (min (hermitianDilation A).rank (hermitianDilation B).rank)) :
    ‖oddSingularTransform A f - oddSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have h12A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f).toBlocks₁₂
      = oddSingularTransform A f := by
    rw [Qatlib.Concepts.QsvtCore.ApproxToolkit.hermitianDilation_odd_fromBlocks A f hodd]
    simp
  have h12B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f).toBlocks₁₂
      = oddSingularTransform B f := by
    rw [Qatlib.Concepts.QsvtCore.ApproxToolkit.hermitianDilation_odd_fromBlocks B f hodd]
    simp
  rw [← h12A, ← h12B]
  have hle := dilation_block12_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f)
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f)
  have hnormA : ‖hermitianDilation A‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hA1
  have hnormB : ‖hermitianDilation B‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hB1
  have hδ' : 0 < ‖hermitianDilation A - hermitianDilation B‖ := by
    rw [hermitianDilation_sub_norm]; exact hδpos
  have hth := clause1_hermitian_function_printed (A := hermitianDilation A) (B := hermitianDilation B)
    (hA := hermitianDilation_adjoint A) (hB := hermitianDilation_adjoint B) f ω
    hnormA hnormB hω hδ' (by rwa [hermitianDilation_sub_norm])
  rw [hermitianDilation_sub_norm] at hth
  exact hle.trans hth

theorem clause1_even_printed_robustness {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (heven : IsEvenFunction f)
    (hadeq : printedRobustnessAdequacy ‖A - B‖
      (min (hermitianDilation A).rank (hermitianDilation B).rank)) :
    ‖rightSingularTransform A f - rightSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have h22A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f).toBlocks₂₂
      = rightSingularTransform A f := by
    rw [Qatlib.Concepts.QsvtCore.ApproxToolkit.hermitianDilation_even_fromBlocks A f heven]
    simp
  have h22B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f).toBlocks₂₂
      = rightSingularTransform B f := by
    rw [Qatlib.Concepts.QsvtCore.ApproxToolkit.hermitianDilation_even_fromBlocks B f heven]
    simp
  rw [← h22A, ← h22B]
  have hle := dilation_block22_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f)
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f)
  have hnormA : ‖hermitianDilation A‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hA1
  have hnormB : ‖hermitianDilation B‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hB1
  have hδ' : 0 < ‖hermitianDilation A - hermitianDilation B‖ := by
    rw [hermitianDilation_sub_norm]; exact hδpos
  have hth := clause1_hermitian_function_printed (A := hermitianDilation A) (B := hermitianDilation B)
    (hA := hermitianDilation_adjoint A) (hB := hermitianDilation_adjoint B) f ω
    hnormA hnormB hω hδ' (by rwa [hermitianDilation_sub_norm])
  rw [hermitianDilation_sub_norm] at hth
  exact hle.trans hth

theorem clause1_equality_at_zero : SvtEqualityAtZero := by
  intro I O _ _ _ _ A B f hδ
  exact Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.singularTransforms_eq_of_norm_sub_zero A B f hδ

theorem printedRobustnessThreshold_pos (r : ℕ) : 0 < printedRobustnessThreshold r := by
  have h0 : (0:ℝ) < 7 + 2 * (r : ℝ) := by positivity
  have h1 : (1:ℝ) < Real.exp (7 + 2 * (r : ℝ)) := by
    have h := Real.exp_lt_exp.mpr h0
    simpa using! h
  have h2 : (0:ℝ) < Real.exp (7 + 2 * (r : ℝ)) - 1 := by linarith
  unfold printedRobustnessThreshold
  exact div_pos (by norm_num) h2

theorem clause1_printed_robustness_threshold (r : ℕ) :
    printedRobustnessAdequacy (printedRobustnessThreshold r) r := by
  have hexp : (1:ℝ) < Real.exp (7 + 2 * r) := by
    have h0 : (0:ℝ) < 7 + 2 * r := by positivity
    have h := Real.exp_lt_exp.mpr h0
    simpa using! h
  have hkey : 2 / printedRobustnessThreshold r + 1 = Real.exp (7 + 2 * r) := by
    unfold printedRobustnessThreshold
    field_simp
    ring
  have hlog : Real.log (2 / printedRobustnessThreshold r + 1) = 7 + 2 * r := by
    rw [hkey, Real.log_exp]
  have h2r : (7 + 2 * r : ℝ) + 1 = 2 * ((r : ℝ) + 4) := by
    ring
  have hfac : modulusRobustnessFactor (printedRobustnessThreshold r) =
      16 * ((r : ℝ) + 4) ^ 2 := by
    unfold modulusRobustnessFactor
    rw [hlog, h2r]
    ring
  have hlog1r : Real.log (1 + (r : ℝ)) ≤ (r : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + (r : ℝ))
    linarith
  have hw : hermitianRankLogWeight r = 1 + Real.log (1 + (r : ℝ)) := rfl
  have hbound : (2 + quasicommutatorConstant * (1 + Real.log (1 + (r : ℝ)))) ≤
      16 * ((r : ℝ) + 4) ^ 2 := by
    have hq : 0 ≤ quasicommutatorConstant := quasicommutatorConstant_pos.le
    have hmul := mul_le_mul_of_nonneg_left hlog1r hq
    have h1 : (2 + quasicommutatorConstant * (1 + Real.log (1 + (r : ℝ))))
        ≤ 2 + quasicommutatorConstant * (1 + (r : ℝ)) := by linarith
    have hr : (0:ℝ) ≤ (r : ℝ) := by positivity
    have hsq : 0 ≤ ((r : ℝ) - 1 / 2) ^ 2 := sq_nonneg _
    have h2 : 2 + quasicommutatorConstant * (1 + (r : ℝ)) ≤ 16 * ((r : ℝ) + 4) ^ 2 := by
      unfold quasicommutatorConstant
      nlinarith
    linarith
  unfold printedRobustnessAdequacy
  rw [hw, hfac]
  exact hbound

theorem clause1_printed_factor_dominates (r : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδr : δ ≤ printedRobustnessThreshold r) :
    2 + quasicommutatorConstant * hermitianRankLogWeight r ≤ modulusRobustnessFactor δ := by
  have hexp : 1 < Real.exp (7 + 2 * (r : ℝ)) := by
    have h0 : (0:ℝ) < 7 + 2 * (r : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr h0
    simpa using! h
  have hE : 0 < Real.exp (7 + 2 * (r : ℝ)) - 1 := by linarith
  have hthr : printedRobustnessThreshold r = 2 / (Real.exp (7 + 2 * (r : ℝ)) - 1) := by
    unfold printedRobustnessThreshold
    norm_num
  have hδr' : δ ≤ 2 / (Real.exp (7 + 2 * (r : ℝ)) - 1) := by rwa [hthr] at hδr
  have hmul : δ * (Real.exp (7 + 2 * (r : ℝ)) - 1) ≤ 2 := (le_div_iff₀ hE).mp hδr'
  have hinv : Real.exp (7 + 2 * (r : ℝ)) - 1 ≤ 2 / δ :=
    (le_div_iff₀ hδ).mpr (by linarith [hmul])
  have harg : 0 < 2 / δ + 1 := by positivity
  have hle : Real.exp (7 + 2 * (r : ℝ)) ≤ 2 / δ + 1 := by linarith
  have hlog : 7 + 2 * (r : ℝ) ≤ Real.log (2 / δ + 1) := by
    by_contra hcon
    have hlt : Real.log (2 / δ + 1) < 7 + 2 * (r : ℝ) := lt_of_not_ge hcon
    have h2 : 2 / δ + 1 ≤ Real.exp (7 + 2 * (r : ℝ)) :=
      (Real.log_le_iff_le_exp harg).mp (le_of_lt hlt)
    have heq : 2 / δ + 1 = Real.exp (7 + 2 * (r : ℝ)) := le_antisymm h2 hle
    rw [heq, Real.log_exp] at hlt
    linarith
  have hlog0 : 0 ≤ Real.log (2 / δ + 1) + 1 := by
    have hgt : 1 < 2 / δ + 1 := by linarith
    have h := Real.log_pos hgt
    linarith
  have hsq : (7 + 2 * (r : ℝ) + 1) ^ 2 ≤ (Real.log (2 / δ + 1) + 1) ^ 2 := by
    have hbase : 0 ≤ 7 + 2 * (r : ℝ) + 1 := by positivity
    exact (sq_le_sq₀ hbase hlog0).mpr (by linarith)
  have hpoly : 16 * ((r : ℝ) + 4) ^ 2 ≤ 4 * (Real.log (2 / δ + 1) + 1) ^ 2 := by
    have heq : 4 * (7 + 2 * (r : ℝ) + 1) ^ 2 = 16 * ((r : ℝ) + 4) ^ 2 := by ring
    linarith [hsq]
  have hlogle : Real.log (1 + (r : ℝ)) ≤ r := by
    have hpos : 0 < 1 + (r : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hright : 2 + 144 * (1 + Real.log (1 + (r : ℝ)))
      ≤ 146 + 144 * (r : ℝ) := by
    have hr : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [mul_le_mul_of_nonneg_left hlogle (by norm_num : (0:ℝ) ≤ 144)]
  have hquad : 0 ≤ 16 * (r : ℝ) ^ 2 - 16 * (r : ℝ) + 110 := by
    nlinarith [sq_nonneg ((r : ℝ) - 1 / 2)]
  have hfinal : 146 + 144 * (r : ℝ) ≤ 16 * ((r : ℝ) + 4) ^ 2 := by
    have hr : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [hquad]
  unfold hermitianRankLogWeight quasicommutatorConstant modulusRobustnessFactor
  linarith [hpoly, hright, hfinal]

theorem clause1_printed_adequacy_in_range (r : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδr : δ ≤ printedRobustnessThreshold r) :
    printedRobustnessAdequacy δ r :=
  clause1_printed_factor_dominates r δ hδ hδr

theorem clause1_odd_printed_robustness_range {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hodd : IsOddFunction f)
    (hδr : ‖A - B‖ ≤ printedRobustnessThreshold
      (min (hermitianDilation A).rank (hermitianDilation B).rank)) :
    ‖oddSingularTransform A f - oddSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hadeq := clause1_printed_adequacy_in_range
    (min (hermitianDilation A).rank (hermitianDilation B).rank) ‖A - B‖ hδpos hδr
  exact clause1_odd_printed_robustness A B f ω hA1 hB1 hω hδpos hodd hadeq

theorem clause1_even_printed_robustness_range {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (heven : IsEvenFunction f)
    (hδr : ‖A - B‖ ≤ printedRobustnessThreshold
      (min (hermitianDilation A).rank (hermitianDilation B).rank)) :
    ‖rightSingularTransform A f - rightSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hadeq := clause1_printed_adequacy_in_range
    (min (hermitianDilation A).rank (hermitianDilation B).rank) ‖A - B‖ hδpos hδr
  exact clause1_even_printed_robustness A B f ω hA1 hB1 hω hδpos heven hadeq

theorem clause1_endpoint :
    SvtRobustnessBound ∧ SvtEqualityAtZero ∧
      (∀ (r : ℕ), printedRobustnessAdequacy (printedRobustnessThreshold r) r) ∧
      (∀ (r : ℕ) (δ : ℝ), 0 < δ → δ ≤ printedRobustnessThreshold r →
        printedRobustnessAdequacy δ r) := by
  refine ⟨?_, clause1_equality_at_zero, fun r => clause1_printed_robustness_threshold r, ?_⟩
  · intro I O _ _ _ _ A B f ω hA1 hB1 hω hδpos
    constructor
    · intro hodd hadeq
      exact clause1_odd_printed_robustness A B f ω hA1 hB1 hω hδpos hodd hadeq
    · intro heven hadeq
      exact clause1_even_printed_robustness A B f ω hA1 hB1 hω hδpos heven hadeq
  · intro r δ hδ hδr
    exact clause1_printed_adequacy_in_range r δ hδ hδr

theorem clause2_zero_degree_rates (δ : ℝ) (m : ℝ) :
    zeroDegreeBridgeRate δ = 0 ∧ zeroDegreeInteriorRate m δ = 0 := by
  constructor
  · simp only [zeroDegreeBridgeRate, polynomialRobustnessBound]
    ring
  · simp only [zeroDegreeInteriorRate, interiorRobustnessRate]
    ring

theorem clause2_bridge_rate_homogeneous (n : ℕ) (δ : ℝ) :
    polynomialRobustnessBound n δ = (n : ℝ) * polynomialRobustnessBound 1 δ := by
  simp only [polynomialRobustnessBound]
  ring

theorem clause2_interior_rate_homogeneous (n : ℕ) (m δ : ℝ) :
    interiorRobustnessRate n m δ = (n : ℝ) * interiorRobustnessRate 1 m δ := by
  simp only [interiorRobustnessRate]
  ring

theorem clause2_bridge_rate_mono (n n' : ℕ) (δ : ℝ) (h : n ≤ n') :
    polynomialRobustnessBound n δ ≤ polynomialRobustnessBound n' δ := by
  have h1 : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast h
  have hsq : 0 ≤ 4 * Real.sqrt δ := by positivity
  have hmul : 4 * Real.sqrt δ * (n : ℝ) ≤ 4 * Real.sqrt δ * (n' : ℝ) :=
    mul_le_mul_of_nonneg_left h1 hsq
  unfold polynomialRobustnessBound
  linarith [hmul]

theorem clause2_interior_rate_mono (n n' : ℕ) (m δ : ℝ) (hδ : 0 ≤ δ) (h : n ≤ n') :
    interiorRobustnessRate n m δ ≤ interiorRobustnessRate n' m δ := by
  have h1 : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast h
  have hsq : 0 ≤ Real.sqrt (2 / (1 - m ^ 2)) := Real.sqrt_nonneg _
  have hnonneg : 0 ≤ Real.sqrt (2 / (1 - m ^ 2)) * δ := mul_nonneg hsq hδ
  have hmul : Real.sqrt (2 / (1 - m ^ 2)) * δ * (n : ℝ)
      ≤ Real.sqrt (2 / (1 - m ^ 2)) * δ * (n' : ℝ) :=
    mul_le_mul_of_nonneg_left h1 hnonneg
  unfold interiorRobustnessRate
  linarith [hmul]

theorem clause2_interior_rate_at_boundary (n : ℕ) (δ : ℝ) :
    interiorRobustnessRate n 1 δ = 0 := by
  simp only [interiorRobustnessRate]
  ring

theorem clause2_bridge_rate_nonneg (n : ℕ) (δ : ℝ) :
    0 ≤ polynomialRobustnessBound n δ := by
  unfold polynomialRobustnessBound
  have h1 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2

theorem clause2_interior_rate_nonneg (n : ℕ) (m : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ interiorRobustnessRate n m δ := by
  unfold interiorRobustnessRate
  have h1 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : 0 ≤ Real.sqrt (2 / (1 - m ^ 2)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (2 / (1 - m ^ 2)) * δ := mul_nonneg h2 hδ
  exact mul_nonneg (mul_nonneg h1 h2) hδ

theorem clause2_endpoint :
    Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma23PolynomialLevel ∧
      Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23InteriorRobustness ∧
      (∀ δ m : ℝ, zeroDegreeBridgeRate δ = 0 ∧ zeroDegreeInteriorRate m δ = 0) ∧
      (∀ (n : ℕ) (δ : ℝ),
        polynomialRobustnessBound n δ = (n : ℝ) * polynomialRobustnessBound 1 δ) ∧
      (∀ (n : ℕ) (m δ : ℝ),
        interiorRobustnessRate n m δ = (n : ℝ) * interiorRobustnessRate 1 m δ) := by
  refine ⟨Qatlib.Concepts.QsvtCore.QsVtStability.lemma23PolynomialLevel,
    Qatlib.Concepts.QsvtCore.QsVtStability.lemma23InteriorRobustness, ?_, ?_, ?_⟩
  · intro δ m
    exact clause2_zero_degree_rates δ m
  · intro n δ
    exact clause2_bridge_rate_homogeneous n δ
  · intro n m δ
    exact clause2_interior_rate_homogeneous n m δ

theorem clause3_endpoint :
    Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistence ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSP ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3Characterization ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransport ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransport := by
  exact ⟨Qatlib.Concepts.QsvtCore.PhaseExistence.corollary8ComplexPhaseExistence,
    Qatlib.Concepts.QsvtCore.PhaseExistence.corollary10RealQSP,
    Qatlib.Concepts.QsvtCore.PhaseExistence.theorem3Characterization,
    Qatlib.Concepts.QsvtCore.PhaseExistence.signalWordTransport,
    Qatlib.Concepts.QsvtCore.PhaseExistence.singleQubitWordTransport⟩

theorem clause4_ledger_counts (d bitTime peakWorkspace : ℕ) :
    (lcuWordLedger d bitTime peakWorkspace).dataQueries = d ∧
      (lcuWordLedger d bitTime peakWorkspace).adjointQueries = d ∧
      (lcuWordLedger d bitTime peakWorkspace).projectorNots = 2 * (d / 2) ∧
      (lcuWordLedger d bitTime peakWorkspace).phaseGates = d := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem clause4_endpoint :
    ∀ d bitTime peakWorkspace : ℕ,
      (lcuWordLedger d bitTime peakWorkspace).dataQueries = d ∧
        (lcuWordLedger d bitTime peakWorkspace).adjointQueries = d ∧
        (lcuWordLedger d bitTime peakWorkspace).projectorNots = 2 * (d / 2) ∧
        (lcuWordLedger d bitTime peakWorkspace).phaseGates = d :=
  fun d bitTime peakWorkspace => clause4_ledger_counts d bitTime peakWorkspace

theorem clause5_endpoint :
    Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma9ChebyshevWord :=
  Qatlib.Concepts.QsvtCore.PhaseExistence.lemma9ChebyshevWord

theorem clause6_endpoint :
    Qatlib.Concepts.QsvtCore.QsVtMain.SourceConventionQSVTGeneral :=
  Qatlib.Concepts.QsvtCore.QsVtMain.sourceConventionQSVTGeneral

theorem clause7_endpoint :
    Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBounds ∧
      Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquation ∧
      (∀ d bitTime peakWorkspace : ℕ,
        (lcuWordLedger d bitTime peakWorkspace).dataQueries = d ∧
          (lcuWordLedger d bitTime peakWorkspace).phaseGates = d) := by
  refine ⟨Qatlib.Concepts.QsvtCore.HamiltonianSim.simulationCostBounds_answer,
    Qatlib.Concepts.QsvtCore.HamiltonianSim.simulationCostEquation_answer, ?_⟩
  intro d bitTime peakWorkspace
  exact ⟨(clause4_ledger_counts d bitTime peakWorkspace).1,
    (clause4_ledger_counts d bitTime peakWorkspace).2.2.2⟩

private def clause8CanonicalC (k : ℕ) : ℕ → ℝ := fun q => if q = k + 1 then 1 else 0

theorem clause8_node_value (η : ℝ) (k : ℕ) :
    ((integerNode η k : Int) : ℝ) = (integerNodeNat η k : ℝ) := by
  unfold integerNode integerNodeNat
  exact (natCast_ceil_eq_intCast_ceil (R := ℝ) (by positivity)).symm

private theorem clause8_canonical_coefficients (η : ℝ) (k : ℕ) :
    (∑ q ∈ Finset.Icc 1 (k + 1), clause8CanonicalC k q = 1) ∧
      (∀ q ∈ Finset.Icc 1 k,
        |clause8CanonicalC k q| ≤
          2 ^ (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) *
            Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - correctedGamma η k))) := by
  refine ⟨by classical simp [clause8CanonicalC], ?_⟩
  intro q hq
  have hq' : q ≠ k + 1 := by
    have h1 := Finset.mem_Icc.mp hq
    omega
  simp only [clause8CanonicalC, if_neg hq', abs_zero]
  have h1 : (0:ℝ) ≤ 2 ^ (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - correctedGamma η k)) := by
    positivity
  exact h1

theorem clause8_node_integral (η : ℝ) (hη1 : 305 / 1000 < η) (hη2 : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (h t ε β : ℝ)
    (hh : 0 < h) (ht : 0 < t) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) = (integerNodeNat η k : ℝ) := by
  obtain ⟨-, -, hexp, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    lemma12IntegerNodesCorrected η hη1 hη2 k hk (m : ℝ) h t ε β (by exact_mod_cast hm)
      hh ht hε hβ hβ1 (clause8CanonicalC k) (clause8_canonical_coefficients η k).1
      (clause8_canonical_coefficients η k).2
  rw [← clause8_node_value η k]
  exact hexp

theorem clause8_gamma_bounds (η : ℝ) (hη1 : 305 / 1000 < η) (hη2 : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (h t ε β : ℝ)
    (hh : 0 < h) (ht : 0 < t) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    gammaReq η k ≤ correctedGamma η k ∧ correctedGamma η k ≤ 2 := by
  obtain ⟨-, -, -, hgam1, hgam2, -, -, -, -, -, -, -, -, -⟩ :=
    lemma12IntegerNodesCorrected η hη1 hη2 k hk (m : ℝ) h t ε β (by exact_mod_cast hm)
      hh ht hε hβ hβ1 (clause8CanonicalC k) (clause8_canonical_coefficients η k).1
      (clause8_canonical_coefficients η k).2
  exact ⟨hgam1, hgam2⟩

theorem clause8_exponential_count_within_budget (η : ℝ) (hη1 : 305 / 1000 < η)
    (hη2 : η < 312 / 1000) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (h t ε β : ℝ)
    (hh : 0 < h) (ht : 0 < t) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    (exponentialCount η k m (retryCountNat (m : ℝ) h t ε β k) : ℝ) ≤
      eq67Budget η k m (retryCountNat (m : ℝ) h t ε β k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hretry, hretry2, hretry3, hcost⟩ :=
    lemma12IntegerNodesCorrected η hη1 hη2 k hk (m : ℝ) h t ε β (by exact_mod_cast hm)
      hh ht hε hβ hβ1 (clause8CanonicalC k) (clause8_canonical_coefficients η k).1
      (clause8_canonical_coefficients η k).2
  have hretry' : ((retryCountNat (m : ℝ) h t ε β k : ℕ) : ℝ) =
      ((retryCount (m : ℝ) h t ε β k : Int) : ℝ) := by
    have h0 : 0 ≤ retryCount (m : ℝ) h t ε β k := by omega
    have h1 : ((retryCountNat (m : ℝ) h t ε β k : ℕ) : Int) =
        (retryCount (m : ℝ) h t ε β k : Int) := by
      unfold retryCountNat
      exact Int.toNat_of_nonneg h0
    exact congrArg (fun z : Int => (z : ℝ)) h1
  have hcount : (exponentialCount η k m (retryCountNat (m : ℝ) h t ε β k) : ℝ) =
      10 * (m : ℝ) * ((5 : ℝ) ^ (k - 1)) * (k : ℝ) *
        ((integerNode η k : Int) : ℝ) * ((retryCount (m : ℝ) h t ε β k : Int) : ℝ) := by
    unfold exponentialCount
    push_cast
    rw [← clause8_node_value η k, ← hretry']
    ring
  rw [hcount]
  unfold eq67Budget
  rw [hretry']
  exact hcost

theorem clause8_recovery_tail (r : ℕ) (hr : 0 < r) (p : Fin (3 * r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2) :
    MeasureProb (retryState (3 * r) p) (retryExhausted r) ≤ retryFailureBound r := by
  have h := subtractionRetryTail r hr p hp0 hp1
  exact h

theorem clause8_recovery_ledger (r : ℕ) :
    retryAttemptCount r = 3 * r ∧ retryToleratedFailures r = 2 * r ∧
      retryStepBudget r = 5 * r := by
  exact ⟨rfl, rfl, rfl⟩

theorem clause8_recovery_failure_bound (r : ℕ) (hr : 0 < r) :
    retryFailureBound r < 1 ∧
      ∀ r' : ℕ, r ≤ r' → retryFailureBound r' ≤ retryFailureBound r := by
  constructor
  · unfold retryFailureBound
    have h1 : (0:ℝ) < r := by exact_mod_cast hr
    have h2 : -(r : ℝ) / 14 < 0 := by linarith
    have h3 : Real.exp (-(r : ℝ) / 14) < Real.exp 0 := Real.exp_lt_exp.mpr h2
    simpa using! h3
  · intro r' hrr'
    unfold retryFailureBound
    have h1 : -(r' : ℝ) / 14 ≤ -(r : ℝ) / 14 := by
      have h2 : (r : ℝ) ≤ (r' : ℝ) := by exact_mod_cast hrr'
      linarith
    exact Real.exp_le_exp.mpr h1

theorem clause8_theorem13_corrected :
    Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13Corrected :=
  Qatlib.Concepts.CoherentSim.ResetDiscard.theorem13Corrected

theorem clause8_endpoint :
    Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesCorrected ∧
      (∀ η : ℝ, 305 / 1000 < η → η < 312 / 1000 → ∀ k : ℕ, 1 ≤ k →
        ∀ m : ℕ, 1 ≤ m → ∀ h t ε β : ℝ, 0 < h → 0 < t → 0 < ε → 0 < β → β < 1 →
          Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) = (integerNodeNat η k : ℝ)) ∧
      (∀ η : ℝ, 305 / 1000 < η → η < 312 / 1000 → ∀ k : ℕ, 1 ≤ k →
        ∀ m : ℕ, 1 ≤ m → ∀ h t ε β : ℝ, 0 < h → 0 < t → 0 < ε → 0 < β → β < 1 →
          (exponentialCount η k m (retryCountNat (m : ℝ) h t ε β k) : ℝ) ≤
            eq67Budget η k m (retryCountNat (m : ℝ) h t ε β k)) ∧
      (∀ r : ℕ, 0 < r → ∀ p : Fin (3 * r) → ℝ, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1 / 2) →
        MeasureProb (retryState (3 * r) p) (retryExhausted r) ≤ retryFailureBound r) ∧
      Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13Corrected := by
  refine ⟨Qatlib.Papers.HamLCUSim12.Multiproduct.lemma12IntegerNodesCorrected, ?_, ?_, ?_, ?_⟩
  · intro η hη1 hη2 k hk m hm h t ε β hh ht hε hβ hβ1
    exact clause8_node_integral η hη1 hη2 k hk m hm h t ε β hh ht hε hβ hβ1
  · intro η hη1 hη2 k hk m hm h t ε β hh ht hε hβ hβ1
    exact clause8_exponential_count_within_budget η hη1 hη2 k hk m hm h t ε β hh ht hε hβ hβ1
  · intro r hr p hp0 hp1
    exact clause8_recovery_tail r hr p hp0 hp1
  · exact clause8_theorem13_corrected

theorem clause9_source_word_plan (d : ℕ) (A Qt : Polynomial ℝ) (hd : Even d) (hd0 : 0 < d)
    (hA : A.comp (-Polynomial.X) = A) (hQt : Qt.comp (-Polynomial.X) = -Qt)
    (hAdeg : A.degree ≤ (d : WithBot ℕ)) (hQtdeg : Qt.degree < (d : WithBot ℕ))
    (hineq : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1)
    (hA1 : A.eval 1 = 1) :
    ∃ (w : SourceWordPlan), w.phaseGates + 1 = d ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        lqRepoAmpWord w.gamma0 w.gamma1 w.psis x =
          realEval A (Complex.ofReal x) +
            Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt (Complex.ofReal x) := by
  obtain ⟨γ₀, γ₁, psis, hlen, hamp⟩ :=
    clause9_clause1c d A Qt hd hd0 hA hQt hAdeg hQtdeg hineq hA1
  refine ⟨{ gamma0 := γ₀, gamma1 := γ₁, psis := psis }, ?_, ?_⟩
  · exact hlen
  · intro x hx
    exact hamp x hx

theorem clause9_source_word_charges_ledger (d : ℕ) (A Qt : Polynomial ℝ) (hd : Even d) (hd0 : 0 < d)
    (hA : A.comp (-Polynomial.X) = A) (hQt : Qt.comp (-Polynomial.X) = -Qt)
    (hAdeg : A.degree ≤ (d : WithBot ℕ)) (hQtdeg : Qt.degree < (d : WithBot ℕ))
    (hineq : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1)
    (hA1 : A.eval 1 = 1) :
    ∃ (w : SourceWordPlan), w.phaseGates = d - 1 ∧
      w.projectorNots = 2 * ((d - 1) / 2) ∧
      w.boundaryRotations = 2 := by
  obtain ⟨w, hlen, _⟩ :=
    clause9_source_word_plan d A Qt hd hd0 hA hQt hAdeg hQtdeg hineq hA1
  refine ⟨w, ?_, ?_, ?_⟩
  · have h1 : w.phaseGates + 1 = d := hlen
    omega
  · have h1 : w.phaseGates = d - 1 := by omega
    have h2 : w.psis.length = d - 1 := by
      simp only [SourceWordPlan.phaseGates] at h1
      exact h1
    simp only [SourceWordPlan.projectorNots, h2]
  · rfl

theorem clause9_source_word_matches_compiled_ledger (w : SourceWordPlan)
    (bitTime peakWorkspace : ℕ) :
    w.phaseGates = (lcuWordLedger w.phaseGates bitTime peakWorkspace).phaseGates ∧
      w.projectorNots = (lcuWordLedger w.phaseGates bitTime peakWorkspace).projectorNots := by
  have h4 := clause4_ledger_counts w.phaseGates bitTime peakWorkspace
  refine ⟨h4.2.2.2, ?_⟩
  calc w.projectorNots = 2 * (w.phaseGates / 2) := rfl
    _ = (lcuWordLedger w.phaseGates bitTime peakWorkspace).projectorNots := h4.2.2.1.symm

private theorem clause9_sparse_row_card {n d : ℕ} {b : ℝ} (O : LqSparseOracle n d b) :
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

private theorem clause9_sparse_col_card {n d : ℕ} {b : ℝ} (O : LqSparseOracle n d b) :
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

private theorem clause9_scaled_opNorm_le_one {n d : ℕ} {b : ℝ}
    (O : LqSparseOracle n d b) (hd : 0 < d) (hb : 0 < b) :
    ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • O.H‖ ≤ 1 := by
  have hrow := clause9_sparse_row_card O
  have hcol := clause9_sparse_col_card O
  have hconsumer := sparse_overlap_derived_sparse_entry_norm_consumer
    (Fin (2 ^ n)) (Fin (2 ^ n)) O.H d b hb hd hrow hcol O.entry_bound
  have hnorm : ‖O.H‖ ≤ (d : ℝ) * b := hconsumer.2
  have hdb : (0 : ℝ) < (d : ℝ) * b := mul_pos (by exact_mod_cast hd) hb
  have hsmul : ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • O.H‖
      = ‖((((d : ℝ) * b)⁻¹ : ℝ) : ℂ)‖ * ‖O.H‖ := norm_smul _ _
  rw [hsmul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdb)]
  rw [← div_eq_inv_mul]
  exact (div_le_one hdb).mpr hnorm

theorem clause9_walk_frame_constructed {n d : ℕ} {b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (O : LqSparseOracle n d b) :
    ∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
      (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
      LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S := by
  exact walk_frame_of_spectral (((d : ℝ) * b)⁻¹ : ℝ) O.H O.hermitian
    (clause9_scaled_opNorm_le_one O hd hb)

theorem clause9_sparse_simulation_constructed {n d : ℕ} {b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (O : LqSparseOracle n d b)
    (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ)
    (hframe : LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S) :
    SparseEigenphaseTransport n d b O L R S ∧
      ∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
        SparseSimulationWord n d b O L R S t ε := by
  obtain ⟨h6, h7⟩ := clause9_clause3_from_frame n d b hd hb O L R S hframe
  refine ⟨h6, ?_⟩
  intro t ε ht hε hε1
  exact h7 t ε ht hε hε1

theorem clause9_sparse_simulation_from_oracle {n d : ℕ} {b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (O : LqSparseOracle n d b) :
    (∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S) ∧
      ∀ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S →
          ∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
            SparseSimulationWord n d b O L R S t ε := by
  obtain ⟨L, R, S, hframe⟩ := clause9_walk_frame_constructed (O := O) hd hb
  refine ⟨⟨L, R, S, hframe⟩, ?_⟩
  intro L' R' S' hframe' t ε ht hε hε1
  obtain ⟨_, h7⟩ := clause9_sparse_simulation_constructed (O := O) hd hb L' R' S' hframe'
  exact h7 t ε ht hε hε1

theorem clause9_sparse_word_charges_ledger (Q bitTime peakWorkspace : ℕ) :
    (lcuWordLedger (2 * (Q - 1)) bitTime peakWorkspace).phaseGates = 2 * (Q - 1) ∧
      (lcuWordLedger (2 * (Q - 1)) bitTime peakWorkspace).dataQueries = 2 * (Q - 1) ∧
      (lcuWordLedger (2 * (Q - 1)) bitTime peakWorkspace).adjointQueries = 2 * (Q - 1) := by
  have h4 := clause4_ledger_counts (2 * (Q - 1)) bitTime peakWorkspace
  exact ⟨h4.2.2.2, h4.1, h4.2.1⟩

theorem clause9_window_count_bounds (d : ℕ) (b t ε : ℝ)
    (hd : 0 < d) (hb : 0 < b) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    3 * (t * (d : ℝ) * b) ≤ (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ∧
      2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
        8 * (Real.log (32 / (ε / 8)) /
          Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) + 2) ∧
      2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
        2 * (3 * (t * (d : ℝ) * b) + 3 * Real.log (32 / (ε / 8)) + 8) :=
  clause9_clause4 d b t ε hd hb ht hε hε1

theorem clause9_window_length_budget (τ ε : ℝ) :
    τ + 1 ≤ (lcCorrectedQ τ ε : ℝ) :=
  lcCorrectedQ_length_budget τ ε

theorem clause9_window_count_at_least_four (τ ε : ℝ) :
    4 ≤ lcuWindowCount τ ε := by
  unfold lcuWindowCount lcCorrectedQ
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem clause9_endpoint :
    Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncation ∧
      Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegree ∧
      (∀ d : ℕ, ∀ A Qt : Polynomial ℝ, Even d → 0 < d → A.comp (-Polynomial.X) = A →
        Qt.comp (-Polynomial.X) = -Qt → A.degree ≤ (d : WithBot ℕ) →
        Qt.degree < (d : WithBot ℕ) →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) →
        A.eval 1 = 1 → ∃ (w : SourceWordPlan), w.phaseGates = d - 1 ∧
          w.projectorNots = 2 * ((d - 1) / 2) ∧ w.boundaryRotations = 2) ∧
      Lc17EndpointContract ∧
      (∀ {n d : ℕ} {b : ℝ}, 0 < d → 0 < b → ∀ O : LqSparseOracle n d b,
        (∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
            (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
            LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S) ∧
          ∀ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
            (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
            LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S →
              ∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
                SparseSimulationWord n d b O L R S t ε) ∧
      (∀ (d : ℕ) (b t ε : ℝ), 0 < d → 0 < b → 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
        3 * (t * (d : ℝ) * b) ≤ (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ∧
          2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
            8 * (Real.log (32 / (ε / 8)) /
              Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) + 2) ∧
          2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
            2 * (3 * (t * (d : ℝ) * b) + 3 * Real.log (32 / (ε / 8)) + 8)) ∧
      (∀ τ ε : ℝ, τ + 1 ≤ (lcCorrectedQ τ ε : ℝ)) ∧
      (∀ τ ε : ℝ, 4 ≤ lcuWindowCount τ ε) := by
  refine ⟨Qatlib.Concepts.QspSimulation.JacobiAnger.jacobiAngerTruncation,
    Qatlib.Concepts.QspSimulation.JacobiAnger.jacobiAngerCorrectedDegree, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro d A Qt hd hd0 hA hQt hAdeg hQtdeg hineq hA1
    exact clause9_source_word_charges_ledger d A Qt hd hd0 hA hQt hAdeg hQtdeg hineq hA1
  · exact Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame.g9
  · intro n d b hd hb O
    exact clause9_sparse_simulation_from_oracle (O := O) hd hb
  · intro d b t ε hd hb ht hε hε1
    exact clause9_window_count_bounds d b t ε hd hb ht hε hε1
  · intro τ ε
    exact clause9_window_length_budget τ ε
  · intro τ ε
    exact clause9_window_count_at_least_four τ ε

end G1

end Qatlib.Papers.QSingValue19.AlgorithmApps
