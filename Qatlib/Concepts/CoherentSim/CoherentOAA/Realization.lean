/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem qsvt_odd_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₂
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R := by
  refine ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.right_isometry, ?_⟩
  exact qsvt_odd_eq_dilation h base zs hodd

theorem qsvt_even_left_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₁
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L L := by
  refine ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.left_isometry, ?_⟩
  exact qsvt_even_left_eq_dilation h base zs heven

theorem qsvt_even_right_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₂₂
      (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R R := by
  refine ⟨phasedAlternating_unitary (adjoint_unitary h.unitary)
    (rangeProjector_isOrthogonalProjector h.left_isometry)
    (rangeProjector_isOrthogonalProjector h.right_isometry) hb zs hzs,
    h.right_isometry, h.right_isometry, ?_⟩
  exact qsvt_even_right_eq_dilation h base zs heven

theorem qsvt_odd_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ∃ cs : List (AdjointStep H),
      ProjectedUnitaryEncoding
        (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₂
        (evaluate U cs) L R ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    queryCount_compileQSVT _ _ _ _, gateCount_compileQSVT _ _ _ _⟩
  rw [evaluate_compileQSVT]
  exact qsvt_odd_projectedEncoding h hb zs hzs hodd

theorem qsvt_even_right_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ∃ cs : List (AdjointStep H),
      ProjectedUnitaryEncoding
        (aeval (hermitianDilation A) (responseP base zs)).toBlocks₂₂
        (evaluate U cs) R R ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨(compileQSVT (rangeProjector L) (rangeProjector R) base zs).map swapQueries,
    ?_, ?_, ?_⟩
  · rw [evaluate_swapQueries, evaluate_compileQSVT]
    exact qsvt_even_right_projectedEncoding h hb zs hzs heven
  · rw [adjointQueryCount_swapQueries, queryCount_compileQSVT]
  · rw [adjointGateCount_swapQueries, gateCount_compileQSVT]

section SpectralNorm

open scoped Matrix.Norms.L2Operator

theorem qsvt_odd_oracleReplacement {A : Matrix O I ℂ} {U V : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z)
    (hodd : zs.length % 2 = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hUV : ‖U - V‖ ≤ δ) :
    BlockEncoding (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₂
      (phasedAlternating V (rangeProjector R) (rangeProjector L) base zs) L R
      1 ((zs.length : ℝ) * δ) := by
  have hP := rangeProjector_isOrthogonalProjector h.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector h.left_isometry
  refine ⟨phasedAlternating_unitary hV hP hQ hb zs hzs,
    h.left_isometry, h.right_isometry, by norm_num,
    mul_nonneg (Nat.cast_nonneg _) hδ, ?_⟩
  rw [one_smul, ← qsvt_odd_eq_dilation h base zs hodd]
  exact (compress_phasedAlternating_oracle_error h.left_isometry h.right_isometry
    h.unitary hV hP hQ hb zs hzs).trans
      (mul_le_mul_of_nonneg_left hUV (Nat.cast_nonneg _))

end SpectralNorm

end Qatlib.Concepts.CoherentSim.CoherentOAA
