/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitReciprocalCutoff
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! The original matrix oracle drives the entire shared, averaged Neumann word.
Known preparation and frame gates are explicit ideal matrix macros; elementary
synthesis and bit complexity are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L]


/-- Fixed program parameters contain no unknown original data matrix. -/
def rawUniformNeumannWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (α B₀ : ℝ) (z : L → ℂ) :
    List (AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × ShiftedRawSpace L H))) :=
  substituteAdjointCircuit
    (phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (rawShiftedWord α B₀ z))
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector (rawShiftedFrame F)))

omit [Fintype H] in
/-- The finite construction in `OriginalUniformNeumann` satisfies `oracle_one` under the displayed hypotheses. -/
private theorem oracle_one (b : ℕ) : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle (H := H) b 1 = 1 := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, parallelOracle, parallel_select_one,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, TensorGate, Matrix.one_kronecker_one]

/-- The finite construction in `OriginalUniformNeumann` satisfies `oracle_mul` under the displayed hypotheses. -/
private theorem oracle_mul (b : ℕ) (U V : Matrix H H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (U*V) = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U * Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_mul, Matrix.one_mul,
    parallelOracle, parallel_select_mul]

/-- The finite construction in `OriginalUniformNeumann` satisfies `oracle_adjoint` under the displayed hypotheses. -/
private theorem oracle_adjoint (b : ℕ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b Uᴴ = (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U)ᴴ := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_conjTranspose,
    Matrix.conjTranspose_one, parallelOracle, parallel_select_adjoint]

/-- The actual finite word or frame satisfies `oracle_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem oracle_unitary (b : ℕ) (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U ∈ unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))

/-- The actual original-query word, its mean polynomial target, all known macros
and every forward/backward body call are tied to the same program. -/
theorem original_uniform_neumann_encoding (b : ℕ) (hb : 0 < b)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B₀ : ℝ) (z : L → ℂ) (henc : BlockEncoding A U F F α 0)
    (hB : 0 < B₀) (hbound : ∀ j, α + ‖z j‖ ≤ B₀) :
    WellFormedAdjointCircuit (rawUniformNeumannWord b hb F α B₀ z) ∧
    ProjectedUnitaryEncoding (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (jointNormalizedShift A z B₀) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (rawShiftedQuery (L := L) U))
        (rawUniformNeumannWord b hb F α B₀ z))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F)) ∧
    adjointQueryCount (rawUniformNeumannWord b hb F α B₀ z) = 2*b-1 ∧
    adjointGateCount (rawUniformNeumannWord b hb F α B₀ z) = 8*b-3 := by
  obtain ⟨hword, hs, hrawq, hrawg⟩ := raw_shifted_encoding H I L A U F α B₀ z henc hB hbound
  let W := evaluate (rawShiftedQuery (L := L) U) (rawShiftedWord α B₀ z)
  let P := rangeProjector (rawShiftedFrame (L := L) F)
  let cs := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P
  let body := phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (rawShiftedWord (H := H) α B₀ z)
  have hp : IsOrthogonalProjector P := rangeProjector_isOrthogonalProjector hs.left_isometry
  obtain ⟨hcq,hcg,hcw⟩ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb P
  have hbq : adjointQueryCount body = 1 := (phaseLiftWord_counts _ _).1.trans hrawq
  have hbg : adjointGateCount body = 3 := (phaseLiftWord_counts _ _).2.trans hrawg
  have hbw : WellFormedAdjointCircuit body := phaseLiftWord_wellFormed
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (oracle_unitary b) hword
  have hlift := phaseLiftWord_evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (oracle_one b)
    (oracle_mul b) (oracle_adjoint b) (rawShiftedQuery (L := L) U) (rawShiftedWord α B₀ z)
  obtain ⟨he,hq,hg,hw⟩ := substitute_adjoint_evaluate_cost
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (rawShiftedQuery (L := L) U)) body cs
  have ht : evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (rawShiftedQuery (L := L) U))
      (rawUniformNeumannWord b hb F α B₀ z) = evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b W) cs := by
    change evaluate _ (substituteAdjointCircuit body cs) = _
    rw [he, hlift]
  have hbe := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding b hb W (rawShiftedFrame (L := L) F)
    hs.unitary hs.left_isometry
  rw [hs.encoded] at hbe
  refine ⟨hw hbw (hcw hp), ?_, ?_, ?_⟩
  · rw [ht]
    exact hbe
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [hq, hcq, hbq, Nat.mul_one]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [hg, hcg, hcq, hbg]
    omega

/-- Actual resolvent and geometric error from original common-frame/actual-W
inputs, on the same shared averaged word with no reciprocal-phase input. -/
theorem original_uniform_neumann_resolvent (b : ℕ) (hb : 0 < b)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B₀ r : ℝ) (z : L → ℂ) (henc : BlockEncoding A U F F α 0)
    (hB : 0 < B₀) (hbound : ∀ j, α + ‖z j‖ ≤ B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖) :
    WellFormedAdjointCircuit (rawUniformNeumannWord b hb F α B₀ z) ∧
    BlockEncoding (jointMatrixResolvent A z)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (rawShiftedQuery (L := L) U))
        (rawUniformNeumannWord b hb F α B₀ z))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F))
      ((b : ℝ)/B₀) (reciprocalError (jointResolventCondition B₀ r)⁻¹ b / B₀) ∧
    adjointQueryCount (rawUniformNeumannWord b hb F α B₀ z) = 2*b-1 ∧
    adjointGateCount (rawUniformNeumannWord b hb F α B₀ z) = 8*b-3 := by
  obtain ⟨hw,he,hq,hg⟩ := original_uniform_neumann_encoding b hb A U F α B₀ z henc hB hbound
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hk : 0 < jointResolventCondition B₀ r := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hk1 : (jointResolventCondition B₀ r)⁻¹ ≤ 1 :=
    (inv_le_one₀ hk).mpr ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _))
  have herr := original_neumann_resolvent_error H I L A U F α B₀ r z b henc hB hbound hr hsep
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hBc : (B₀ : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hscale : ((b : ℝ)/B₀) • (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (jointNormalizedShift A z B₀) b) =
      jointNeumannResolvent A z B₀ b := by
    ext i j
    simp only [jointNeumannResolvent, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv]
    field_simp [hbc,hBc]
  refine ⟨hw, ⟨he.unitary, he.left_isometry, he.right_isometry, div_pos hbp hB,
    div_nonneg (reciprocalError_nonneg (inv_pos.mpr hk) hk1 b) hB.le, ?_⟩, hq, hg⟩
  rw [he.encoded, hscale]
  simpa only [norm_sub_rev] using herr


/-- The finite construction in `OriginalUniformNeumann` satisfies `reciprocal_condition_mono` under the displayed hypotheses. -/
private theorem reciprocal_condition_mono (κ K : ℝ) (hκ : 1 ≤ κ) (hK : κ ≤ K) (b : ℕ) :
    reciprocalError κ⁻¹ b ≤ reciprocalError K⁻¹ b := by
  have hκp : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hKp : 0 < K := hκp.trans_le hK
  have hi : K⁻¹ ≤ κ⁻¹ := (inv_le_inv₀ hKp hκp).mpr hK
  have hκi : κ⁻¹ ≤ 1 := (inv_le_one₀ hκp).mpr hκ
  have hκ0 : 0 ≤ κ⁻¹ := (inv_pos.mpr hκp).le
  have hq : 0 ≤ 1-κ⁻¹^2 := by nlinarith
  have hqle : 1-κ⁻¹^2 ≤ 1-K⁻¹^2 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hKp.le) hi 2
    linarith
  unfold reciprocalError
  simp only [div_eq_mul_inv, inv_inv]
  exact mul_le_mul (pow_le_pow_left₀ hq hqle b) hK hκp.le
    (pow_nonneg (hq.trans hqle) b)

/-- A finite integer cutoff closes the precision parameter without any phase
search. This conservative pinned cutoff is K²(k+K+1), not the tighter analytical
K² log(K/epsilon) cutoff discussed in the experiment. -/
theorem original_uniform_neumann_precision (K k : ℕ)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B₀ r : ℝ) (z : L → ℂ) (henc : BlockEncoding A U F F α 0)
    (hB : 0 < B₀) (hbound : ∀ j, α + ‖z j‖ ≤ B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖)
    (hK : jointResolventCondition B₀ r ≤ (K : ℝ)) :
    let b := explicitInverseCutoff K k
    ∃ hb : 0 < b,
      WellFormedAdjointCircuit (rawUniformNeumannWord b hb F α B₀ z) ∧
      BlockEncoding (jointMatrixResolvent A z)
        (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (rawShiftedQuery (L := L) U))
          (rawUniformNeumannWord b hb F α B₀ z))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (rawShiftedFrame F))
        ((b : ℝ)/B₀) (((2 : ℝ)⁻¹)^k/B₀) ∧
      adjointQueryCount (rawUniformNeumannWord b hb F α B₀ z) = 2*b-1 ∧
      adjointGateCount (rawUniformNeumannWord b hb F α B₀ z) = 8*b-3 := by
  have hκ2 : 2 ≤ jointResolventCondition B₀ r := le_max_left _ _
  have hKp : 0 < K := by
    have h : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hκ2.trans hK)
    exact_mod_cast h
  let b := explicitInverseCutoff K k
  have hb : 0 < b := (explicit_inverse_cutoff_integer_formula K k).2 hKp
  obtain ⟨hw,he,hq,hg⟩ := original_uniform_neumann_resolvent b hb A U F α B₀ r z
    henc hB hbound hr hsep
  refine ⟨hb,hw,he.mono ?_,hq,hg⟩
  apply div_le_div_of_nonneg_right _ hB.le
  exact (reciprocal_condition_mono _ _ ((by norm_num : (1 : ℝ) ≤ 2).trans hκ2) hK b).trans
    (explicit_inverse_geometric_precision K k hKp)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
