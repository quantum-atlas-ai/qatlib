/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeGroupedColumnError
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeEndpointDiagnosis
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannBlockEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeLegalAbstractExperiment
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
/-! Actual-column weighting of the existing shared original-query Neumann
word. Label duplication is explicit; a scalar grouped residual replaces any
comparison with a canonical full PREPARE completion. The outer PREPARE,
phase, frame and Neumann preparations still use matrix-macro semantics. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {K J H I : Type} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for grouped Neumann Inner Dec Eq in the native grouped neumann consumer model. -/
local instance groupedNeumannInnerDecEq (b : ℕ) : DecidableEq
    (NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for grouped Neumann Outer Dec Eq in the native grouped neumann consumer model. -/
local instance groupedNeumannOuterDecEq (b : ℕ) : DecidableEq
    (K × NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- All nodes retain the same input oracle and common frame. The estimate
does not require a small native coefficient error; the b-dependent price is
explicit. The given Q and phase table are known parameters, not a synthesis
or precision-selection algorithm. -/
theorem grouped_native_neumann_resolvent
    (b : ℕ) (hb : 0 < b) (node : K → J) (hnode : Function.Surjective node)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (weights : J → ℂ) (Q : Matrix K K ℂ) (φ : K → ℂ) (k₀ : K)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B L D : ℝ) (r : J → ℝ) (z : J → ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B) (hL : 0 < L)
    (hbound : ∀ j, α + ‖z j‖ ≤ B) (hr : ∀ j, 0 < r j)
    (hsep : ∀ j w, w ∈ matrixNumericalRange A → r j ≤ ‖z j - w‖)
    (hQ : Q ∈ Matrix.unitaryGroup K ℂ) (hφ : ∀ k, star (φ k) * φ k = 1)
    (hD : ∑ j, ‖weights j / (L : ℂ) - groupedColumnCoefficient node Q φ k₀ j‖ ≤ D) :
    BlockEncoding (∑ j, weights j • matrixResolvent A (z j))
      (evaluate (cleanEndpointOracle (J := K) b U)
        (columnPhaseWord Q φ (cleanEndpointBody b hb F
          (fun k => ps (node k)) (fun k => p (node k)) (fun k => slack (node k)))))
      (tagFrame k₀ (cleanEndpointFrame b hb F))
      (tagFrame k₀ (cleanEndpointFrame b hb F)) (L * ((b : ℝ) / B))
      ((∑ j, ‖weights j‖ *
        (((b : ℝ)^2 * nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
          reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B)) +
        L * ((b : ℝ) / B) * D) := by
  let Y := cleanEndpointBlock b A α ps p slack
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have he (j : J) : ‖matrixResolvent A (z j) - ((b : ℝ) / B) • Y j‖ ≤
      ((b : ℝ)^2 * nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
        reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B := by
    have hs : ((b : ℝ) / B) • Y j = ((B⁻¹ : ℝ) : ℂ) •
        leftDefectNeumann (nativeShiftBlock (ps j) (p j) (slack j) A α) b := by
      ext x y
      simp only [Y, cleanEndpointBlock, nativeShiftBlock, Matrix.smul_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_inv]
      field_simp [hbc, hBc]
    rw [hs, norm_sub_rev]
    exact (native_original_neumann_resolvent b hb (ps j) (p j) (slack j)
      A U F α B (r j) (z j) hbe hB (hbound j) (hr j) (hsep j)).2.2.1
  exact grouped_column_word_error node hnode (cleanEndpointFrame b hb F)
    (cleanEndpointOracle (J := K) b U)
    (cleanEndpointBody b hb F (fun k => ps (node k))
      (fun k => p (node k)) (fun k => slack (node k)))
    Y (fun j => matrixResolvent A (z j)) Q φ k₀ weights L ((b : ℝ) / B) D
    (fun j => ((b : ℝ)^2 * nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
      reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B)
    (endpoint_frame_isometry b hb F hbe.left_isometry) hQ hφ
    (endpoint_word_unitary b hb F A U α hbe _ _ _)
    (endpoint_block b hb F A U α hbe _ _ _)
    hL (div_pos hbp hB) hD he

omit [Fintype J] [DecidableEq J] [DecidableEq I] in
/-- Counts of that same word. The three added instructions are the supplied
PREPARE/phase/adjoint matrices, not the expanded physical-stream ledger. -/
theorem grouped_native_neumann_word_counts
    (b : ℕ) (hb : 0 < b) (node : K → J)
    (F : Matrix H I ℂ) (U : Matrix H H ℂ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (Q : Matrix K K ℂ) (φ : K → ℂ) :
    adjointQueryCount (columnPhaseWord Q φ (cleanEndpointBody b hb F
      (fun k => ps (node k)) (fun k => p (node k)) (fun k => slack (node k)))) = 2*b-1 ∧
    adjointGateCount (columnPhaseWord Q φ (cleanEndpointBody b hb F
      (fun k => ps (node k)) (fun k => p (node k)) (fun k => slack (node k)))) =
      2*b+(2*b-1)*3+3 := by
  have hc := columnPhaseWord_counts Q φ (cleanEndpointBody b hb F
    (fun k => ps (node k)) (fun k => p (node k)) (fun k => slack (node k)))
  have hs := nativeMultiNodeRelabeledWord_cost b hb F
    (fun k => ps (node k)) (fun k => p (node k)) (fun k => slack (node k)) U
  exact ⟨hc.1.trans hs.1, hc.2.trans (by rw [cleanEndpointBody, hs.2])⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
