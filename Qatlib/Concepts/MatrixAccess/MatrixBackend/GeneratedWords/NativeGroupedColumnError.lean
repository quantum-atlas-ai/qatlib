/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeColumnWeightedWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Group actual preparation labels before estimating coefficient error. In
particular, two slack labels selecting the same node pay their imbalance,
not the sum of their probabilities. This is a matrix-macro consumer, not a
refinement of the Python emitter or a discrete-gate synthesis theorem. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {K J H I : Type} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The actual coefficient at a node, after all labels mapping to it have
been combined. Padding with zero amplitude contributes zero automatically. -/
def groupedColumnCoefficient (node : K → J) (Q : Matrix K K ℂ)
    (φ : K → ℂ) (k₀ : K) (j : J) : ℂ :=
  ∑ k, if node k = j then columnPhaseCoefficient Q φ k₀ k else 0

omit [DecidableEq K] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in
/-- The finite construction in `NativeGroupedColumnError` satisfies `sum_grouped_column` under the displayed hypotheses. -/
theorem sum_grouped_column (node : K → J) (Q : Matrix K K ℂ)
    (φ : K → ℂ) (k₀ : K) (Y : J → Matrix I I ℂ) :
    (∑ k, columnPhaseCoefficient Q φ k₀ k • Y (node k)) =
      ∑ j, groupedColumnCoefficient node Q φ k₀ j • Y j := by
  simp only [groupedColumnCoefficient, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [ite_smul]

/-- Positive scale, actual grouped scalar residual and per-node error
produce a bound for the very same wrapped query word. The source relation
is only on the clean subspace; no full SELECT equality is assumed. -/
theorem grouped_column_word_error
    [outer : DecidableEq (K × H)]
    (node : K → J) (hnode : Function.Surjective node)
    (F : Matrix H I ℂ) (O : Matrix (K × H) (K × H) ℂ)
    (W : List (AdjointStep (K × H))) (Y T : J → Matrix I I ℂ)
    (Q : Matrix K K ℂ) (φ : K → ℂ) (k₀ : K)
    (weights : J → ℂ) (L s D : ℝ) (ε : J → ℝ)
    (hF : IsIsometry F) (hQ : Q ∈ Matrix.unitaryGroup K ℂ)
    (hφ : ∀ k, star (φ k) * φ k = 1)
    (hW : evaluate O W ∈ Matrix.unitaryGroup (K × H) ℂ)
    (hblock : compress ((1 : Matrix K K ℂ) ⊗ₖ F) (evaluate O W)
      ((1 : Matrix K K ℂ) ⊗ₖ F) = select (fun k => Y (node k)))
    (hL : 0 < L) (hs : 0 < s)
    (hD : ∑ j, ‖weights j / (L : ℂ) - groupedColumnCoefficient node Q φ k₀ j‖ ≤ D)
    (hε : ∀ j, ‖T j - s • Y j‖ ≤ ε j) :
    BlockEncoding (∑ j, weights j • T j)
      (evaluate O (columnPhaseWord Q φ W)) (tagFrame k₀ F) (tagFrame k₀ F)
      (L * s) ((∑ j, ‖weights j‖ * ε j) + L * s * D) := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  let c := groupedColumnCoefficient node Q φ k₀
  have hp := column_phase_word_encoding F O W (fun k => Y (node k)) Q φ k₀
    hF hQ hφ hW hblock
  have hcorner : compress (tagFrame k₀ F) (evaluate O (columnPhaseWord Q φ W))
      (tagFrame k₀ F) = ∑ j, c j • Y j := by
    exact hp.encoded.trans (sum_grouped_column node Q φ k₀ Y)
  have hn (j : J) : ‖Y j‖ ≤ 1 := by
    obtain ⟨k,hk⟩ := hnode j
    simpa only [hk] using clean_node_norm_le_one F (evaluate O W)
      (fun k => Y (node k)) hF hW hblock k
  have hε0 (j : J) : 0 ≤ ε j := (norm_nonneg _).trans (hε j)
  have hD0 : 0 ≤ D := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hD
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have herrc : ‖∑ j, (weights j - (L : ℂ) * c j) • Y j‖ ≤ L * D := by
    calc
      _ ≤ ∑ j, ‖(weights j - (L : ℂ) * c j) • Y j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖weights j - (L : ℂ) * c j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (hn j) (norm_nonneg _)).trans_eq (mul_one _)
      _ = L * ∑ j, ‖weights j / (L : ℂ) - c j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have he : weights j - (L : ℂ) * c j =
            (L : ℂ) * (weights j / (L : ℂ) - c j) := by field_simp
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hL.le
  have herrn : ‖∑ j, weights j • (T j - s • Y j)‖ ≤ ∑ j, ‖weights j‖ * ε j := by
    calc
      _ ≤ ∑ j, ‖weights j • (T j - s • Y j)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun j _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hε j) (norm_nonneg _))
  have hsplit : (∑ j, weights j • T j) - (L * s) • (∑ j, c j • Y j) =
      (∑ j, weights j • (T j - s • Y j)) +
        s • (∑ j, (weights j - (L : ℂ) * c j) • Y j) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ext x y
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  refine ⟨hp.unitary, hp.left_isometry, hp.right_isometry, mul_pos hL hs,
    add_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hε0 j)))
      (mul_nonneg (mul_nonneg hL.le hs.le) hD0), ?_⟩
  rw [hcorner, hsplit]
  calc
    _ ≤ ‖∑ j, weights j • (T j - s • Y j)‖ +
        ‖s • (∑ j, (weights j - (L : ℂ) * c j) • Y j)‖ := norm_add_le _ _
    _ ≤ (∑ j, ‖weights j‖ * ε j) + s * (L * D) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      exact add_le_add herrn (mul_le_mul_of_nonneg_left herrc hs.le)
    _ = _ := by ring

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
