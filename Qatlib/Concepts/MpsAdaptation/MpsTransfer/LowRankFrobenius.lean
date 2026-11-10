/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.HermitianRankLogStability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem spectralFrobenius_lowRank_error
    {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A X : Matrix O I ℂ) :
    spectralFrobenius A^2 - (X.rank : ℝ)*‖A‖^2 ≤ spectralFrobenius (A-X)^2 := by
  have hsigma (i : Fin (Fintype.card I)) : matrixSingularValues A i ≤ ‖A‖ := by
    have h := Matrix.l2_opNorm_mulVec A (rightSingularBasis A i)
    change ‖A.toEuclideanLin (rightSingularBasis A i)‖ ≤
      ‖A‖*‖rightSingularBasis A i‖ at h
    simpa only [norm_apply_rightSingularBasis, norm_rightSingularBasis, mul_one] using h
  let J : Finset (Fin (Fintype.card I)) := Finset.univ.filter fun i => i.val < X.rank
  have hcard : J.card ≤ X.rank := by
    have hsub : J.image (fun i => i.val) ⊆ Finset.range X.rank := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    calc
      J.card = (J.image (fun i => i.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.range X.rank).card := Finset.card_le_card hsub
      _ = X.rank := Finset.card_range _
  have hpoint (i : Fin (Fintype.card I)) :
      (matrixSingularValues A i)^2 ≤
        (matrixSingularValues A i-matrixSingularValues X i)^2 +
          if i.val < X.rank then ‖A‖^2 else 0 := by
    by_cases hi : i.val < X.rank
    · rw [if_pos hi]
      have hs := (sq_le_sq₀ (matrixSingularValues_nonneg A i) (norm_nonneg A)).mpr (hsigma i)
      nlinarith [sq_nonneg (matrixSingularValues A i-matrixSingularValues X i)]
    · rw [if_neg hi, matrixSingularValues_eq_zero_of_rank_le (Nat.le_of_not_gt hi)]
      simp
  have hbonus : (∑ i : Fin (Fintype.card I), if i.val < X.rank then ‖A‖^2 else 0) =
      (J.card : ℝ)*‖A‖^2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, J]
  have hsum :=
      Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (Fintype.card I)))) => hpoint i)
  rw [Finset.sum_add_distrib, hbonus, ← spectralFrobenius_sq_singular] at hsum
  have hmirsky := singular_mirsky_bound A X
  have hc : (J.card : ℝ)*‖A‖^2 ≤ (X.rank : ℝ)*‖A‖^2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
  linarith

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
