/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.LinearMetaGrad
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option warningAsError false

noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace Qatlib.Papers.LatentPQCTran26.MainResults.EuclideanLayer

abbrev Parameters (K D : ℕ) := EuclideanSpace ℝ (Fin K × Option (Fin D))

def columnLinear (K D : ℕ) (col : Option (Fin D)) :
    Parameters K D →ₗ[ℝ] EuclideanSpace ℝ (Fin K) where
  toFun w := WithLp.toLp 2 (fun i => w (i,col))
  map_add' u v := by ext i; rfl
  map_smul' c w := by ext i; rfl

theorem column_norm_le (K D : ℕ) (col : Option (Fin D)) (w : Parameters K D) :
    ‖columnLinear K D col w‖ ≤ ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (w (i,j))) (Finset.mem_univ col)

def column (K D : ℕ) (col : Option (Fin D)) :
    Parameters K D →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  (columnLinear K D col).mkContinuous 1 (fun w => by simpa using column_norm_le K D col w)

def decoder (K D : ℕ) (u : Fin D → ℝ) :
    Parameters K D →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  column K D none + ∑ j, u j • column K D (some j)

theorem decoder_apply (K D : ℕ) (u : Fin D → ℝ) (w : Parameters K D) (i : Fin K) :
    decoder K D u w i = w (i,none) + ∑ j, u j * w (i,some j) := by
  simp [decoder, column, columnLinear]

theorem decoder_continuous (K D : ℕ) : Continuous (decoder K D) := by
  unfold decoder
  fun_prop

theorem decoder_norm_le (K D : ℕ) (u : Fin D → ℝ) (M : ℝ)
    (hM : ∀ j, |u j| ≤ M) :
    ‖decoder K D u‖ ≤ ‖column K D none‖ + M * ∑ j, ‖column K D (some j)‖ := by
  calc
    ‖decoder K D u‖ ≤ ‖column K D none‖ + ∑ j, ‖u j • column K D (some j)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ ‖column K D none‖ + ∑ j, M * ‖column K D (some j)‖ := by
      gcongr with j
      simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hM j) (norm_nonneg (column K D (some j)))
    _ = _ := by rw [Finset.mul_sum]

def biasLinear (K D : ℕ) : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] Parameters K D where
  toFun b := WithLp.toLp 2 (fun ij => match ij.2 with | none => b ij.1 | some _ => 0)
  map_add' u v := by ext ⟨i,j⟩; cases j <;> simp
  map_smul' c w := by ext ⟨i,j⟩; cases j <;> simp

theorem bias_norm (K D : ℕ) (b : EuclideanSpace ℝ (Fin K)) :
    ‖biasLinear K D b‖ = ‖b‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_option, biasLinear]

def bias (K D : ℕ) : EuclideanSpace ℝ (Fin K) →L[ℝ] Parameters K D :=
  (biasLinear K D).mkContinuous 1 (fun b => by simp [bias_norm])

theorem bias_norm_le (K D : ℕ) : ‖bias K D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  simp [bias, bias_norm]

theorem decoder_bias (K D : ℕ) (u : Fin D → ℝ) :
    (decoder K D u).comp (bias K D) = ContinuousLinearMap.id ℝ _ := by
  ext b i
  simp [decoder_apply, bias, biasLinear]

end Qatlib.Papers.LatentPQCTran26.MainResults.EuclideanLayer
