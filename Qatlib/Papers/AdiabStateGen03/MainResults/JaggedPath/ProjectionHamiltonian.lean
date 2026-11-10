/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath

open Qatlib.Papers.AdiabStateGen03.MainResults
open WithLp

variable {n : ℕ}

def projHam (v : Dim n → ℂ) : Ham n :=
  1 - Matrix.vecMulVec v (star v)

lemma projHam_apply (v : Dim n → ℂ) (i j : Dim n) :
    projHam v i j = (if i = j then (1 : ℂ) else 0) - v i * star (v j) := by
  simp only [projHam, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]

theorem projHam_isHermitian (v : Dim n → ℂ) : IsHermitian (projHam v) := by
  refine IsHermitian.ext ?_
  intro i j
  rw [projHam_apply, projHam_apply]
  by_cases h : i = j
  · subst h
    simp [mul_comm]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp [mul_comm]

lemma projHam_mulVec_apply (v w : Dim n → ℂ) (i : Dim n) :
    (projHam v *ᵥ w) i = w i - v i * (star v ⬝ᵥ w) := by
  rw [projHam, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply]
  congr 1
  simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

lemma dotProduct_star_self (v : Dim n → ℂ) :
    star v ⬝ᵥ v = (⟪toLp 2 v, toLp 2 v⟫_ℂ) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  exact (dotProduct_comm v (star v)).symm

theorem projHam_mulVec_self (v : Dim n → ℂ)
    (hv : ‖toLp 2 v‖ = 1) : projHam v *ᵥ v = 0 := by
  ext i
  rw [projHam_mulVec_apply, Pi.zero_apply]
  have h : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_star_self, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  rw [h, mul_one, sub_self]

theorem projHam_mulVec_of_orth (v w : Dim n → ℂ)
    (h : ⟪toLp 2 v, toLp 2 w⟫_ℂ = 0) :
    projHam v *ᵥ w = w := by
  ext i
  rw [projHam_mulVec_apply]
  have hz : star v ⬝ᵥ w = 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
    exact h
  rw [hz, mul_zero, sub_zero]

lemma ofLp_toOp_projHam (v : Dim n → ℂ) (x : State n) :
    ofLp (toOp (projHam v) x) = ofLp x - (⟪toLp 2 v, x⟫_ℂ) • v := by
  rw [toOp, Matrix.ofLp_toEuclideanCLM]
  ext i
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, projHam_mulVec_apply]
  have hc : star v ⬝ᵥ ofLp x = ⟪toLp 2 v, x⟫_ℂ := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, WithLp.toLp_ofLp]
  rw [hc]
  ring

lemma toOp_projHam_apply (v : Dim n → ℂ) (x : State n) :
    toOp (projHam v) x
      = x - (⟪toLp 2 v, x⟫_ℂ) • toLp 2 v := by
  have h := congrArg (fun y : Dim n → ℂ => toLp 2 y) (ofLp_toOp_projHam v x)
  simpa using h

theorem projHam_rayleigh_self (v : Dim n → ℂ)
    (hv : ‖toLp 2 v‖ = 1) :
    rayleigh (projHam v) (toLp 2 v) = 0 := by
  unfold rayleigh
  have hzero : toOp (projHam v) (toLp 2 v) = 0 := by
    rw [toOp_projHam_apply]
    have hinner : ⟪toLp 2 v, toLp 2 v⟫_ℂ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      norm_num
    rw [hinner]
    simp
  rw [hzero, inner_zero_right]
  simp

theorem projHam_rayleigh_nonneg (v : Dim n → ℂ) (x : State n)
    (hv : ‖toLp 2 v‖ = 1) :
    0 ≤ rayleigh (projHam v) x := by
  unfold rayleigh
  rw [toOp_projHam_apply]
  set c : ℂ := ⟪toLp 2 v, x⟫_ℂ with hcdef
  have hinner : ⟪x, x - c • toLp 2 v⟫_ℂ = ((‖x‖ ^ 2 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, inner_smul_right]
    have hvx : ⟪x, toLp 2 v⟫_ℂ = (starRingEnd ℂ) c := by
      rw [hcdef]
      exact (inner_conj_symm x (toLp 2 v)).symm
    rw [hvx, inner_self_eq_norm_sq_to_K, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ac_rfl
  rw [hinner]
  simp only [Complex.ofReal_re]
  have hc : ‖c‖ ≤ ‖x‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (toLp 2 v) x
    have hcv : ‖c‖ = ‖⟪toLp 2 v, x⟫_ℂ‖ := rfl
    rw [hcv]
    calc ‖⟪toLp 2 v, x⟫_ℂ‖ ≤ ‖toLp 2 v‖ * ‖x‖ := h
      _ = ‖x‖ := by rw [hv, one_mul]
  have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith [sq_nonneg ‖c‖, sq_nonneg ‖x‖, norm_nonneg c]

theorem projHam_isGroundstate (v : Dim n → ℂ)
    (hv : ‖toLp 2 v‖ = 1) :
    IsGroundstate (projHam v) (toLp 2 v) := by
  refine ⟨hv, ?_⟩
  intro φ _hφ
  rw [projHam_rayleigh_self v hv]
  exact projHam_rayleigh_nonneg v φ hv

theorem projHam_spectralGap_one (v : Dim n → ℂ)
    (hv : ‖toLp 2 v‖ = 1) :
    SpectralGapAtLeast (projHam v) (toLp 2 v) 1 := by
  intro _hgs φ hφnorm horth
  have hact : toOp (projHam v) φ = φ := by
    rw [toOp_projHam_apply, horth]
    simp
  have hray : rayleigh (projHam v) φ = 1 := by
    unfold rayleigh
    rw [hact, inner_self_eq_norm_sq_to_K, hφnorm]
    norm_num
  rw [hray, projHam_rayleigh_self v hv]
  norm_num

def convHam (η : ℝ) (v w : Dim n → ℂ) : Ham n :=
  ((1 - η : ℝ) : ℂ) • projHam v + (η : ℂ) • projHam w

theorem convHam_isHermitian (η : ℝ) (v w : Dim n → ℂ) :
    IsHermitian (convHam η v w) := by
  have h1 : IsSelfAdjoint ((1 - η : ℝ) : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  have h2 : IsSelfAdjoint ((η : ℝ) : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  unfold convHam
  exact IsHermitian.add (IsHermitian.smul (projHam_isHermitian v) h1)
    (IsHermitian.smul (projHam_isHermitian w) h2)

lemma convHam_mulVec (η : ℝ) (v w z : Dim n → ℂ) :
    convHam η v w *ᵥ z
      = ((1 - η : ℝ) : ℂ) • (projHam v *ᵥ z) + (η : ℂ) • (projHam w *ᵥ z) := by
  simp [convHam, Matrix.add_mulVec, Matrix.smul_mulVec]

end Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath
