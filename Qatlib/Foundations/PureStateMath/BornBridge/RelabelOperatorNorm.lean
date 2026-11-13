/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Operator norm invariance under basis relabeling

This module proves that relabeling a finite basis preserves the Euclidean norm of a state and
the induced ℓ² operator norm of a matrix. It also preserves distances between matrices,
including a swap of tensor registers; these are coordinate-invariance properties of the operator
norm [Bhatia1997].

## Main statements

* `norm_toEuclidean_relabelState`: Relabeling preserves the Euclidean state norm.
* `l2_norm_relabelGate`: Relabeling preserves the ℓ² operator norm.
* `l2_norm_swap_registers_sub`: Swapping registers preserves operator-norm distance.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.BornBridge

open Matrix

open scoped Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Relabeling a finite state basis by an equivalence preserves its Euclidean ℓ² norm. -/
theorem norm_toEuclidean_relabelState (e : I ≃ J) (w : QState I) :
    ‖toEuclidean_fromVec (relabelState e w)‖ = ‖toEuclidean_fromVec w‖ := by
  have hsq : ‖toEuclidean_fromVec (relabelState e w)‖ ^ 2 = ‖toEuclidean_fromVec w‖ ^ 2 := by
    rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, inner_relabelState]
  calc ‖toEuclidean_fromVec (relabelState e w)‖
      = Real.sqrt (‖toEuclidean_fromVec (relabelState e w)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖toEuclidean_fromVec w‖ ^ 2) := by rw [hsq]
    _ = ‖toEuclidean_fromVec w‖ := Real.sqrt_sq (norm_nonneg _)

/-- Relabeling a matrix basis by an equivalence does not increase its induced ℓ² operator norm. -/
theorem l2_opNorm_relabelGate_le (e : I ≃ J) (N : Matrix I I ℂ) :
    ‖relabelGate e N‖ ≤ ‖N‖ := by
  have hround2 : ∀ s : QState J, relabelState e (relabelState e.symm s) = s := by
    intro s
    funext j
    simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hbound : ∀ x : EuclideanSpace ℂ J,
      ‖toEuclidean_fromVec (relabelState e
          (ApplyGate N (relabelState e.symm (toVec_fromEuclidean x))))‖ ≤ ‖N‖ * ‖x‖ := by
    intro x
    calc ‖toEuclidean_fromVec (relabelState e
            (ApplyGate N (relabelState e.symm (toVec_fromEuclidean x))))‖
        = ‖toEuclidean_fromVec (ApplyGate N (relabelState e.symm (toVec_fromEuclidean x)))‖ :=
          norm_toEuclidean_relabelState e _
      _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
            (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) N
              (toEuclidean_fromVec (relabelState e.symm (toVec_fromEuclidean x)))‖ :=
          (congrArg (fun v : EuclideanSpace ℂ I => ‖v‖)
            (toEuclideanCLM_applyGate N (relabelState e.symm (toVec_fromEuclidean x)))).symm
      _ ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
            (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) N‖
            * ‖toEuclidean_fromVec (relabelState e.symm (toVec_fromEuclidean x))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖N‖ * ‖toEuclidean_fromVec (relabelState e.symm (toVec_fromEuclidean x))‖ := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]
      _ = ‖N‖ * ‖x‖ := by
          rw [norm_toEuclidean_relabelState e.symm, toEuclidean_fromVec_toVec_fromEuclidean]
  have hclm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix J J ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)) (relabelGate e N)‖ ≤ ‖N‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hstep : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix J J ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)) (relabelGate e N) x‖
        = ‖toEuclidean_fromVec (ApplyGate (relabelGate e N) (toVec_fromEuclidean x))‖ :=
        congrArg (fun v : EuclideanSpace ℂ J => ‖v‖)
          (toEuclideanCLM_applyGate (relabelGate e N) (toVec_fromEuclidean x))
    rw [hstep, (hround2 (toVec_fromEuclidean x)).symm, applyGate_relabelGate]
    exact hbound x
  calc ‖relabelGate e N‖
      = ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix J J ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)) (relabelGate e N)‖ :=
        (Matrix.l2_opNorm_toEuclideanCLM _).symm
    _ ≤ ‖N‖ := hclm

/-- Relabeling a matrix basis by an equivalence preserves its induced ℓ² operator norm. -/
theorem l2_norm_relabelGate (e : I ≃ J) (N : Matrix I I ℂ) :
    ‖relabelGate e N‖ = ‖N‖ :=
  le_antisymm (l2_opNorm_relabelGate_le e N)
    (by
      have h := l2_opNorm_relabelGate_le e.symm (relabelGate e N)
      rwa [relabelGate_relabelGate] at h)

/-- Simultaneously relabeling two matrices preserves the induced ℓ² operator norm of their
difference. -/
theorem l2_norm_relabelGate_sub (e : I ≃ J) (A B : Matrix I I ℂ) :
    ‖relabelGate e A - relabelGate e B‖ = ‖A - B‖ := by
  have hsub : relabelGate e A - relabelGate e B = relabelGate e (A - B) := by
    ext i j
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
  rw [hsub, l2_norm_relabelGate]

/-- Swapping the two tensor-register indices of two matrices preserves their induced ℓ²
operator-norm distance. -/
theorem l2_norm_swap_registers_sub (A B : Matrix (I × J) (I × J) ℂ) :
    ‖relabelGate (Equiv.prodComm I J) A - relabelGate (Equiv.prodComm I J) B‖
      = ‖A - B‖ :=
  l2_norm_relabelGate_sub (Equiv.prodComm I J) A B

end Qatlib.Foundations.PureStateMath.BornBridge
