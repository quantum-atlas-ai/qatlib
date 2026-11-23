/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Euclidean regularity of the AMP coordinates

The field and history together form one Euclidean vector, with the new field in the first
coordinate. The update in [GohMuller2026], Equation (24), is a continuous linear functional.
Its exact operator norm gives the catalyst bound of Equation (32) and a common constant for
the two coordinate maps in Assumption 2.1. These estimates apply on the entire Euclidean domain.

[arXiv:2609.35131v1](https://arxiv.org/abs/2609.35131v1)
-/

set_option autoImplicit false

open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics

/-- The coefficient vector of the update, in field-then-history coordinates. -/
noncomputable def ampUpdateCoefficients (s : ℝ) (t : ℕ) :
    EuclideanSpace ℝ (Fin (t + 2)) :=
  EuclideanSpace.single 0 1 + EuclideanSpace.single (Fin.succ 0) (s ^ 2 * (1 - s))

/-- The continuous linear functional implementing the actual affine AMP update, with the field
followed by the `t + 1` history coordinates. -/
noncomputable def ampUpdateOperator (s : ℝ) (t : ℕ) :
    EuclideanSpace ℝ (Fin (t + 2)) →L[ℝ] ℝ :=
  innerSL ℝ (ampUpdateCoefficients s t)

/-- The field is stored at index zero and the history starts with the catalyst coordinate. -/
theorem ampUpdateOperator_apply (s : ℝ) (t : ℕ) (z : EuclideanSpace ℝ (Fin (t + 2))) :
    ampUpdateOperator s t z = FCoord s (z 0) (fun i => z i.succ) := by
  rw [ampUpdateOperator, innerSL_apply_apply, ampUpdateCoefficients, inner_add_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp [FCoord]
  ring

/-- The exact `ℓ² → ℝ` operator norm of the update for every real schedule value. -/
theorem ampUpdateOperator_norm (s : ℝ) (t : ℕ) :
    ‖ampUpdateOperator s t‖ = Real.sqrt (1 + (s ^ 2 * (1 - s)) ^ 2) := by
  have h := ampUpdateOperator_apply s t (ampUpdateCoefficients s t)
  rw [ampUpdateOperator, innerSL_apply_apply, real_inner_self_eq_norm_sq] at h
  rw [ampUpdateOperator, innerSL_apply_norm, ← Real.sqrt_sq (norm_nonneg _), h]
  congr 1
  simp [FCoord, ampUpdateCoefficients, PiLp.add_apply]
  ring

/-- The sharp uniform operator-norm bound on the unit schedule interval, attained at `2 / 3`. -/
theorem ampUpdateOperator_norm_max (t : ℕ) :
    IsGreatest ((fun s : ℝ => ‖ampUpdateOperator s t‖) '' Set.Icc 0 1)
      (Real.sqrt (1 + (4 / 27 : ℝ) ^ 2)) := by
  refine ⟨⟨2 / 3, by constructor <;> norm_num, ?_⟩, ?_⟩
  · change ‖ampUpdateOperator (2 / 3) t‖ = _
    rw [ampUpdateOperator_norm]
    norm_num
  · rintro _ ⟨s, hs, rfl⟩
    change ‖ampUpdateOperator s t‖ ≤ _
    rw [ampUpdateOperator_norm]
    obtain ⟨hc₀, hc⟩ := catalyst_coefficient_bounds s hs
    exact Real.sqrt_le_sqrt (add_le_add le_rfl (pow_le_pow_left₀ hc₀ hc 2))

/-- A single positive constant controls the two actual coordinate maps throughout horizon `T`.
The histories use the Euclidean norm and the update uses the Euclidean norm of the field and
history together. The spin readout also vanishes at the zero history. -/
theorem euclidean_assumption21 (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ t ≤ T, s t ∈ Set.Icc (0 : ℝ) 1) :
    let K := max (2 * Real.sqrt (T : ℝ)) (Real.sqrt (1 + (4 / 27 : ℝ) ^ 2))
    0 < K ∧ ∀ t ≤ T,
      fCoord s t (fun _ => 0) = 0 ∧
      (∀ u v : EuclideanSpace ℝ (Fin (t + 1)),
        |fCoord s t u.ofLp - fCoord s t v.ofLp| ≤ K * ‖u - v‖) ∧
      (∀ x y : EuclideanSpace ℝ (Fin (t + 2)),
        |FCoord (s t) (x 0) (fun i => x i.succ) - FCoord (s t) (y 0) (fun i => y i.succ)| ≤
          K * ‖x - y‖) := by
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity) (le_max_right _ _), fun t ht => ⟨fCoord_zero s t, ?_, ?_⟩⟩
  · intro u v
    have hun : Real.sqrt (∑ a, (u.ofLp a - v.ofLp a) ^ 2) = ‖u - v‖ := by
      calc
        _ = Real.sqrt (∑ a, ((u - v) a) ^ 2) := by simp only [PiLp.sub_apply]
        _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
    rw [← hun]
    exact (fCoord_lipschitz_l2 s T t ht hs u.ofLp v.ofLp).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · intro x y
    rw [← ampUpdateOperator_apply, ← ampUpdateOperator_apply, ← map_sub, ← Real.norm_eq_abs]
    have hnorm := (ampUpdateOperator_norm_max t).2 ⟨s t, hs t ht, rfl⟩
    exact ((ampUpdateOperator (s t) t).le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_right (hnorm.trans (le_max_right _ _)) (norm_nonneg _))

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics
