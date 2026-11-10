/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.ClassicalAnalogue
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

namespace WalkStructure

variable {X : Type*} [Fintype X]

def sqrtPi (D : WalkStructure X) (x : X) : ℝ := Real.sqrt (D.π x)

def disc (s : X → ℝ) (p : X → X → ℝ) : Matrix X X ℝ := fun x y => s x * p x y / s y

theorem disc_eq_quantum (D : WalkStructure X) (hπ : ∀ x, 0 < D.π x)
    (h : D.swapFixed) :
    disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2) =
      (fun x y => D.φ y x * D.φ x y) := by
  funext x y
  have hsy : Real.sqrt (D.π y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hπ y))
  have hrev : Real.sqrt (D.π x) * D.φ x y = Real.sqrt (D.π y) * D.φ y x := by
    have h1 := D.w_φ x y
    have h2 := D.w_φ y x
    have h3 := h x y
    rw [h1, h2] at h3
    exact h3
  simp only [disc, sqrtPi]
  field_simp [hsy]
  calc Real.sqrt (D.π x) * D.φ x y ^ 2
      = (Real.sqrt (D.π x) * D.φ x y) * D.φ x y := by ring
    _ = (Real.sqrt (D.π y) * D.φ y x) * D.φ x y := by rw [hrev]
    _ = D.φ x y * Real.sqrt (D.π y) * D.φ y x := by ring

theorem disc_mulVec_similar (s : X → ℝ) (hs : ∀ x, s x ≠ 0)
    (p : Matrix X X ℝ) (v : X → ℝ) (μ : ℝ)
    (hpv : p.mulVec v = μ • v) :
    (disc s p).mulVec (fun x => s x * v x) = μ • (fun x => s x * v x) := by
  ext x
  simp only [disc, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ y, s x * p x y / s y * (s y * v y)) =
      s x * ∑ y, p x y * v y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by field_simp [hs y])
  have hx := congrFun hpv x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
  rw [hsum, hx]
  ring

theorem theorem_3_18_discriminant (D : WalkStructure X) (hπ : ∀ x, 0 < D.π x)
    (h : D.swapFixed) (v : X → ℝ) (μ : ℝ)
    (hpv : (Matrix.of (fun x y => (D.φ x y) ^ 2)).mulVec v = μ • v) :
    disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2) =
        (fun x y => D.φ y x * D.φ x y) ∧
      (disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2)).mulVec
          (fun x => sqrtPi D x * v x) = μ • (fun x => sqrtPi D x * v x) := by
  refine ⟨disc_eq_quantum D hπ h, ?_⟩
  exact disc_mulVec_similar (sqrtPi D)
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (hπ x))) _ _ _ hpv

end WalkStructure

end Qatlib.Papers.HittingTimes08.MainResults
