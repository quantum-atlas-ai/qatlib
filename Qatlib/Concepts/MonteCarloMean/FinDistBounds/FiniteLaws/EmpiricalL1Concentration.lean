/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1Concentration
open scoped BigOperators
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def histogram {n : ℕ} (ω : Fin n → X) (x : X) : ℝ :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun y => if y = x then 1 else 0) ω

def deviation {n : ℕ} (target : X → ℝ) (ω : Fin n → X) : ℝ :=
  ∑ x, |histogram ω x - target x|

theorem coordinate_difference {n : ℕ} (hn : 0 < n) (target : X → ℝ)
    (ω τ : Fin n → X) (i : Fin n) (h : ∀ j, j ≠ i → ω j = τ j) :
    |deviation target ω - deviation target τ| ≤ 2 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpoint (x : X) :
      abs (abs (histogram ω x-target x)-abs (histogram τ x-target x)) ≤
        |histogram ω x-histogram τ x| := by
    simpa only [sub_sub_sub_cancel_right] using
      abs_abs_sub_abs_le_abs_sub (histogram ω x-target x) (histogram τ x-target x)
  have hdiff (x : X) : |histogram ω x-histogram τ x| =
      |(if ω i=x then (1 : ℝ) else 0)-(if τ i=x then 1 else 0)|/(n : ℝ) := by
    rw [histogram, histogram, Qatlib.Concepts.SketchArith.SketchBuild.finite_avg_coordinate_difference n _ ω τ i h,
      abs_div, abs_of_pos hnR]
  have hsum : (∑ x : X,
      |(if ω i=x then (1 : ℝ) else 0)-(if τ i=x then 1 else 0)|) ≤ 2 := by
    calc
      _ ≤ ∑ x : X, (|(if ω i=x then (1 : ℝ) else 0)|+
          |(if τ i=x then (1 : ℝ) else 0)|) :=
        Finset.sum_le_sum fun x _ => abs_sub _ _
      _ = 2 := by
        have habs (a x : X) : |(if a=x then (1 : ℝ) else 0)| =
            (if a=x then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        simp_rw [habs]
        simp [Finset.sum_add_distrib]
        norm_num
  calc
    _ = |∑ x : X, (|histogram ω x-target x|-|histogram τ x-target x|)| := by
      rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ x : X, abs (abs (histogram ω x-target x)-abs (histogram τ x-target x)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : X, |histogram ω x-histogram τ x| :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x : X,
        |(if ω i=x then (1 : ℝ) else 0)-(if τ i=x then 1 else 0)|)/(n : ℝ) := by
      simp_rw [hdiff]; rw [Finset.sum_div]
    _ ≤ 2/(n : ℝ) := div_le_div_of_nonneg_right hsum hnR.le

theorem tail (n : ℕ) (hn : 0 < n) (p : Fin n → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (target : X → ℝ) (u : ℝ) (hu : 0 < u) :
    let μ :=
        (Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw p).expect
        (deviation target)
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => μ+u ≤ deviation target ω),
      (Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw p).prob ω) ≤ Real.exp (-u^2*(n : ℝ)/2) ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => u ≤ |deviation target ω-μ|),
      (Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw p).prob ω) ≤ 2*Real.exp (-u^2*(n : ℝ)/2) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum : (∑ i : Fin n, (2/(n : ℝ))^2) = 4/(n : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    norm_num
  have he : -2*u^2/(4/(n : ℝ)) = -u^2*(n : ℝ)/2 := by
    field_simp; ring
  have ht := Qatlib.Concepts.SketchArith.SketchBuild.finite_product_bounded_differences_tail X n p (deviation target)
    (fun _ => 2/(n : ℝ)) u (fun _ => by positivity)
    (by rw [hsum]; positivity) hu
    (fun i ω τ h => coordinate_difference hn target ω τ i h)
  simpa only [hsum, he] using ht

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1Concentration
