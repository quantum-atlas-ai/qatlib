/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.MistakeUpdates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate perceptron updates and stopping

Instantiates the abstract mistake-update process with real Euclidean feature vectors and Boolean
labels. Coordinate formulas, verified classification after the budget, and a first-stopping-time
bound express the perceptron convergence argument used in [WiebeKapoorSvore2016].

## Main statements

* `native_verified_output`: Under the unit-norm feature and positive unit-separator margin
  assumptions, the budgeted output strictly classifies every example and all subsequent iterates
  equal it [WiebeKapoorSvore2016].
* `native_first_stop`: Under the unit-norm feature and positive unit-separator margin
  assumptions, there is a first stopping index `M` with `γ^2 * M ≤ 1`, strict classification, a
  mistake at every earlier iterate, and constant subsequent iterates [WiebeKapoorSvore2016].

## References

* [Wiebe et al., 2016][WiebeKapoorSvore2016]
-/

namespace Qatlib.Papers.QPerceptron16.UpdateRun
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open Qatlib.Concepts.LinearLearning.MistakeUpdates
variable {N d : ℕ}

/-- The real Euclidean feature space of dimension `d`. -/
abbrev Feature (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The real label sign, equal to one for `true` and minus one for `false`. -/
def labelSign (labels : Fin N → Bool) (i : Fin N) : ℝ := if labels i then 1 else -1

/-- The dataset formed from the supplied feature vectors and Boolean labels. -/
def trainingData (features : Fin N → Feature d) (labels : Fin N → Bool) : Dataset N (Feature d) :=
  ⟨features,labels⟩

/-- The inner product with a signed training datum equals the label sign times the coordinate
dot product. -/
theorem coordinate_score (features : Fin N → Feature d) (labels : Fin N → Bool)
    (w : Feature d) (i : Fin N) :
    ⟪w,signedDatum (trainingData features labels) i⟫_ℝ =
      labelSign labels i * ∑ j,w j*features i j := by
  unfold signedDatum trainingData labelSign
  split_ifs <;> simp [inner_neg_right,PiLp.inner_apply,mul_comm]

/-- An example is a mistake exactly when its signed coordinate score is nonpositive. -/
theorem native_mistake_predicate (features : Fin N → Feature d) (labels : Fin N → Bool)
    (w : Feature d) (i : Fin N) :
    i∈mistakes (trainingData features labels) w ↔ labelSign labels i*(∑ j,w j*features i j)≤0 := by
  rw [mem_mistakes,coordinate_score]

/-- When mistakes remain, the next iterate adds the signed feature vector of the least mistaken
index. -/
theorem native_update (features : Fin N → Feature d) (labels : Fin N → Bool) (n : ℕ)
    (h : (mistakes (trainingData features labels) (run (trainingData features labels) n)).Nonempty) :
    run (trainingData features labels) (n+1)=run (trainingData features labels) n+
      labelSign labels ((mistakes (trainingData features labels) (run (trainingData features labels) n)).min' h) •
        features ((mistakes (trainingData features labels) (run (trainingData features labels) n)).min' h) := by
  rw [run,increment,dif_pos h]
  congr 1
  unfold signedDatum trainingData labelSign
  split_ifs <;> simp

/-- The perceptron iterate at the margin-dependent verification budget. -/
def output (features : Fin N → Feature d) (labels : Fin N → Bool) (γ : ℝ) : Feature d :=
  run (trainingData features labels) (verificationBudget γ)

/-- Under the unit-norm feature and positive unit-separator margin assumptions, the budgeted
output strictly classifies every example and all subsequent iterates equal it
[WiebeKapoorSvore2016]. -/
theorem native_verified_output (features : Fin N → Feature d) (labels : Fin N → Bool)
    (u : Feature d) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖features i‖≤1)
    (hmargin : ∀ i,γ≤labelSign labels i*(∑ j,u j*features i j)) :
    (∀ i,0<labelSign labels i*(∑ j,output features labels γ j*features i j)) ∧
      ∀ k,run (trainingData features labels) (verificationBudget γ+k)=output features labels γ := by
  have hm : ∀ i,γ≤⟪u,signedDatum (trainingData features labels) i⟫_ℝ := by
    intro i
    rw [coordinate_score]
    exact hmargin i
  obtain ⟨hs,ha⟩ := verified_output (trainingData features labels) u hu γ hγ hunit hm
  refine ⟨?_,ha⟩
  intro i
  simpa only [coordinate_score,output] using hs i

/-- Under the unit-norm feature and positive unit-separator margin assumptions, there is a first
stopping index `M` with `γ^2 * M ≤ 1`, strict classification, a mistake at every earlier
iterate, and constant subsequent iterates [WiebeKapoorSvore2016]. -/
theorem native_first_stop (features : Fin N → Feature d) (labels : Fin N → Bool)
    (u : Feature d) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖features i‖≤1)
    (hmargin : ∀ i,γ≤labelSign labels i*(∑ j,u j*features i j)) :
    ∃ M : ℕ,γ^2*(M:ℝ)≤1 ∧
      (∀ i,0<labelSign labels i*(∑ j,run (trainingData features labels) M j*features i j)) ∧
      (∀ n<M,(mistakes (trainingData features labels) (run (trainingData features labels) n)).Nonempty) ∧
      ∀ k,run (trainingData features labels) (M+k)=run (trainingData features labels) M := by
  have hm : ∀ i,γ≤⟪u,signedDatum (trainingData features labels) i⟫_ℝ := by
    intro i
    rw [coordinate_score]
    exact hmargin i
  obtain ⟨M,hM,hs,hm,ha⟩ := first_stop_bound (trainingData features labels) u hu γ hγ hunit hm
  exact ⟨M,hM,fun i => by simpa only [coordinate_score] using hs i,hm,ha⟩

end
end Qatlib.Papers.QPerceptron16.UpdateRun
