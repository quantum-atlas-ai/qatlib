/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.MistakeUpdates
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Qatlib.Papers.QPerceptron16.UpdateRun
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open Qatlib.Concepts.LinearLearning.MistakeUpdates
variable {N d : ℕ}

abbrev Feature (d : ℕ) := EuclideanSpace ℝ (Fin d)

def labelSign (labels : Fin N → Bool) (i : Fin N) : ℝ := if labels i then 1 else -1

def trainingData (features : Fin N → Feature d) (labels : Fin N → Bool) : Dataset N (Feature d) :=
  ⟨features,labels⟩

theorem coordinate_score (features : Fin N → Feature d) (labels : Fin N → Bool)
    (w : Feature d) (i : Fin N) :
    ⟪w,signedDatum (trainingData features labels) i⟫_ℝ =
      labelSign labels i * ∑ j,w j*features i j := by
  unfold signedDatum trainingData labelSign
  split_ifs <;> simp [inner_neg_right,PiLp.inner_apply,mul_comm]

theorem native_mistake_predicate (features : Fin N → Feature d) (labels : Fin N → Bool)
    (w : Feature d) (i : Fin N) :
    i∈mistakes (trainingData features labels) w ↔ labelSign labels i*(∑ j,w j*features i j)≤0 := by
  rw [mem_mistakes,coordinate_score]

theorem native_update (features : Fin N → Feature d) (labels : Fin N → Bool) (n : ℕ)
    (h : (mistakes (trainingData features labels) (run (trainingData features labels) n)).Nonempty) :
    run (trainingData features labels) (n+1)=run (trainingData features labels) n+
      labelSign labels ((mistakes (trainingData features labels) (run (trainingData features labels) n)).min' h) •
        features ((mistakes (trainingData features labels) (run (trainingData features labels) n)).min' h) := by
  rw [run,increment,dif_pos h]
  congr 1
  unfold signedDatum trainingData labelSign
  split_ifs <;> simp

def output (features : Fin N → Feature d) (labels : Fin N → Bool) (γ : ℝ) : Feature d :=
  run (trainingData features labels) (verificationBudget γ)

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
