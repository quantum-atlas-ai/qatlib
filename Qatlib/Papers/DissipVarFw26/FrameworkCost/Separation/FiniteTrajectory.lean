/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation.TrajectorySeparation
import Mathlib.Probability.ProbabilityMassFunction.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Gradient BigOperators
namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation
open Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent
open Qatlib.Papers.DissipVarFw26.FrameworkCost.PL
open Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype Ω]

def expectedGap (law : PMF Ω) (C : E → ℝ) (η Cstar : ℝ) (initial : Ω → E)
    (t : ℕ) : ℝ :=
  ∑ ω, (law ω).toReal * (C (gdIter C η (initial ω) t) - Cstar)

theorem expectedGap_step (law : PMF Ω) (C : E → ℝ) (β η Cstar G : ℝ)
    (initial : Ω → E) (hβ : 0 < β) (hsmooth : SmoothGrad C β)
    (hη : 0 < η) (hηβ : η ≤ 1 / β) (t : ℕ)
    (hflat : (∑ ω, (law ω).toReal * ‖∇ C (gdIter C η (initial ω) t)‖ ^ 2) ≤ G) :
    expectedGap law C η Cstar initial t - expectedGap law C η Cstar initial (t + 1) ≤
      (3 * η / 2) * G := by
  unfold expectedGap
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ ω, ((law ω).toReal * (C (gdIter C η (initial ω) t) - Cstar) -
      (law ω).toReal * (C (gdIter C η (initial ω) (t + 1)) - Cstar)) =
        ∑ ω, (law ω).toReal * (C (gdIter C η (initial ω) t) -
          C (gdIter C η (initial ω) t - η • ∇ C (gdIter C η (initial ω) t))) := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [gdIter]
            ring
    _ ≤ ∑ ω, (law ω).toReal * ((3 * η / 2) * ‖∇ C (gdIter C η (initial ω) t)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (lemma2_descent_upper C β η hβ hsmooth hη hηβ _) ENNReal.toReal_nonneg
    _ = (3 * η / 2) * ∑ ω, (law ω).toReal * ‖∇ C (gdIter C η (initial ω) t)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ (3 * η / 2) * G := mul_le_mul_of_nonneg_left hflat (by positivity)

theorem lemma4_finite_trajectory_steps (law : PMF Ω) (C : E → ℝ)
    (β η Cstar G δ0 ε : ℝ) (initial : Ω → E) (T : ℕ)
    (hβ : 0 < β) (hsmooth : SmoothGrad C β) (hη : 0 < η)
    (hηβ : η ≤ 1 / β) (hG : 0 < G)
    (hflat : ∀ t, t < T →
      (∑ ω, (law ω).toReal * ‖∇ C (gdIter C η (initial ω) t)‖ ^ 2) ≤ G)
    (h0 : δ0 ≤ expectedGap law C η Cstar initial 0)
    (hT : expectedGap law C η Cstar initial T ≤ ε) :
    (2 * (δ0 - ε)) / (3 * η * G) ≤ (T : ℝ) := by
  apply lemma4_trajectory_flat_steps (expectedGap law C η Cstar initial) η G δ0 ε T
    hη hG _ h0 hT
  intro t ht
  exact expectedGap_step law C β η Cstar G initial hβ hsmooth hη hηβ t (hflat t ht)

theorem theorem2_finite_separation
    (Cd Cu : E → ℝ) (βd μd Cds : ℝ) (hβd : 0 < βd)
    (hsd : SmoothGrad Cd βd) (hpl : PLCond Cd μd Cds) (hmin : ∀ x, Cds ≤ Cd x)
    (hμ : 0 < μd) (hμβ : μd ≤ βd) (θd : E) (ε : ℝ)
    (hΔ : 0 < Cd θd - Cds) (hε : 0 < ε)
    (law : PMF Ω) (βu ηu Cus G δ0 : ℝ) (initial : Ω → E) (T : ℕ)
    (hβu : 0 < βu) (hsu : SmoothGrad Cu βu) (hη : 0 < ηu)
    (hηβ : ηu ≤ 1 / βu) (hG : 0 < G)
    (hflat : ∀ t, t < T →
      (∑ ω, (law ω).toReal * ‖∇ Cu (gdIter Cu ηu (initial ω) t)‖ ^ 2) ≤ G)
    (h0 : δ0 ≤ expectedGap law Cu ηu Cus initial 0)
    (hT : expectedGap law Cu ηu Cus initial T ≤ ε) :
    Cd (gdIter Cd (1 / βd) θd (precisionSteps βd μd (Cd θd - Cds) ε)) - Cds ≤ ε ∧
      (2 * (δ0 - ε)) / (3 * ηu * G) ≤ (T : ℝ) :=
  ⟨theorem1_actual_precision Cd βd μd Cds hβd hsd hpl hmin hμ hμβ θd hΔ ε hε,
   lemma4_finite_trajectory_steps law Cu βu ηu Cus G δ0 ε initial T
     hβu hsu hη hηβ hG hflat h0 hT⟩

end Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation
