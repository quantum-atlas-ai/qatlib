/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation.TrajectorySeparation
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Expected gaps along finite random gradient trajectories

`expectedGap` averages the cost gap of actual gradient-descent trajectories over a finite
probability mass function on initial conditions. A bound on the expected squared gradient norm
controls per-step expected descent and yields a lower bound on the steps needed to reach a
target expected gap, alongside the conditional PL precision guarantee.

This development follows [YaoEtAl2026].

## Main statements

* `expectedGap_step`: expected squared-gradient control bounds expected descent.
* `lemma4_finite_trajectory_steps`: the endpoint gaps imply a step lower bound.
* `theorem2_finite_separation`: the PL precision guarantee and finite-trajectory lower bound
  hold together.

## References

* [Yao et al., 2026][YaoEtAl2026]
-/

set_option autoImplicit false
noncomputable section
open scoped Gradient BigOperators
namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation
open Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent
open Qatlib.Papers.DissipVarFw26.FrameworkCost.PL
open Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype Ω]

/-- The finite probability-weighted average of `C (gdIter C η (initial ω) t) - Cstar` over the
initial conditions. -/
def expectedGap (law : PMF Ω) (C : E → ℝ) (η Cstar : ℝ) (initial : Ω → E)
    (t : ℕ) : ℝ :=
  ∑ ω, (law ω).toReal * (C (gdIter C η (initial ω) t) - Cstar)

/-- For positive `β`, `SmoothGrad C β`, and `0 < η ≤ 1 / β`, an expected squared-gradient bound
`G` at time `t` bounds the decrease in expected gap by `(3 * η / 2) * G`. -/
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

/-- Under smoothness, a permitted positive step size, and an expected squared-gradient bound `G
> 0` before time `T`, initial expected gap at least `δ0` and terminal expected gap at most
`ε` imply `2 * (δ0 - ε) / (3 * η * G) ≤ T`. See [YaoEtAl2026]. -/
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

/-- Under the stated smoothness and PL hypotheses for `Cd` and finite-trajectory gradient bounds
for `Cu`, the `Cd` precision iterate reaches gap at most `ε` while the `Cu` trajectory
length is at least `2 * (δ0 - ε) / (3 * ηu * G)`. See [YaoEtAl2026]. -/
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
