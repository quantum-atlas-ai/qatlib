/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound.SourceLowerBound
public import Qatlib.Papers.ConvexVolEst19.MainResults.Isotropic.SourceIsotropic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section


/-!
# Boundaries of the old volume-estimation interfaces

An unconstrained conductance variable has no lower bound. The old
estimator predicate accepts exact volume output at zero query cost,
so it cannot imply a positive membership-query lower bound.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ConvexVolEst19.MainResults

open LowerBound Isotropic
open scoped BigOperators

/-- An unrestricted scalar conductance cannot satisfy any fixed universal lower bound. -/
theorem arbitrary_phi_refuted (b : ℝ) : ¬ ∀ phi : ℝ, b ≤ phi := by
  intro h
  have := h (b - 1)
  linarith

/-- The old scalar estimator predicate permits zero-query exact output. -/
theorem zero_query_estimator (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    MultiplicativeVolumeEstimator n ε 0 := by
  refine ⟨le_refl _, 1, 1, by norm_num, hε, ?_, ?_⟩
  · have hd : 0 < 1 + ε := by linarith
    rw [mul_one, div_le_one hd]
    linarith
  · norm_num
    linarith

/-- No positive scalar lower bound follows from the old estimator predicate. -/
theorem estimator_lower_bound_refuted (n : ℕ) (ε b : ℝ) (hε : 0 ≤ ε) (hb : 0 < b) :
    ¬ ∀ q : ℝ, MultiplicativeVolumeEstimator n ε q → b ≤ q := by
  intro h
  exact (not_le_of_gt hb) (h 0 (zero_query_estimator n ε hε))

/-- A factor-two covariance perturbation meets the old exponential comparison but is not near-isotropic. -/
theorem isotropic_counterexample :
    let q : (Fin 1 → ℝ) → ℝ := fun v => ∑ i, (v i) ^ 2
    let q' : (Fin 1 → ℝ) → ℝ := fun v => 2 * q v
    (∀ v, q' v ≤ Real.exp 1 * q v ∧ (1 / Real.exp 1) * q v ≤ q' v) ∧
      NearIsotropic q ∧ ¬ NearIsotropic q' := by
  dsimp only
  have he : 2 < Real.exp 1 := Real.exp_one_gt_two
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  constructor
  · intro v
    have hs : 0 ≤ ∑ i : Fin 1, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    constructor
    · nlinarith [mul_nonneg hs (sub_nonneg.mpr he.le)]
    · have hinv : (1 : ℝ) / Real.exp 1 ≤ 2 := by
        rw [div_le_iff₀ hepos]
        linarith
      exact mul_le_mul_of_nonneg_right hinv hs
  · constructor
    · intro v
      have hs : 0 ≤ ∑ i : Fin 1, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      constructor <;> nlinarith
    · intro h
      have hv := (h (fun _ => 1)).2
      norm_num at hv

end Qatlib.Papers.ConvexVolEst19.MainResults
