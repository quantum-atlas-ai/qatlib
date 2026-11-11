/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.SignedCollisionStatistics
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Signed collision estimators and Born records

This module applies pair U-statistics to signed collision kernels for mean squared residuals. It
proves exact mean, variance, and pair-evaluation formulas and realizes the signed record law as
the Born distribution of a normalized state, connecting received records with nonlinear quantum
estimation [HuangKuengPreskill2020].

## Main statements

* `actual_mean`: unbiased estimation of `residualMean`.
* `actual_variance`: exact pair U-statistic error formula.
* `born_record_mass`: the signed record law as a Born distribution.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator
open Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics
open scoped BigOperators
noncomputable section
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- The uniform mean over labels of the squared residual `a * m x - b * u x`. -/
def residualMean (m u : S → ℝ) (a b : ℝ) : ℝ :=
  (∑ x, (a*m x-b*u x)^2)/(Fintype.card S : ℝ)

/-- The residual collision kernel is symmetric in its two signed records. -/
theorem collision_symmetric (u : S → ℝ) (a b : ℝ) (x y : S × Bool) :
    Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u x y = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u y x := by
  by_cases h : x.1=y.1
  · simp only [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision, h, if_true]
    ring
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision, h,
      Ne.symm h]

/-- For at least two independent signed records, the residual collision U-statistic has
expectation equal to `residualMean`. -/
theorem actual_mean (m u : S → ℝ) (a b : ℝ) (hm : ∀ x, |m x| ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ w : Fin n → S × Bool, (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).probOf w *
      Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w) = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean m u a b := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.finite_pair_u_statistic_unbiased (S × Bool) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) n _ hn]
  simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.mul_sum, mul_assoc, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean] using
    Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residual_collision_unbiased m u a b hm

/-- The mean squared error of the residual collision U-statistic has the exact
conditional-variance and kernel-variance decomposition with coefficients `4 * (n - 2) / (n *
(n - 1))` and `2 / (n * (n - 1))`. -/
theorem actual_variance (m u : S → ℝ) (a b : ℝ) (hm : ∀ x, |m x| ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ w : Fin n → S × Bool, (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).probOf w *
      (Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w-Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean m u a b)^2) =
      (4*(n-2 : ℕ) : ℝ)/((n : ℝ)*(n-1 : ℕ))*
        Qatlib.Concepts.ShadowModels.UStatBackend.pairConditionalVariance (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) +
      2/((n : ℝ)*(n-1 : ℕ))*Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelVariance (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) := by
  have hmean : Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean m u a b :=
    by simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.mul_sum, mul_assoc, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.residualMean] using
      Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residual_collision_unbiased m u a b hm
  simpa only [hmean] using Qatlib.Concepts.ShadowModels.UStatBackend.finite_pair_u_statistic_exact_variance (S × Bool)
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm) n (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) hn (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.collision_symmetric u a b)

/-- The counted residual collision evaluator returns the pair U-statistic and uses exactly
`n.choose 2` kernel evaluations. -/
theorem actual_value_and_count (u : S → ℝ) (a b : ℝ) (n : ℕ) (w : Fin n → S × Bool) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.pairUCounted (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w).1 = Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w ∧
      (Qatlib.Concepts.ShadowModels.UStatBackend.pairUCounted (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w).2 = n.choose 2 :=
  Qatlib.Concepts.ShadowModels.UStatBackend.finite_pair_u_statistic_actual_value_and_count (S × Bool) n (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision a b u) w

/-- The state on label-bit pairs obtained by assigning each label's qubit state the
uniform-label amplitude factor `1 / sqrt (Fintype.card S)`. -/
def recordState (v : S → Qatlib.Foundations.PureStateMath.QState Bool) : Qatlib.Foundations.PureStateMath.QState (S × Bool) :=
  fun r => (((Real.sqrt (Fintype.card S : ℝ))⁻¹ : ℝ) : ℂ) * v r.1 r.2

/-- The difference between the squared magnitudes of the false and true amplitudes of each
label's qubit state. -/
def signal (v : S → Qatlib.Foundations.PureStateMath.QState Bool) (x : S) : ℝ :=
    ‖v x false‖^2-‖v x true‖^2

/-- For normalized qubit states, the signal at every label has absolute value at most one. -/
theorem signal_bounds (v : S → Qatlib.Foundations.PureStateMath.QState Bool) (hv : ∀ x, Qatlib.Foundations.PureStateMath.Normalized (v x)) :
    ∀ x, |signal v x| ≤ 1 := by
  intro x
  have hs : ‖v x true‖^2+‖v x false‖^2=1 := by
    simpa only [Qatlib.Foundations.PureStateMath.Normalized,Fintype.sum_bool] using hv x
  apply abs_le.mpr
  dsimp [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal]
  constructor <;> nlinarith [sq_nonneg ‖v x true‖,sq_nonneg ‖v x false‖]

/-- For normalized local qubit states, the Born mass of `recordState` equals the signed record
law with signal `signal v`. -/
theorem born_record_mass (v : S → Qatlib.Foundations.PureStateMath.QState Bool) (hv : ∀ x, Qatlib.Foundations.PureStateMath.Normalized (v x)) (r : S × Bool) :
    Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.recordState v) r = (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal v) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal_bounds v hv)).prob r := by
  have hM : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : ‖v r.1 true‖^2+‖v r.1 false‖^2=1 := by
    simpa only [Qatlib.Foundations.PureStateMath.Normalized,Fintype.sum_bool] using hv r.1
  have hn : ‖(((Real.sqrt (Fintype.card S : ℝ))⁻¹ : ℝ) : ℂ)‖^2 = (Fintype.card S : ℝ)⁻¹ := by
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hM.le]
  change ‖(((Real.sqrt (Fintype.card S : ℝ))⁻¹ : ℝ) : ℂ)*v r.1 r.2‖^2 = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal v) r
  rw [norm_mul,mul_pow,hn]
  rcases r with ⟨x,b⟩
  cases b <;> dsimp
      [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal,Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign] at * <;> field_simp <;> nlinarith

/-- Uniformly combining normalized local qubit states in `recordState` gives a normalized state. -/
theorem record_normalized (v : S → Qatlib.Foundations.PureStateMath.QState Bool) (hv : ∀ x, Qatlib.Foundations.PureStateMath.Normalized (v x)) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.recordState v) := by
  change (∑ r,
      Qatlib.Foundations.PureStateMath.BornProb
      (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.recordState v) r)=1
  simp_rw [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.born_record_mass v hv]
  exact (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal v) (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator.signal_bounds v hv)).sum_one
end
end Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionEstimator
