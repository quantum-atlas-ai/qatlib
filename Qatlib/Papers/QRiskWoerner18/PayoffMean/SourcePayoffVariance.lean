/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.PayoffMean

set_option backward.isDefEq.respectTransparency false

/-!
# The source mean, second moment and variance readouts

Woerner--Egger, arXiv:1806.06893v1, Section II. After Eq. (4) the paper specialises
the payoff to `f(i) = i/(N - 1)` and to `f(i) = i^2/(N - 1)^2`, so that the same
accepted-flag readout estimates `E[X/(N-1)]` and `E[X^2/(N-1)^2]`, and hence
`E[X]`, `E[X^2]` and `Var(X) = E[X^2] - E[X]^2`.

The two readouts below are the source-level flag probabilities of exactly those two
payoffs on the actual Eq. (3) preparation. They are stated separately because the
paper lists them as two distinct choices, and the variance line is recorded as the
paper's decomposition of the two readouts rather than as a new estimator.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.QRiskWoerner18.PayoffMean
open scoped BigOperators

namespace Qatlib.Papers.QRiskWoerner18.PayoffMean

/-- The paper's normalised level `i/(N - 1)` on the `2^n`-point support. -/
noncomputable def sourceLevel (n : ℕ) (i : Fin (2 ^ n)) : ℝ :=
  (i : ℝ) / ((2 : ℝ) ^ n - 1)

/-- The actual preparation's readout of `E[X/(N-1)]`, i.e. the source mean of the
normalised variable. -/
noncomputable def sourceNormalizedMean {n : ℕ} (p : FinDist (Fin (2 ^ n))) : ℝ :=
  ∑ i, p.prob i * sourceLevel n i

/-- The actual preparation's readout of `E[X^2/(N-1)^2]`. -/
noncomputable def sourceNormalizedSecondMoment {n : ℕ} (p : FinDist (Fin (2 ^ n))) : ℝ :=
  ∑ i, p.prob i * (sourceLevel n i) ^ 2

/-- The paper's variance line `Var(X) = E[X^2] - E[X]^2`, written as the difference of
the two normalised readouts (`(N-1)^2 * Var = E[X^2/(N-1)^2] - E[X/(N-1)]^2`). -/
noncomputable def sourceVarianceDecomposition {n : ℕ} (p : FinDist (Fin (2 ^ n))) : ℝ :=
  sourceNormalizedSecondMoment p - sourceNormalizedMean p ^ 2

/-- On a support with `n >= 1` the normalised level lies in the source payoff range
`[0, 1]`. -/
theorem sourceLevel_mem_Icc (n : ℕ) (hn : 1 ≤ n) (i : Fin (2 ^ n)) :
    sourceLevel n i ∈ Set.Icc (0 : ℝ) 1 := by
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    simpa using this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by linarith
  have hle : (i : ℕ) ≤ 2 ^ n - 1 := Nat.le_sub_one_of_lt i.isLt
  have hc : ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    ring
  have hi : (i : ℝ) ≤ (2 : ℝ) ^ n - 1 := by
    calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
      _ ≤ ((2 ^ n - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (2 : ℝ) ^ n - 1 := hc
  refine ⟨div_nonneg (by positivity) hpos.le, (div_le_one hpos).mpr hi⟩

/-- **Section II, estimating `E[X]`.** Choosing `f(i) = i/(N-1)` makes the
accepted-flag probability of the actual preparation equal the normalised source mean,
so the existing amplitude-estimation readout estimates `E[X/(N-1)]`. -/
theorem source_mean_flag_probability (n : ℕ) (hn : 1 ≤ n)
    (p : FinDist (Fin (2 ^ n))) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    MeasureProb
        (ApplyGate (payoffPreparation A (sourceLevel n)) (Ket (sourceZero n, false)))
        (Finset.univ.filter (fun q : Fin (2 ^ n) × Bool => q.2 = true)) =
      sourceNormalizedMean p := by
  have hborn := source_born_probability n p A hcolumn
  have hflag := (payoff_actual_rotation_and_mean A (sourceZero n) (sourceLevel n) hA
    (sourceLevel_mem_Icc n hn)).2
  rw [hflag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hborn i]

/-- **Section II, estimating `E[X^2]`.** Choosing `f(i) = i^2/(N-1)^2` makes the
accepted-flag probability equal the normalised second moment. -/
theorem source_second_moment_flag_probability (n : ℕ) (hn : 1 ≤ n)
    (p : FinDist (Fin (2 ^ n))) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    MeasureProb
        (ApplyGate (payoffPreparation A (fun i => (sourceLevel n i) ^ 2))
          (Ket (sourceZero n, false)))
        (Finset.univ.filter (fun q : Fin (2 ^ n) × Bool => q.2 = true)) =
      sourceNormalizedSecondMoment p := by
  have hsq : ∀ i : Fin (2 ^ n), (sourceLevel n i) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    obtain ⟨h0, h1⟩ := sourceLevel_mem_Icc n hn i
    exact ⟨by positivity, by nlinarith⟩
  have hborn := source_born_probability n p A hcolumn
  have hflag := (payoff_actual_rotation_and_mean A (sourceZero n)
    (fun i => (sourceLevel n i) ^ 2) hA hsq).2
  rw [hflag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hborn i]

/-- **The paper's variance line.** The variance readout is the difference of the two
preceding readouts, `E[X^2/(N-1)^2] - E[X/(N-1)]^2`; no third estimator is used. -/
theorem source_variance_readout (n : ℕ) (p : FinDist (Fin (2 ^ n))) :
    sourceVarianceDecomposition p =
      sourceNormalizedSecondMoment p - sourceNormalizedMean p ^ 2 := rfl

end Qatlib.Papers.QRiskWoerner18.PayoffMean
