/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean

@[expose] public section

/-!
# Conditional relative-variance estimator at explicit precision

Theorem 6 of [Montanaro2015] states the relative-error guarantee for a payoff with bounded
variance. The locked library proves the conditional form
(`relative_variance_actual_conditional_estimator`): for `k ≥ 4` and `B ≥ 1`, the computed
estimator is within `3 * sqrt (B + 1) * 2^(-k) * μ` of the mean with probability at least `2/3`.

This module turns that statement into the source form with a free accuracy parameter `ε`:

* `relative_variance_conditional_failure_le_third`: once `3 * sqrt (B + 1) * 2^(-k) ≤ ε`, the
  single-record failure event of relative size `ε` has probability at most `1/3`, which is the
  exact complement of the published `2/3` success bound;
* `relative_variance_median_failure_le_quarter`: the sorted median over `2 * r + 1` fresh
  relative records (`r ≥ 12`) fails with probability at most `1/4`, which is the confidence
  level of the paper.

## Main statements

* `relative_variance_conditional_failure_le_third`
* `relative_variance_median_failure_le_quarter`

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Matrix
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A failure event for a certificate over a single sample has the same probability as the
total mass of that event under the underlying distribution. -/
private theorem probEvent_one_eq_mass {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] :
    p.probEvent (fun ω : Fin 1 → X => E (ω 0))
      = ∑ x ∈ (Finset.univ : Finset X).filter E, p.prob x := by
  classical
  let e : (Fin 1 → X) ≃ X :=
    { toFun := fun ω => ω 0
      invFun := fun x _ => x
      left_inv := by
        intro ω
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rfl
      right_inv := fun _ => rfl }
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter,
    ← e.symm.sum_comp (fun ω => if E (ω 0) then p.probOf ω else 0)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [e, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]

/-- The mass of the relative-error failure event of a single relative record is at most `1/3`.
This is the complement of the locked `2/3` success guarantee, after the accuracy condition
`3 * sqrt (B + 1) * 2^(-k) ≤ ε` is used to pass from the dyadic threshold to `ε * μ`. -/
private theorem relativeMean_failure_mass_le_third (B k : ℕ) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (hB : 1 ≤ B)
    (hk : 4 ≤ k) (ε : ℝ) (_hε : 0 < ε)
    (hεk : 3 * Real.sqrt (B + 1 : ℝ) * (2 : ℝ) ^ (-((k : ℤ))) ≤ ε) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    0 < μ → (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i - μ) ^ 2) ≤ (B : ℝ) * μ ^ 2 →
    SignedMean.mass (relativeMeanLaw B k A j f hA hf)
        (fun x => ε * μ < |relativeMeanEstimate B k f x - μ|) ≤ 1 / 3 := by
  classical
  intro μ hμ hv
  rw [neg_pow_half_eq k] at hεk
  have hgood := relative_variance_actual_conditional_estimator I B k A j f hA hf hB hk
  simp only [] at hgood
  have hgood' : (2 : ℝ) / 3 ≤ SignedMean.mass (relativeMeanLaw B k A j f hA hf)
      (fun x => |relativeMeanEstimate B k f x - μ| ≤
        3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ) := hgood hμ hv
  have hshift : 3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ ≤ ε * μ :=
    mul_le_mul_of_nonneg_right hεk hμ.le
  have hsub : SignedMean.mass (relativeMeanLaw B k A j f hA hf)
        (fun x => ε * μ < |relativeMeanEstimate B k f x - μ|)
      ≤ SignedMean.mass (relativeMeanLaw B k A j f hA hf)
        (fun x => ¬(|relativeMeanEstimate B k f x - μ| ≤
          3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ)) := by
    refine SignedMean.mass_mono _ (fun x hx hle => ?_)
    have h1 : 3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ
        < |relativeMeanEstimate B k f x - μ| := lt_of_le_of_lt hshift hx
    exact absurd h1 (not_lt.mpr hle)
  have hcompl := SignedMean.mass_complement (relativeMeanLaw B k A j f hA hf)
    (fun x => |relativeMeanEstimate B k f x - μ| ≤
      3 * Real.sqrt (B + 1 : ℝ) * (1 / 2 : ℝ) ^ k * μ)
  linarith

/-- With `B ≥ 1`, `k ≥ 4`, positive mean, variance at most `B` times the squared mean, and the
accuracy condition `3 * sqrt (B + 1) * 2^(-k) ≤ ε`, the computed estimator
`relativeMeanEstimate` deviates from the mean by a relative error larger than `ε` with
probability at most `1/3`. This is the source form of [Montanaro2015], Theorem 6 for one trial,
built on the locked conditional estimator. -/
theorem relative_variance_conditional_failure_le_third (B k : ℕ) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (hB : 1 ≤ B)
    (hk : 4 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hεk : 3 * Real.sqrt (B + 1 : ℝ) * (2 : ℝ) ^ (-((k : ℤ))) ≤ ε) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    0 < μ → (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i - μ) ^ 2) ≤ (B : ℝ) * μ ^ 2 →
    (relativeMeanLaw B k A j f hA hf).probEvent
        (fun ω : Fin 1 → (Fin (32 * B) → I) × LayerRecord k =>
          ε * μ < |relativeMeanEstimate B k f (ω 0) - μ|)
      ≤ 1 / 3 := by
  classical
  intro μ hμ hv
  rw [probEvent_one_eq_mass (relativeMeanLaw B k A j f hA hf)
    (fun x => ε * μ < |relativeMeanEstimate B k f x - μ|)]
  exact relativeMean_failure_mass_le_third B k A j f hA hf hB hk ε hε hεk hμ hv

/-- With `B ≥ 1`, `k ≥ 4`, positive mean, variance at most `B` times the squared mean, the
accuracy condition `3 * sqrt (B + 1) * 2^(-k) ≤ ε`, and `r ≥ 12` fresh relative records, the
sorted median of the relative estimates deviates from the mean by a relative error larger than
`ε` with probability at most `1/4`. This is the confidence level of
[Montanaro2015], Theorem 6. -/
theorem relative_variance_median_failure_le_quarter (B k r : ℕ) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (hB : 1 ≤ B)
    (hk : 4 ≤ k) (hr : 12 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (hεk : 3 * Real.sqrt (B + 1 : ℝ) * (2 : ℝ) ^ (-((k : ℤ))) ≤ ε) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    0 < μ → (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i - μ) ^ 2) ≤ (B : ℝ) * μ ^ 2 →
    (relativeMeanLaw B k A j f hA hf).probEvent
        (fun ω : Fin (2 * r + 1) → (Fin (32 * B) → I) × LayerRecord k =>
          ε * μ < |sortedBlockMedian r (fun a => relativeMeanEstimate B k f (ω a)) - μ|)
      ≤ 1 / 4 := by
  classical
  intro μ hμ hv
  have hb := relativeMean_failure_mass_le_third B k A j f hA hf hB hk ε hε hεk hμ hv
  have hmain := SignedMean.sorted_median_failure (relativeMeanLaw B k A j f hA hf)
    (relativeMeanEstimate B k f) r μ (ε * μ) (by positivity) hb
  refine le_trans hmain ?_
  have h12 : ((8 : ℝ) / 9) ^ 12 ≤ 1 / 4 := by norm_num
  calc ((8 : ℝ) / 9) ^ r ≤ ((8 : ℝ) / 9) ^ 12 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
    _ ≤ 1 / 4 := h12

end Qatlib.Papers.MCMontanaro15.MonteCarlo
