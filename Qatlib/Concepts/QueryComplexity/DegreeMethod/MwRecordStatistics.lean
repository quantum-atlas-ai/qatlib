/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwAlternating
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-!
# Bernoulli statistics of alternating measurement records

For a normalized clean eigenvector, agreement records of alternating projective measurements
follow the independent Bernoulli law `recordLaw`. The agreement count has expectation `n * p`,
and concentration estimates give explicit upper bounds on threshold acceptance and rejection
events.

The mathematical background is developed in [MarriottWatrous2005].

## Main statements

* `record_event_probability`: identifies record-event mass with Bernoulli event probability.
* `record_expectation`: computes the expected agreement count.
* `record_concentration`: bounds deviations of the agreement count.
* `threshold_soundness`: bounds acceptance when the threshold is separated above the eigenvalue.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators Classical
noncomputable section

/-- The Boolean probability distribution assigning probability `p` to true and `1 - p` to false. -/
def bernoulli (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by cases b <;> dsimp <;> linarith [hp.1, hp.2]
  sum_one := by simp

/-- The product distribution of `n` independent Boolean variables with success probability `p`. -/
def recordLaw (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist (Fin n → Bool) :=
  independent fun _ => bernoulli p hp

/-- The number of true agreement bits in a finite record, regarded as a real number. -/
def agreements {n : ℕ} (z : Fin n → Bool) : ℝ := ∑ i, if z i then 1 else 0

/-- The recursively defined weight of a finite-function record equals the product of its
individual Bernoulli factors. -/
theorem recordWeight_ofFn {n : ℕ} (p : ℝ) (z : Fin n → Bool) :
    recordWeight p (List.ofFn z) = ∏ i, if z i then p else 1 - p := by
  have h (zs : List Bool) : recordWeight p zs = (zs.map fun b => if b then p else 1 - p).prod := by
    induction zs with
    | nil => rfl
    | cons b zs ih => simp only [recordWeight, List.map_cons, List.prod_cons, ih]
  rw [h, List.map_ofFn, List.prod_ofFn]
  rfl

variable {H : Type} [Fintype H] [DecidableEq H]

/-- For a normalized vector fixed by `Q` with compressed eigenvalue `p`, the mass of each
length-`n` branch equals its probability under `recordLaw n p hp`. -/
theorem record_probability (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) {n : ℕ} (z : Fin n → Bool) :
    MeasureProb (branchState Q P (List.ofFn z) ψ) Finset.univ = (recordLaw n p hp).prob z := by
  rw [record_mass Q P hQ hP ψ p hfix heig, recordWeight_ofFn]
  have hm : MeasureProb ψ Finset.univ = 1 := hψ
  rw [hm, mul_one]
  rfl

/-- The sum of unnormalized branch masses over all length-`n` agreement records satisfying
`event`. -/
def recordEvent (P Q : Matrix H H ℂ) (ψ : QState H) (n : ℕ)
    (event : (Fin n → Bool) → Prop) : ℝ :=
  ∑ z ∈ Finset.univ.filter event,
    MeasureProb (branchState Q P (List.ofFn z) ψ) Finset.univ

/-- For a normalized clean eigenvector, record-event mass equals the event probability under the
independent Bernoulli record law. -/
theorem record_event_probability (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) (event : (Fin n → Bool) → Prop) :
    recordEvent P Q ψ n event = eventMass (recordLaw n p hp) event := by
  exact Finset.sum_congr rfl fun z _ => record_probability P Q hP hQ ψ p hp hfix heig hψ z

/-- For a normalized vector fixed by `Q` with compressed eigenvalue `p ∈ [0, 1]`, the total mass
of all length-`n` branches is one. -/
theorem record_total (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) :
    ∑ z : Fin n → Bool, MeasureProb (branchState Q P (List.ofFn z) ψ) Finset.univ = 1 := by
  simp_rw [record_probability P Q hP hQ ψ p hp hfix heig hψ]
  exact (recordLaw n p hp).sum_one

/-- The expected number of agreements under `recordLaw n p hp` is `n * p`. -/
theorem record_expectation (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (recordLaw n p hp).expect agreements = n * p := by
  have he : @agreements n = weightedSum (fun _ : Fin n => (1 : ℝ))
      (fun _ b => if b then (1 : ℝ) else 0) := by
    funext z
    simp [agreements, weightedSum]
  rw [he, recordLaw, ProbabilityInterfaces.independent_weighted_expectation]
  simp [bernoulli, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect]

/-- For a normalized clean eigenvector, the probability of an agreement-count deviation at least
`n * d` is at most `2 * exp (-2 * (n * d)^2 / n)` when `n, d > 0`. -/
theorem record_concentration (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 < d) :
    recordEvent P Q ψ n (fun z => n * d ≤ |agreements z - n * p|) ≤
      2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  rw [record_event_probability P Q hP hQ ψ p hp hfix heig hψ]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := independent_weighted_hoeffding
    (fun _ : Fin n => bernoulli p hp) (fun _ => 1)
    (fun _ b => if b then (1 : ℝ) else 0) (fun _ => 0) (fun _ => 1)
    (n * d) (fun _ => by norm_num) (fun _ b => by cases b <;> norm_num)
    (mul_pos hnR hd) (by simpa using! hnR)
  have he : weightedSum (fun _ : Fin n => (1 : ℝ))
      (fun _ b => if b then (1 : ℝ) else 0) = @agreements n := by
    funext z
    simp [agreements, weightedSum]
  rw [he, show (independent fun _ : Fin n => bernoulli p hp).expect agreements = n * p
    from record_expectation n p hp] at h
  simpa [recordLaw] using! h

/-- If `p + d ≤ threshold`, a normalized clean eigenvector exceeds the agreement threshold with
probability at most `2 * exp (-2 * (n * d)^2 / n)` when `n, d > 0`. -/
theorem threshold_soundness (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) (hn : 0 < n) (threshold d : ℝ)
    (hd : 0 < d) (hgap : p + d ≤ threshold) :
    recordEvent P Q ψ n (fun z => n * threshold ≤ agreements z) ≤
      2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  have hsub : ∀ z : Fin n → Bool, n * threshold ≤ agreements z →
      n * d ≤ |agreements z - n * p| := by
    intro z hz
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hg := mul_le_mul_of_nonneg_left hgap hn0
    have habs := le_abs_self (agreements z - n * p)
    nlinarith
  rw [record_event_probability P Q hP hQ ψ p hp hfix heig hψ]
  calc
    _ ≤ eventMass (recordLaw n p hp) (fun z => n * d ≤ |agreements z - n * p|) :=
      eventMass_mono _ _ _ hsub
    _ ≤ _ := by
      rw [← record_event_probability P Q hP hQ ψ p hp hfix heig hψ]
      exact record_concentration P Q hP hQ ψ p hp hfix heig hψ n hn d hd

/-- If `threshold + d ≤ p`, a normalized clean eigenvector falls below the agreement threshold
with probability at most `2 * exp (-2 * (n * d)^2 / n)` when `n, d > 0`. -/
theorem threshold_completeness (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) (hn : 0 < n) (threshold d : ℝ)
    (hd : 0 < d) (hgap : threshold + d ≤ p) :
    recordEvent P Q ψ n (fun z => agreements z < n * threshold) ≤
      2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  have hsub : ∀ z : Fin n → Bool, agreements z < n * threshold →
      n * d ≤ |agreements z - n * p| := by
    intro z hz
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hg := mul_le_mul_of_nonneg_left hgap hn0
    have habs := neg_le_abs (agreements z - n * p)
    nlinarith
  rw [record_event_probability P Q hP hQ ψ p hp hfix heig hψ]
  calc
    _ ≤ eventMass (recordLaw n p hp) (fun z => n * d ≤ |agreements z - n * p|) :=
      eventMass_mono _ _ _ hsub
    _ ≤ _ := by
      rw [← record_event_probability P Q hP hQ ψ p hp hfix heig hψ]
      exact record_concentration P Q hP hQ ψ p hp hfix heig hψ n hn d hd

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
