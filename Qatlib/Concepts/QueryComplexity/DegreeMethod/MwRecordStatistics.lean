/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwAlternating
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
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
set_option warningAsError false
noncomputable section

def bernoulli (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by cases b <;> dsimp <;> linarith [hp.1, hp.2]
  sum_one := by simp

def recordLaw (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist (Fin n → Bool) :=
  independent fun _ => bernoulli p hp

def agreements {n : ℕ} (z : Fin n → Bool) : ℝ := ∑ i, if z i then 1 else 0

theorem recordWeight_ofFn {n : ℕ} (p : ℝ) (z : Fin n → Bool) :
    recordWeight p (List.ofFn z) = ∏ i, if z i then p else 1 - p := by
  have h (zs : List Bool) : recordWeight p zs = (zs.map fun b => if b then p else 1 - p).prod := by
    induction zs with
    | nil => rfl
    | cons b zs ih => simp only [recordWeight, List.map_cons, List.prod_cons, ih]
  rw [h, List.map_ofFn, List.prod_ofFn]
  rfl

variable {H : Type} [Fintype H] [DecidableEq H]

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

def recordEvent (P Q : Matrix H H ℂ) (ψ : QState H) (n : ℕ)
    (event : (Fin n → Bool) → Prop) : ℝ :=
  ∑ z ∈ Finset.univ.filter event,
    MeasureProb (branchState Q P (List.ofFn z) ψ) Finset.univ

theorem record_event_probability (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) (event : (Fin n → Bool) → Prop) :
    recordEvent P Q ψ n event = eventMass (recordLaw n p hp) event := by
  exact Finset.sum_congr rfl fun z _ => record_probability P Q hP hQ ψ p hp hfix heig hψ z

theorem record_total (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hfix : Q *ᵥ ψ = ψ) (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ)
    (hψ : Normalized ψ) (n : ℕ) :
    ∑ z : Fin n → Bool, MeasureProb (branchState Q P (List.ofFn z) ψ) Finset.univ = 1 := by
  simp_rw [record_probability P Q hP hQ ψ p hp hfix heig hψ]
  exact (recordLaw n p hp).sum_one

theorem record_expectation (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (recordLaw n p hp).expect agreements = n * p := by
  have he : @agreements n = weightedSum (fun _ : Fin n => (1 : ℝ))
      (fun _ b => if b then (1 : ℝ) else 0) := by
    funext z
    simp [agreements, weightedSum]
  rw [he, recordLaw, ProbabilityInterfaces.independent_weighted_expectation]
  simp [bernoulli, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect]

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
