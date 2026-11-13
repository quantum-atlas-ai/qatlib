/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
import Qatlib.Concepts.NumericalWord.MixedWordError.HeterogeneousNumericalWord

/-!
# Composition and measurement error bounds

The product estimates express additive accumulation of operator errors, while
`lemma4_measurement_distance` bounds measurement probability differences by trace norm. The
mixed-word bridges apply these estimates to the precision budget, and `lemma5_error_budget`
records the corresponding total-variation triangle bound. The development follows [Kitaev1995].

## Main statements

* `lemma3_unitary_operator_error`: bounds the error of an ordered product of unitary matrices by
  the sum of step errors.
* `lemma4_measurement_distance`: bounds outcome probability differences by trace norm.
* `lemma5_bridge_mixedWord`: bounds event-probability error by twice the word budget.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.NumericalWord.MixedWordError

/-- A finite list of norm-one elements in a normed ring has product norm at most one. -/
theorem list_prod_norm_le_one {R : Type} [NormedRing R] [NormOneClass R] (l : List R)
    (h : ∀ x ∈ l, ‖x‖ = 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons]
    calc ‖x * xs.prod‖ ≤ ‖x‖ * ‖xs.prod‖ := norm_mul_le _ _
      _ = ‖xs.prod‖ := by rw [h x (by simp), one_mul]
      _ ≤ 1 := ih (fun y hy => h y (by simp [hy]))

/-- For paired lists of norm-one factors with nonnegative step-error bounds, the norm of the
product difference is at most the sum of the bounds. This is the product estimate of
[Kitaev, 1995, Lemma 3][Kitaev1995]. -/
theorem lemma3_operator_error {R : Type} [NormedRing R] [NormOneClass R]
    (l : List (R × R × ℝ))
    (hU : ∀ p ∈ l, ‖p.1‖ = 1)
    (hU' : ∀ p ∈ l, ‖p.2.1‖ = 1)
    (hδ : ∀ p ∈ l, 0 ≤ p.2.2)
    (herr : ∀ p ∈ l, ‖p.2.1 - p.1‖ ≤ p.2.2) :
    ‖(l.map (fun p => p.2.1)).prod - (l.map (fun p => p.1)).prod‖ ≤
      (l.map (fun p => p.2.2)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨u, u', d⟩ := a
    have hn1 : ∀ p ∈ l, ‖p.1‖ = 1 := fun p hp => hU p (List.mem_cons_of_mem _ hp)
    have hn2 : ∀ p ∈ l, ‖p.2.1‖ = 1 := fun p hp => hU' p (List.mem_cons_of_mem _ hp)
    have hd : ∀ p ∈ l, 0 ≤ p.2.2 := fun p hp => hδ p (List.mem_cons_of_mem _ hp)
    have he : ∀ p ∈ l, ‖p.2.1 - p.1‖ ≤ p.2.2 := fun p hp => herr p (List.mem_cons_of_mem _ hp)
    have ih' := ih hn1 hn2 hd he
    set A := (l.map (fun p => p.1)).prod with hAdef
    set B := (l.map (fun p => p.2.1)).prod with hBdef
    set s := (l.map (fun p => p.2.2)).sum with hsdef
    have hBA : ‖B - A‖ ≤ s := ih'
    have hAnorm : ‖A‖ ≤ 1 := by
      rw [hAdef]
      apply list_prod_norm_le_one
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hn1 p hp
    have hu' : ‖u'‖ = 1 := hU' (u, u', d) (by simp)
    have hd0 : 0 ≤ d := hδ (u, u', d) (by simp)
    have hed : ‖u' - u‖ ≤ d := herr (u, u', d) (by simp)
    have key : u' * B - u * A = u' * (B - A) + (u' - u) * A := by noncomm_ring
    have h1 : ‖u' * (B - A)‖ ≤ ‖B - A‖ := by
      calc ‖u' * (B - A)‖ ≤ ‖u'‖ * ‖B - A‖ := norm_mul_le _ _
        _ = ‖B - A‖ := by rw [hu', one_mul]
    have h2 : ‖(u' - u) * A‖ ≤ d := by
      calc ‖(u' - u) * A‖ ≤ ‖u' - u‖ * ‖A‖ := norm_mul_le _ _
        _ ≤ d * 1 := mul_le_mul hed hAnorm (norm_nonneg _) hd0
        _ = d := by ring
    have hb : ‖u' * (B - A) + (u' - u) * A‖ ≤ s + d := by
      calc ‖u' * (B - A) + (u' - u) * A‖
          ≤ ‖u' * (B - A)‖ + ‖(u' - u) * A‖ := norm_add_le _ _
        _ ≤ ‖B - A‖ + d := add_le_add h1 h2
        _ ≤ s + d := by linarith
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [key]
    linarith

/-- The difference between reverse-ordered products of paired unitary matrices has norm at most
the sum of the given step-error bounds, as in [Kitaev, 1995, Lemma 3][Kitaev1995]. -/
theorem lemma3_unitary_operator_error {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ × Matrix I I ℂ × ℝ))
    (hU : ∀ p ∈ l, p.1 ∈ Matrix.unitaryGroup I ℂ)
    (hU' : ∀ p ∈ l, p.2.1 ∈ Matrix.unitaryGroup I ℂ)
    (herr : ∀ p ∈ l, ‖p.2.1 - p.1‖ ≤ p.2.2) :
    ‖(l.map (fun p => p.2.1)).reverse.prod -
        (l.map (fun p => p.1)).reverse.prod‖ ≤ (l.map (fun p => p.2.2)).sum := by
  classical
  have hδ : ∀ p ∈ l, 0 ≤ p.2.2 := fun p hp => (norm_nonneg _).trans (herr p hp)
  cases isEmpty_or_nonempty I with
  | inl h =>
    have hsame : (l.map (fun p => p.2.1)).reverse.prod =
        (l.map (fun p => p.1)).reverse.prod := Subsingleton.elim _ _
    rw [hsame, sub_self, norm_zero]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hδ p hp
  | inr h =>
    have h := lemma3_operator_error l.reverse
      (fun p hp => CStarRing.norm_of_mem_unitary (hU p (List.mem_reverse.mp hp)))
      (fun p hp => CStarRing.norm_of_mem_unitary (hU' p (List.mem_reverse.mp hp)))
      (fun p hp => hδ p (List.mem_reverse.mp hp))
      (fun p hp => herr p (List.mem_reverse.mp hp))
    simpa only [List.map_reverse, List.sum_reverse] using h

/-- For a finite POVM and two density operators, the sum of absolute outcome probability
differences is at most the trace norm of their difference. This is the measurement-distance
estimate of [Kitaev, 1995, Lemma 4][Kitaev1995]. -/
theorem lemma4_measurement_distance {O : Type} [Fintype O] [DecidableEq O] {d : ℕ}
    (E : FinitePOVM O d) (A B : Operator d)
    (hA : IsDensityOperator A) (hB : IsDensityOperator B) :
    (∑ o, |(povmRecordLaw E A hA).prob o - (povmRecordLaw E B hB).prob o|) ≤
      Matrix.traceNorm (A - B) := by
  have h :=
    Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le
      E A B hA hB
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv] at h
  linarith

/-- Total variation distance on finite distributions satisfies the triangle inequality. -/
theorem tv_triangle {X : Type} [Fintype X] [DecidableEq X]
    (p q r : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv p r ≤
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv p q +
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv q r := by
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv]
  have hsum : (∑ x, |p.prob x - r.prob x|) ≤
      ∑ x, (|p.prob x - q.prob x| + |q.prob x - r.prob x|) := by
    apply Finset.sum_le_sum
    intro x _
    calc |p.prob x - r.prob x| = |(p.prob x - q.prob x) + (q.prob x - r.prob x)| := by
          rw [show p.prob x - r.prob x = (p.prob x - q.prob x) + (q.prob x - r.prob x) by ring]
      _ ≤ |p.prob x - q.prob x| + |q.prob x - r.prob x| := abs_add_le _ _
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- If successive total variation distances are bounded by `eps` and `2 * L * δ`, their endpoint
distance is at most `eps + 2 * L * δ`, as used in [Kitaev, 1995, Lemma 5][Kitaev1995]. -/
theorem lemma5_error_budget {X : Type} [Fintype X] [DecidableEq X]
    (p q r : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (eps δ : ℝ) (L : ℕ)
    (h1 : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv p q ≤ eps)
    (h2 : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv q r ≤
      2 * (L : ℝ) * δ) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv p r ≤
      eps + 2 * (L : ℝ) * δ :=
  (tv_triangle p q r).trans (add_le_add h1 h2)

/-- For valid controls and unitary oracles, the operator norm difference between a mixed word
and its implemented matrix is at most `budget W`. -/
theorem lemma3_bridge_mixedWord {n w : ℕ} (hw : w ≤ n) (S : Type)
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (hv : ValidControls W) (hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) :
    ‖word hw O W - mixedWordMatrix hw O W‖ ≤ budget W :=
  (Qatlib.Concepts.NumericalWord.MixedWordError.g2
    n w hw S O W hv hO).1

/-- For a legal mixed word with valid controls and unitary oracles, every event probability on a
normalized input changes by at most `2 * budget W`, as used in [Kitaev1995]. -/
theorem lemma5_bridge_mixedWord {n w : ℕ} (hw : w ≤ n) (S : Type) [DecidableEq S]
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (paid : List (AccessForm S)) (hv : ValidControls W) (hp : mixedWordLegal W paid)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) :
    ∀ (ψ : QState (Reg n)) (E : Finset (Reg n)), Normalized ψ →
      |MeasureProb (ApplyGate (word hw O W) ψ) E -
        MeasureProb (ApplyGate (mixedWordMatrix hw O W) ψ) E| ≤ 2 * budget W :=
  (Qatlib.Concepts.NumericalWord.MixedWordError.g3
    n w hw S O W paid hv hp hO).2.2

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
