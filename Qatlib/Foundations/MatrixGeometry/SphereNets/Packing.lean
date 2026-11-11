/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Qatlib Contributors
-/

import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Volume bounds for separated finite sets

Proves volume and cardinality bounds for ε-separated finite subsets of the unit ball in a
finite-dimensional real normed space. The specialization `half_separated_card` bounds the size
of a 1-separated subset of the radius-two ball in real Euclidean `N`-space by `5^N`. See
[GohMuller2026] for related background.

## Main statements

* `separated_card_bound`: An ε-separated finite subset of the unit ball, with `ε > 0`, has
  cardinality at most `((1 + ε / 2) / (ε / 2))^finrank ℝ E`.
* `half_separated_card`: A finite subset of the radius-two ball in real Euclidean `N`-space with
  distinct points at distance at least one has cardinality at most `5^N`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open Metric Set Module MeasureTheory
open scoped ENNReal Classical Function
namespace Qatlib.Foundations.MatrixGeometry.SphereNets.Packing
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If points of a finite set lie in the unit ball and distinct points are at least `ε > 0`
apart, then `s.card * (ε / 2)^dim ≤ (1 + ε / 2)^dim`. -/
theorem separated_volume_bound (s : Finset E) (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c≠d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) * (ε/2)^finrank ℝ E ≤ (1+ε/2)^finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ := ε/2
  let ρ := 1+ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball c δ
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball c δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep c hc d hd hcd
    dsimp [δ]
    linarith
  have hA : A ⊆ ball (0:E) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [ρ,δ]
    linarith [hs x hx]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ^finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A=⋃ c∈s,ball c δ from rfl,
          measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ,Finset.sum_const,nsmul_eq_mul,mul_assoc]
      _ ≤ μ (ball (0:E) ρ) := measure_mono hA
      _ = _ := by rw [μ.addHaar_ball_of_pos _ hρ]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ^finrank ℝ E) ≤
      ENNReal.ofReal (ρ^finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 I
  have K := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using K

/-- An ε-separated finite subset of the unit ball, with `ε > 0`, has cardinality at most `((1 +
ε / 2) / (ε / 2))^finrank ℝ E`. -/
theorem separated_card_bound (s : Finset E) (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c≠d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ ((1+ε/2)/(ε/2))^finrank ℝ E := by
  rw [div_pow,le_div_iff₀ (pow_pos (by linarith : 0 < ε/2) _)]
  exact separated_volume_bound s ε hε hs hsep

/-- A finite subset of the radius-two ball in real Euclidean `N`-space with distinct points at
distance at least one has cardinality at most `5^N`. -/
theorem half_separated_card (N : ℕ) (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : ∀ c ∈ s, ‖c‖≤2)
    (hsep : ∀ c ∈ s,∀ d ∈ s,c≠d→1≤‖c-d‖) : s.card ≤ 5^N := by
  simpa using Besicovitch.card_le_of_separated s hs hsep
end Qatlib.Foundations.MatrixGeometry.SphereNets.Packing
