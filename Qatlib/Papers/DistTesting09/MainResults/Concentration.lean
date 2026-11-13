/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs

/-!
# Hoeffding bounds for distribution hit counts

Independent samples from a finite distribution give a hit count for a chosen subset. The module
bounds its upper deviation from the expected count by `exp (-2 * M * δ ^ 2)`, both in centered
form and as a threshold on the count.

This development follows [BravyiHarrowHassidim2011].

## Main statements

* `lemma8_hoeffding_diff`: the centered upper-deviation probability is exponentially small.
* `lemma8_chernoff_hoeffding`: the equivalent upper-tail count bound.

## References

* [Bravyi et al., 2011][BravyiHarrowHassidim2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs

namespace Qatlib.Papers.DistTesting09.MainResults.Concentration

variable {N : ℕ}

/-- For `M > 0` independent samples and `δ > 0`, the probability that the hit count exceeds its
mean `M * ∑ x ∈ B, p.prob x` by at least `M * δ` is at most `exp (-(2 * M * δ ^ 2))`. See
[BravyiHarrowHassidim2011]. -/
theorem lemma8_hoeffding_diff (p : Dist N) (B : Finset (Fin N))
    (M : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    p.probEvent (L := M)
        (fun ω => (M : ℝ) * δ ≤ hitCount B ω - (M : ℝ) * (∑ x ∈ B, p.prob x))
      ≤ Real.exp (-(2 * (M : ℝ) * δ ^ 2)) := by
  classical
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hδ' : 0 < (M : ℝ) * δ := mul_pos hMpos hδ
  have hS : 0 < ∑ _i : Fin M, (1 : ℝ) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    simp only [one_pow, sub_zero, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact_mod_cast hM
  have h := independent_weighted_hoeffding_signed (fun _ : Fin M => p)
    (fun _ => (1 : ℝ)) (fun _ (x : Fin N) => if x ∈ B then (1 : ℝ) else 0)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ((M : ℝ) * δ) 1
    (fun _ => by norm_num)
    (fun _ x => by by_cases hx : x ∈ B <;> simp [hx])
    hδ' (by norm_num) hS

  have hexp : (independent (fun _ : Fin M => p)).expect
      (weightedSum (fun _ => (1 : ℝ)) (fun _ (x : Fin N) => if x ∈ B then (1 : ℝ) else 0))
      = (M : ℝ) * (∑ x ∈ B, p.prob x) := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp only [one_mul, expect_indicator, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

  have hsum : weightedSum (fun _ => (1 : ℝ)) (fun _ (x : Fin N) => if x ∈ B then (1 : ℝ) else 0)
      = fun ω : Fin M → Fin N => hitCount B ω := by
    funext ω
    simp only [weightedSum, hitCount, one_mul]
  have hexp' : (independent (fun _ : Fin M => p)).expect (fun ω => hitCount B ω)
      = (M : ℝ) * (∑ x ∈ B, p.prob x) := by
    rw [← hsum]
    exact hexp
  have h' : eventMass (independent (fun _ : Fin M => p))
      (fun ω => (M : ℝ) * δ ≤ hitCount B ω - (M : ℝ) * (∑ x ∈ B, p.prob x))
      ≤ Real.exp (-2 * ((M : ℝ) * δ) ^ 2 /
          (∑ i : Fin M, (1 : ℝ) ^ 2 * ((1 : ℝ) - 0) ^ 2)) := by
    simpa [hsum, hexp'] using! h
  rw [← eventMass_independent_const p
    (fun ω : Fin M → Fin N => (M : ℝ) * δ ≤ hitCount B ω - (M : ℝ) * (∑ x ∈ B, p.prob x))]
  refine le_trans h' ?_
  simp only [one_pow, sub_zero, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show -2 * ((M : ℝ) * δ) ^ 2 / (M : ℝ) = -(2 * (M : ℝ) * δ ^ 2) by
    field_simp [hMne]]

/-- For `M > 0` independent samples and `δ > 0`, the probability that the hit count is at least
`M * ∑ x ∈ B, p.prob x + M * δ` is at most `exp (-(2 * M * δ ^ 2))`. See
[BravyiHarrowHassidim2011]. -/
theorem lemma8_chernoff_hoeffding (p : Dist N) (B : Finset (Fin N))
    (M : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    p.probEvent (L := M)
        (fun ω => (M : ℝ) * (∑ x ∈ B, p.prob x) + (M : ℝ) * δ ≤ hitCount B ω)
      ≤ Real.exp (-(2 * (M : ℝ) * δ ^ 2)) := by
  classical
  have h1 := lemma8_hoeffding_diff p B M hM δ hδ
  have heq : p.probEvent (L := M)
        (fun ω => (M : ℝ) * (∑ x ∈ B, p.prob x) + (M : ℝ) * δ ≤ hitCount B ω)
      = p.probEvent (L := M)
        (fun ω => (M : ℝ) * δ ≤ hitCount B ω - (M : ℝ) * (∑ x ∈ B, p.prob x)) := by
    apply le_antisymm
    · apply probEvent_mono
      intro ω hω
      linarith
    · apply probEvent_mono
      intro ω hω
      linarith
  rw [heq]
  exact h1

end Qatlib.Papers.DistTesting09.MainResults.Concentration
