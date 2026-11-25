/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic

@[expose] public section

/-!
# Error budget for approximate walk sampling and reflection

Theorem 11 of [Montanaro2015] composes the approximation guarantees of Theorems 9 and 10. Each
elementary step of the implemented walk deviates from the exact one by a total-variation
distance `ε_r = γ / R` (reflections) and `ε_s = γ` (sampling), so the accumulated distance is at
most `R * ε_r + ε_s = 2 * γ`.

This module records the two halves of that composition on the locked Lemma 18 ledger:

* `walk_error_tv_budget`: total variation between the exact and the implemented output is at most
  `2 * γ` once each stage is within `γ / R` and `γ`.
* `walk_approximation_failure_budget`: a union bound over three intrinsic failure branches
  (`3 * 1/10`), the accumulated transport term `(π²/√6) * T * sqrt (2γ)`
  (`sourceLemma18Transport T (2 * γ)`) and three accumulated shifts of `γ` bounds the failure
  probability by `3/10 + (π²/√6) * T * sqrt (2γ) + 3 * γ`.

## Main statements

* `walk_error_tv_budget`
* `walk_approximation_failure_budget`

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic.StageBMONTECARLO
open scoped BigOperators

/-- Total variation distance satisfies the triangle inequality on finite distributions. -/
private theorem tvDist_triangle {X : Type} [Fintype X] [DecidableEq X]
    (p q r : FinDist X) : tvDist p r ≤ tvDist p q + tvDist q r := by
  have h : (∑ x, |p.prob x - r.prob x|)
      ≤ (∑ x, |p.prob x - q.prob x|) + (∑ x, |q.prob x - r.prob x|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have key : p.prob x - r.prob x = (p.prob x - q.prob x) + (q.prob x - r.prob x) := by ring
    rw [key]
    exact abs_add_le _ _
  unfold tvDist
  linarith

/-- If the exact walk output is within `γ / R` of the intermediate law and the intermediate law
is within `γ` of the implemented output, then the exact and implemented outputs differ in total
variation by at most `2 * γ`. This is the total-variation half of the
[Montanaro2015], Theorem 11 error budget with `ε_r = γ / R` and `ε_s = γ`. -/
theorem walk_error_tv_budget {X : Type} [Fintype X] [DecidableEq X] (p q r : FinDist X)
    (R : ℕ) (hR : 0 < R) (γ : ℝ) (hγ : 0 < γ) (hpq : tvDist p q ≤ γ / R)
    (hqr : tvDist q r ≤ γ) : tvDist p r ≤ 2 * γ := by
  refine le_trans (tvDist_triangle p q r) ?_
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hdiv : γ / R ≤ γ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < R)]
    nlinarith [hγ.le]
  linarith

/-- The probability of a union of three sample events is at most the sum of their
probabilities. -/
private theorem probEvent_eq_sum_indicator {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E] :
    p.probEvent E = ∑ ω, p.probOf ω * (if E ω then (1 : ℝ) else 0) := by
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : E ω <;> simp [h]

/-- The probability of a union of three sample events is at most the sum of their
probabilities. -/
private theorem probEvent_union_three {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (A B C : (Fin L → X) → Prop) [DecidablePred A] [DecidablePred B]
    [DecidablePred C] :
    p.probEvent (fun ω => A ω ∨ B ω ∨ C ω)
      ≤ p.probEvent A + p.probEvent B + p.probEvent C := by
  classical
  have hind : ∀ ω : Fin L → X,
      (if A ω ∨ B ω ∨ C ω then (1 : ℝ) else 0)
        ≤ (if A ω then (1 : ℝ) else 0) + (if B ω then (1 : ℝ) else 0)
          + (if C ω then (1 : ℝ) else 0) := by
    intro ω
    by_cases hA : A ω <;> by_cases hB : B ω <;> by_cases hC : C ω <;>
      simp [hA, hB, hC]
  rw [probEvent_eq_sum_indicator p (fun ω => A ω ∨ B ω ∨ C ω), probEvent_eq_sum_indicator p A,
    probEvent_eq_sum_indicator p B, probEvent_eq_sum_indicator p C]
  calc (∑ ω, p.probOf ω * (if A ω ∨ B ω ∨ C ω then (1 : ℝ) else 0))
      ≤ ∑ ω, p.probOf ω * ((if A ω then (1 : ℝ) else 0) + (if B ω then (1 : ℝ) else 0)
          + (if C ω then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hind ω) (Finset.prod_nonneg fun _ _ => p.nonneg _)
    _ = (∑ ω, p.probOf ω * (if A ω then (1 : ℝ) else 0))
          + (∑ ω, p.probOf ω * (if B ω then (1 : ℝ) else 0))
          + (∑ ω, p.probOf ω * (if C ω then (1 : ℝ) else 0)) := by
        simp only [mul_add, Finset.sum_add_distrib]

/-- Three intrinsic failure branches of probability at most `1/10`, an accumulated transport
term bounded by `(π²/√6) * T * sqrt (2γ)`, and three accumulated approximation shifts of at
most `γ` combine, by a union bound, into a total failure probability of at most
`3/10 + (π²/√6) * T * sqrt (2γ) + 3 * γ`. This is the failure half of the
[Montanaro2015], Theorem 11 error budget. -/
theorem walk_approximation_failure_budget {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (γ : ℝ) (_hγ : 0 < γ) (T : ℕ)
    (G : Fin 3 → (Fin L → X) → Prop) [∀ i, DecidablePred (G i)]
    [DecidablePred (fun ω => ∃ i, G i ω)]
    (Gt : (Fin L → X) → Prop) [DecidablePred Gt]
    (S : Fin 3 → (Fin L → X) → Prop) [∀ i, DecidablePred (S i)]
    [DecidablePred (fun ω => ∃ i, S i ω)]
    (hG : ∀ i : Fin 3, p.probEvent (G i) ≤ 1 / 10)
    (hGt : p.probEvent Gt ≤ sourceLemma18Transport T (2 * γ))
    (hS : ∀ i : Fin 3, p.probEvent (S i) ≤ γ) :
    p.probEvent (fun ω => (∃ i, G i ω) ∨ Gt ω ∨ (∃ i, S i ω))
      ≤ 3 / 10 + sourceLemma18Transport T (2 * γ) + 3 * γ := by
  classical
  have h1 : p.probEvent (fun ω => ∃ i : Fin 3, G i ω) ≤ 3 / 10 := by
    refine le_trans (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound p G) ?_
    calc (∑ i : Fin 3, p.probEvent (G i))
        ≤ ∑ _i : Fin 3, (1 / 10 : ℝ) := Finset.sum_le_sum fun i _ => hG i
      _ = 3 / 10 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have h3 : p.probEvent (fun ω => ∃ i : Fin 3, S i ω) ≤ 3 * γ := by
    refine le_trans (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound p S) ?_
    calc (∑ i : Fin 3, p.probEvent (S i))
        ≤ ∑ _i : Fin 3, γ := Finset.sum_le_sum fun i _ => hS i
      _ = 3 * γ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have htri := probEvent_union_three p (fun ω => ∃ i : Fin 3, G i ω) Gt
    (fun ω => ∃ i : Fin 3, S i ω)
  linarith

end Qatlib.Papers.MCMontanaro15.MonteCarlo
