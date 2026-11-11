/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite likelihood support bounds

This module computes the probability that all independent observations lie in a prescribed set.
`support_bound` applies this identity to bound likelihood comparison by the mass of the
competing support, and `decoder_error_bound` sums such bounds over incorrect candidates. These
are elementary finite decision estimates in the statistical framework of [Helstrom1976].

## Main statements

* `all_samples_mass`: The probability that all `k` independent observations satisfy `A` is the
  `k`th power of its one sample probability.
* `support_bound`: The probability under `p` that a `k` sample record has likelihood no larger
  than under `q` is at most the `k`th power of the `p` mass on the support of `q`.
* `decoder_error_bound`: If each incorrect decoder output has likelihood at least the `p`
  likelihood of the record, its error probability is at most the sum of the competing support
  mass powers.

## References

* [Helstrom, 1976][Helstrom1976]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLikelihood
open scoped BigOperators
open scoped Classical
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in

/-- Inclusion of decidable sample record events implies an inequality between their
probabilities. -/
private theorem event_mono (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) {k : ℕ}
    (E F : (Fin k → X) → Prop) [DecidablePred E] [DecidablePred F] (h : ∀ w, E w → F w) :
    p.probEvent E ≤ p.probEvent F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h w (Finset.mem_filter.mp hw).2⟩
  · intro w _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- The probability that all `k` independent observations satisfy `A` is the `k`th power of its
one sample probability. -/
theorem all_samples_mass (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (k : ℕ) (A : X → Prop) [DecidablePred A] :
    p.probEvent (fun w : Fin k → X => ∀ i, A (w i)) =
      (∑ x with A x, p.prob x) ^ k := by
  have h := p.expect_prod (L := k) (fun _ x => if A x then (1 : ℝ) else 0)
  have hi (w : Fin k → X) :
      (∏ i, if A (w i) then (1 : ℝ) else 0) = if ∀ i, A (w i) then 1 else 0 := by
    by_cases hw : ∀ i, A (w i)
    · simp [hw]
    · obtain ⟨i, hi⟩ := not_forall.mp hw
      rw [if_neg hw]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simpa only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul] using h

/-- The probability under `p` that a `k` sample record has likelihood no larger than under `q`
is at most the `k`th power of the `p` mass on the support of `q`. -/
theorem support_bound (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (k : ℕ) :
    p.probEvent (fun w : Fin k → X => p.probOf w ≤ q.probOf w) ≤
      (∑ x with q.prob x ≠ 0, p.prob x) ^ k := by
  apply le_of_le_of_eq (b := p.probEvent (fun w : Fin k → X => ∀ i, q.prob (w i) ≠ 0))
  swap
  · simpa using all_samples_mass p k (fun x => q.prob x ≠ 0)
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro w _
  by_cases hp : p.probOf w = 0
  · simp [hp]
  · have hpos : 0 < p.probOf w :=
      lt_of_le_of_ne (Finset.prod_nonneg fun i _ => p.nonneg _) (Ne.symm hp)
    by_cases hbeat : p.probOf w ≤ q.probOf w
    · have hall : ∀ i, q.prob (w i) ≠ 0 := by
        intro i hi
        have hzero : q.probOf w = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
        rw [hzero] at hbeat
        linarith
      simp [hbeat, hall]
    · simp only [if_neg hbeat]
      split_ifs
      · exact hpos.le
      · exact le_refl _

/-- If each incorrect decoder output has likelihood at least the `p` likelihood of the record,
its error probability is at most the sum of the competing support mass powers. -/
theorem decoder_error_bound (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) {k m : ℕ}
    (q : Fin m → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (truth : Fin m) (decode : (Fin k → X) → Fin m)
    (hdecode : ∀ w, decode w ≠ truth → p.probOf w ≤ (q (decode w)).probOf w) :
    p.probEvent (fun w => decode w ≠ truth) ≤
      ∑ c with c ≠ truth, (∑ x with (q c).prob x ≠ 0, p.prob x) ^ k := by
  let E := fun c (w : Fin k → X) => c ≠ truth ∧ p.probOf w ≤ (q c).probOf w
  have hu := p.union_bound E
  have hm := event_mono p (fun w => decode w ≠ truth)
    (fun w => ∃ c, E c w) (fun w hw => ⟨decode w, hw, hdecode w hw⟩)
  suffices hb : (∑ c, p.probEvent (E c)) ≤
      ∑ c with c ≠ truth, (∑ x with (q c).prob x ≠ 0, p.prob x) ^ k by
    simpa using hm.trans (hu.trans hb)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : c = truth
  · subst c
    simp [E, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
  · rw [if_pos hc]
    exact (event_mono p (E c) (fun w => p.probOf w ≤ (q c).probOf w)
      (fun _ h => h.2)).trans (support_bound p (q c) k)

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLikelihood
