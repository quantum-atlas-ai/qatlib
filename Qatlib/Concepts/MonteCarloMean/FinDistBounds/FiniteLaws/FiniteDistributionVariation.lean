/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteLikelihoodConcentration

/-!
# Transferring finite event probabilities

This module bounds the difference of finite event probabilities by total variation.
`success_transfer` transports a success lower bound to a perturbed law, and `repeated_transfer`
gives the corresponding lower bound for at least one success in independent repetitions.
Statistical distinguishability and total variation are discussed in [Watrous2018].

## Main statements

* `event_distance`: The absolute difference of the probabilities of any finite event under `p`
  and `q` is at most their total variation distance `tv p q`.
* `success_transfer`: An event of probability at least `s` under `p` has probability at least `s
  - eps` under `q` when `tv p q ≤ eps`.
* `repeated_transfer`: If an event has probability at least `s` under `p` and `tv p q ≤ eps`,
  then at least one occurrence in `n` independent `q` samples has probability at least `1 - (1 -
  s + eps) ^ n`.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteDistributionVariation
open scoped BigOperators Classical
open FiniteInformationDivergence
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The absolute difference of the probabilities of any finite event under `p` and `q` is at
most their total variation distance `tv p q`. -/
theorem event_distance (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (S : Finset X) :
    |(∑ x ∈ S, p.prob x)-(∑ x ∈ S, q.prob x)| ≤ tv p q := by
  let d := fun x => p.prob x-q.prob x
  have hz : ∑ x, d x = 0 := by simp [d, Finset.sum_sub_distrib, p.sum_one, q.sum_one]
  have hp : (∑ x ∈ S, d x)+(∑ x ∈ Sᶜ, d x) = 0 := by
    rw [Finset.sum_add_sum_compl]; exact hz
  have ha := Finset.abs_sum_le_sum_abs d S
  have hb := Finset.abs_sum_le_sum_abs d Sᶜ
  have he : (∑ x ∈ Sᶜ, d x) = -(∑ x ∈ S, d x) := by linarith
  rw [he, abs_neg] at hb
  have hs := Finset.sum_add_sum_compl S (fun x => |d x|)
  rw [← Finset.sum_sub_distrib]
  change |∑ x ∈ S, d x| ≤ (∑ x, |d x|)/2
  linarith

omit [DecidableEq X] in

/-- The total mass assigned to a finite subset by a probability distribution is at most one. -/
theorem event_mass_le_one (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (S : Finset X) : ∑ x ∈ S, p.prob x ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun x _ _ => p.nonneg x)

/-- An event of probability at least `s` under `p` has probability at least `s - eps` under `q`
when `tv p q ≤ eps`. -/
theorem success_transfer (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (S : Finset X) (s eps : ℝ)
    (hs : s ≤ ∑ x ∈ S, p.prob x) (he : tv p q ≤ eps) :
    s-eps ≤ ∑ x ∈ S, q.prob x := by
  have h := (le_abs_self ((∑ x ∈ S, p.prob x)-(∑ x ∈ S, q.prob x))).trans
    (event_distance p q S)
  linarith

/-- If an event has probability at least `s` under `p` and `tv p q ≤ eps`, then at least one
occurrence in `n` independent `q` samples has probability at least `1 - (1 - s + eps) ^ n`. -/
theorem repeated_transfer (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (S : Finset X) (s eps : ℝ)
    (hs : s ≤ ∑ x ∈ S, p.prob x) (he : tv p q ≤ eps) (n : ℕ) :
    1-(1-s+eps)^n ≤ q.probEvent (fun w : Fin n → X => ∃ i, w i ∈ S) := by
  rw [FiniteLikelihoodConcentration.repeated_success q n (fun x => x ∈ S)]
  have hm : (∑ x with x ∈ S, q.prob x) = ∑ x ∈ S, q.prob x := by simp
  rw [hm]
  have ht := success_transfer p q S s eps hs he
  have hp := event_mass_le_one q S
  have hpow : (1-∑ x ∈ S, q.prob x)^n ≤ (1-s+eps)^n := by
    gcongr
    linarith
  linarith

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteDistributionVariation
