/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.EmpiricalL1Accuracy
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteDistributionVariation

/-!
# Lower bounds for empirical L1 confidence

This module packages a positive length histogram as `empiricalLaw` and uses records confined to
a subset to force L1 error. `subset_event_lower` bounds the probability of that error event
below by the subset mass to the power `n`, and `confidence_necessary` extracts a logarithmic
necessary sample size. These finite sampling bounds complement Monte Carlo accuracy estimates
[Montanaro2015].

## Main statements

* `deviation_of_all`: If every observation lies in `S`, its empirical L1 error relative to `p`
  is at least twice the `p` mass outside `S`.
* `subset_event_lower`: For a positive sample count, the probability of L1 error at least twice
  the mass outside `S` is at least the `n`th power of the mass of `S`.
* `confidence_necessary`: If `S` has mass strictly between zero and one and the stated L1 error
  event has probability at most positive `delta`, then `n ≥ log delta / log (mass S)`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1LowerBounds
open scoped BigOperators Classical
open EmpiricalL1Concentration FiniteInformationDivergence
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The finite probability distribution given by the histogram of a positive length sample
record. -/
def empiricalLaw {n : ℕ} (hn : 0 < n) (w : Fin n → X) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X where
  prob := histogram w
  nonneg x := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact Finset.sum_nonneg fun i _ => by dsimp; split_ifs <;> norm_num
  sum_one := by
    unfold histogram Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
    rw [← Finset.sum_div, Finset.sum_comm]
    simp [hn.ne']

/-- If every observation lies in `S`, the empirical distribution assigns total mass one to `S`. -/
private theorem empirical_mass_of_all {n : ℕ} (hn : 0 < n)
    (w : Fin n → X) (S : Finset X) (hw : ∀ i, w i ∈ S) :
    (∑ x ∈ S, (empiricalLaw hn w).prob x) = 1 := by
  change (∑ x ∈ S, histogram w x) = 1
  unfold histogram Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [hw, hn.ne']

/-- If every observation lies in `S`, its empirical L1 error relative to `p` is at least twice
the `p` mass outside `S`. -/
theorem deviation_of_all {n : ℕ} (hn : 0 < n) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (w : Fin n → X) (S : Finset X) (hw : ∀ i, w i ∈ S) :
    2*(1-∑ x ∈ S, p.prob x) ≤ deviation p.prob w := by
  have ht := FiniteDistributionVariation.event_distance (empiricalLaw hn w) p S
  rw [empirical_mass_of_all hn w S hw] at ht
  rw [abs_of_nonneg (sub_nonneg.mpr (FiniteDistributionVariation.event_mass_le_one p S))] at ht
  change 1-(∑ x ∈ S, p.prob x) ≤ deviation p.prob w/2 at ht
  linarith

/-- For a positive sample count, the probability of L1 error at least twice the mass outside `S`
is at least the `n`th power of the mass of `S`. -/
theorem subset_event_lower (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) (S : Finset X) :
    (∑ x ∈ S, p.prob x)^n ≤ p.probEvent (fun w : Fin n → X =>
      2*(1-∑ x ∈ S, p.prob x) ≤ deviation p.prob w) := by
  have hm := FiniteLikelihood.all_samples_mass p n (fun x => x ∈ S)
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hm
  rw [← hm]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      deviation_of_all hn p w S (Finset.mem_filter.mp hw).2⟩
  · intro w _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- If `S` has mass strictly between zero and one and the stated L1 error event has probability
at most positive `delta`, then `n ≥ log delta / log (mass S)`. -/
theorem confidence_necessary (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) (S : Finset X)
    (delta : ℝ) (hpos : 0 < ∑ x ∈ S, p.prob x) (hlt : (∑ x ∈ S, p.prob x) < 1)
    (_hdelta : 0 < delta)
    (hguarantee : p.probEvent (fun w : Fin n → X =>
      2*(1-∑ x ∈ S, p.prob x) ≤ deviation p.prob w) ≤ delta) :
    Real.log delta / Real.log (∑ x ∈ S, p.prob x) ≤ (n : ℝ) := by
  have hp := (subset_event_lower p n hn S).trans hguarantee
  have hl := Real.log_le_log (pow_pos hpos n) hp
  rw [Real.log_pow] at hl
  apply (div_le_iff_of_neg (Real.log_neg hpos hlt)).mpr
  exact hl

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1LowerBounds
