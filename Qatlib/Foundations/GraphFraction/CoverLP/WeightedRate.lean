/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphFraction.CoverLP.MinimaxDual

/-!
# Optimal sampling rates from weighted fractional covers

This module relates a common coverage rate to the weighted fractional cover value. If a context
probability distribution covers each demand multiplied by `T`, `rate_le_inverse_cover` bounds
`T` by the reciprocal cover value whenever that value is positive.

For nonnegative demands with a positive entry, `optimal_weighted_rate` constructs a distribution
attaining this reciprocal rate and proves its optimality. This is the weighted context-sampling
characterization used in [XuEtAl2026].

## Main statements

* `rate_le_inverse_cover`: If the weighted cover value is positive and a context probability
  distribution covers `T` times each demand, then `T` is at most the reciprocal cover value.
* `optimal_weighted_rate`: For nonnegative demands with at least one positive entry, the cover
  value is positive and a context distribution attains reciprocal-cover coverage rate; no
  context distribution attains a larger rate. This is the weighted fractional-cover sampling
  characterization in [XuEtAl2026].

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.GraphFraction.CoverLP
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If the weighted cover value is positive and a context probability distribution covers `T`
times each demand, then `T` is at most the reciprocal cover value. -/
theorem rate_le_inverse_cover (G : SimpleGraph V) (a : V → ℝ) (hχ : 0<coverValue G a)
    (q : Context G → ℝ) (hq : q∈stdSimplex ℝ (Context G)) (T : ℝ)
    (hT : ∀ i,T*a i ≤ coverage G q i) : T ≤ 1/coverValue G a := by
  by_cases ht : T ≤ 0
  · exact ht.trans (one_div_pos.mpr hχ).le
  · have hp : 0<T := lt_of_not_ge ht
    have hf : Feasible G a (fun I => q I/T) := by
      refine ⟨fun I => div_nonneg (hq.1 I) hp.le,?_⟩
      intro i
      rw [coverage_div]
      exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hT i)
    have hc := coverValue_le_mass G a (fun I => q I/T) hf
    have hm : (∑ I,q I/T)=1/T := by
      rw [← Finset.sum_div]
      exact congrArg (fun x : ℝ => x/T) hq.2
    rw [hm] at hc
    apply (le_div_iff₀ hχ).mpr
    have hh := (le_div_iff₀ hp).mp hc
    nlinarith

/-- For nonnegative demands with at least one positive entry, the cover value is positive and a
context distribution attains reciprocal-cover coverage rate; no context distribution attains
a larger rate. This is the weighted fractional-cover sampling characterization in
[XuEtAl2026]. -/
theorem optimal_weighted_rate (G : SimpleGraph V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i)
    (i0 : V) (hi0 : 0<a i0) :
    0<coverValue G a ∧ ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧
      (∀ i,(1/coverValue G a)*a i ≤ coverage G q i) ∧
      ∀ r : Context G → ℝ,r∈stdSimplex ℝ (Context G) →
        ∀ T : ℝ,(∀ i,T*a i ≤ coverage G r i) → T ≤ 1/coverValue G a := by
  obtain ⟨hχ,q,hq,hcov⟩ := attained_strategy G a ha i0 hi0
  refine ⟨hχ,q,hq,?_,?_⟩
  · intro i
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hcov i
  · exact fun r hr T hT => rate_le_inverse_cover G a hχ r hr T hT

end Qatlib.Foundations.GraphFraction.CoverLP
