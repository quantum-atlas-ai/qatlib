/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent gate fault measures

`faultLaw` places the weights `e` and `1-e` on Boolean fault and no fault outcomes, using
`ENNReal.ofReal`; it is a probability law when `0 ≤ e ≤ 1`. `independentLaw` forms the product
over gate positions, and `actual_no_fault_probability` evaluates the measure of the event with
no faults. This gives the independent fault factor used in the resource estimates of
[GohMuller2026].

## Main statements

* `faultLaw_probability`: For `0 ≤ e ≤ 1`, the Boolean fault measure is a probability measure.
* `actual_no_fault_probability`: For `e ≤ 1`, the measure of the event that all `G` fault
  coordinates are false equals `ENNReal.ofReal ((1-e)^G)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.OverlapGapGoh26.Resources.Faults

/-- The Boolean fault measure with masses `ENNReal.ofReal e` at true and `ENNReal.ofReal (1-e)`
at false. -/
def faultLaw (e : ℝ) : Measure Bool :=
  ENNReal.ofReal e • Measure.dirac true+ENNReal.ofReal (1-e) • Measure.dirac false

instance faultLaw_finite (e : ℝ) : IsFiniteMeasure (faultLaw e) := by
  constructor
  simp only [faultLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,smul_eq_mul,mul_one]
  finiteness

/-- For `0 ≤ e ≤ 1`, the Boolean fault measure is a probability measure. -/
theorem faultLaw_probability (e : ℝ) (he : 0≤e) (he1 : e≤1) : IsProbabilityMeasure (faultLaw e) := by
  constructor
  simp only [faultLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add he (by linarith),show e+(1-e)=1 by ring,ENNReal.ofReal_one]

/-- The measure of the no fault outcome is `ENNReal.ofReal (1-e)`. -/
theorem faultLaw_false (e : ℝ) : faultLaw e {false}=ENNReal.ofReal (1-e) := by
  simp [faultLaw]

/-- The product measure of `G` Boolean fault coordinates, each with measure `faultLaw e`. -/
def independentLaw (e : ℝ) (G : ℕ) : Measure (Fin G → Bool) :=
  Measure.pi (fun _ => faultLaw e)

/-- For `e ≤ 1`, the measure of the event that all `G` fault coordinates are false equals
`ENNReal.ofReal ((1-e)^G)`. See [GohMuller2026]. -/
theorem actual_no_fault_probability (e : ℝ) (he1 : e≤1) (G : ℕ) :
    independentLaw e G {x | ∀ i,x i=false}=ENNReal.ofReal ((1-e)^G) := by
  have he : {x : Fin G → Bool | ∀ i,x i=false}=Set.pi Set.univ (fun _ => ({false} : Set Bool)) := by
    ext x
    simp
  rw [independentLaw,he,Measure.pi_pi]
  simp only [faultLaw_false,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by linarith : 0≤1-e) G).symm

end Qatlib.Papers.OverlapGapGoh26.Resources.Faults
