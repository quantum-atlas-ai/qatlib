/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Laws of successive coordinate measurements

Successive applications of `Collapse` reduce to intersection of the selected events and commute.
After conditioning on an event of positive mass, `measureProb_postMeasure` gives the usual ratio
of intersection mass to conditioning mass.

The resulting certainty and chain rules describe projective measurement in a fixed basis; see
[NielsenChuang2010].

## Main statements

* `collapse_collapse`: Successive collapses select the intersection.
* `measureProb_postMeasure`: Conditional event mass as a ratio.
* `postMeasure_chain_rule`: Multiplicative chain rule for event masses.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib

namespace Qatlib.Foundations.InstrumentCore.Measurement

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Collapsing first onto `S` and then onto `T` equals collapsing onto their intersection. -/
theorem collapse_collapse (ψ : QState I) (S T : Finset I) :
    Collapse (Collapse ψ S) T = Collapse ψ (S ∩ T) := by
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [collapse_apply, hS, hT]

/-- Coordinate collapses commute. -/
theorem collapse_comm (ψ : QState I) (S T : Finset I) :
    Collapse (Collapse ψ S) T = Collapse (Collapse ψ T) S := by
  rw [collapse_collapse, collapse_collapse, Finset.inter_comm]

/-- The mass of `T` in the state collapsed onto `S` is the original mass of `S ∩ T`. -/
theorem measureProb_collapse (ψ : QState I) (S T : Finset I) :
    MeasureProb (Collapse ψ S) T = MeasureProb ψ (S ∩ T) := by
  unfold MeasureProb
  simp_rw [bornProb_collapse]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [and_comm]

/-- Conditioning on `S` of positive mass gives `T` mass equal to the mass of `S ∩ T` divided by
the mass of `S`. -/
theorem measureProb_postMeasure {ψ : QState I} {S : Finset I}
    (hS : 0 < MeasureProb ψ S) (T : Finset I) :
    MeasureProb (PostMeasure ψ S) T = MeasureProb ψ (S ∩ T) / MeasureProb ψ S := by
  change MeasureProb (((Real.sqrt (MeasureProb ψ S) : ℂ)⁻¹) • Collapse ψ S) T = _
  rw [measureProb_smul, measureProb_collapse]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
    Real.sq_sqrt hS.le]
  ring

/-- An event of positive mass has mass one after conditioning on that event. -/
theorem measureProb_postMeasure_self {ψ : QState I} {S : Finset I}
    (hS : 0 < MeasureProb ψ S) : MeasureProb (PostMeasure ψ S) S = 1 := by
  rw [measureProb_postMeasure hS, Finset.inter_self, div_self hS.ne']

/-- The mass of `S` times the conditional mass of `T` equals the original mass of `S ∩ T`, when
`S` has positive mass. -/
theorem postMeasure_chain_rule {ψ : QState I} {S : Finset I}
    (hS : 0 < MeasureProb ψ S) (T : Finset I) :
    MeasureProb ψ S * MeasureProb (PostMeasure ψ S) T = MeasureProb ψ (S ∩ T) := by
  rw [measureProb_postMeasure hS]
  field_simp [hS.ne']

end Qatlib.Foundations.InstrumentCore.Measurement
