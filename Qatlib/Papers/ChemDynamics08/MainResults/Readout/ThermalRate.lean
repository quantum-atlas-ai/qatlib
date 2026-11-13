/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance
import Qatlib.Papers.ChemDynamics08.MainResults.Readout.ReactionReadout

/-!
# Thermal rate readout

`thermalMixture` forms a weighted sum of outer products, and `thermalRate` forms the
corresponding weighted sum of outcome values. Trace identities connect the mixture readout with
the rate, conditional on the supplied component expectation values. A separate scalar result
supplies arbitrarily small amplitude-estimation error bounds.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `thermal_ancilla_probability`: expresses the real trace as `C²` times the weighted thermal
  rate.
* `thermal_rate_precision`: supplies a positive integer meeting any positive scalar error
  tolerance.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Papers.ChemDynamics08.MainResults.Readout

/-- The sum of outer products of `φ e` weighted by `C² * (Γ e)²`. -/
noncomputable def thermalMixture {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (C : ℝ) (Γ : E → ℝ) : Operator D :=
  ∑ e, ((C ^ 2 * (Γ e) ^ 2 : ℝ) : ℂ) • outerProduct (φ e)

/-- The trace of the weighted mixture times `P` is the weighted sum of the component quadratic
forms of `P`. -/
theorem thermalMixture_trace {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (P : Operator D) (C : ℝ) (Γ : E → ℝ) :
    ((thermalMixture φ C Γ) * P).trace =
      ∑ e, ((C ^ 2 * (Γ e) ^ 2 : ℝ) : ℂ) * (star (φ e) ⬝ᵥ P *ᵥ (φ e)) := by
  unfold thermalMixture
  rw [Finset.sum_mul]
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, trace_outerProduct_mul_eq_quadratic]

/-- The real trace of the weighted mixture times `P` is `C²` times the sum of the component real
quadratic forms weighted by `(Γ e)²` [KassalEtAl2008]. -/
theorem thermalMixture_trace_re {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (P : Operator D) (C : ℝ) (Γ : E → ℝ) :
    ((thermalMixture φ C Γ) * P).trace.re =
      C ^ 2 * ∑ e, (Γ e) ^ 2 * (star (φ e) ⬝ᵥ P *ᵥ (φ e)).re := by
  rw [thermalMixture_trace]
  rw [Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The finite sum of the outcome values `p e` weighted by `(Γ e)²`. -/
noncomputable def thermalRate {E : Type*} [Fintype E] (Γ p : E → ℝ) : ℝ :=
  ∑ e, (Γ e) ^ 2 * p e

/-- If the component real quadratic forms equal `p e`, the mixture readout equals `C² *
thermalRate Γ p` [KassalEtAl2008]. -/
theorem thermal_ancilla_probability {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (P : Operator D) (C : ℝ) (Γ p : E → ℝ)
    (hprob : ∀ e, (star (φ e) ⬝ᵥ P *ᵥ (φ e)).re = p e) :
    ((thermalMixture φ C Γ) * P).trace.re = C ^ 2 * thermalRate Γ p := by
  rw [thermalMixture_trace_re]
  unfold thermalRate
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [hprob e]

/-- Every positive tolerance is at least `2π / M + π² / M²` for some positive integer `M`
[KassalEtAl2008]. -/
theorem thermal_rate_precision (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 0 < M ∧
      2 * Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ eps :=
  amplitude_estimation_precision_guarantee eps heps

end Qatlib.Papers.ChemDynamics08.MainResults.Readout
