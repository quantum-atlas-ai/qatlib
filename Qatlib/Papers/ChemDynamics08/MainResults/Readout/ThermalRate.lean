/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance
import Qatlib.Papers.ChemDynamics08.MainResults.Readout.ReactionReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Papers.ChemDynamics08.MainResults.Readout

noncomputable def thermalMixture {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (C : ℝ) (Γ : E → ℝ) : Operator D :=
  ∑ e, ((C ^ 2 * (Γ e) ^ 2 : ℝ) : ℂ) • outerProduct (φ e)

theorem thermalMixture_trace {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (P : Operator D) (C : ℝ) (Γ : E → ℝ) :
    ((thermalMixture φ C Γ) * P).trace =
      ∑ e, ((C ^ 2 * (Γ e) ^ 2 : ℝ) : ℂ) * (star (φ e) ⬝ᵥ P *ᵥ (φ e)) := by
  unfold thermalMixture
  rw [Finset.sum_mul]
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, trace_outerProduct_mul_eq_quadratic]

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

noncomputable def thermalRate {E : Type*} [Fintype E] (Γ p : E → ℝ) : ℝ :=
  ∑ e, (Γ e) ^ 2 * p e

theorem thermal_ancilla_probability {D : ℕ} {E : Type*} [Fintype E]
    (φ : E → QState (Fin D)) (P : Operator D) (C : ℝ) (Γ p : E → ℝ)
    (hprob : ∀ e, (star (φ e) ⬝ᵥ P *ᵥ (φ e)).re = p e) :
    ((thermalMixture φ C Γ) * P).trace.re = C ^ 2 * thermalRate Γ p := by
  rw [thermalMixture_trace_re]
  unfold thermalRate
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [hprob e]

theorem thermal_rate_precision (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 0 < M ∧
      2 * Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ eps :=
  amplitude_estimation_precision_guarantee eps heps

end Qatlib.Papers.ChemDynamics08.MainResults.Readout
