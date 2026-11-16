/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentForm

@[expose] public section


/-! Complete weighted plain and damped parent forms.
Both frequency indices are summed before taking a real part, with the physical half explicit. -/
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GibbsSource.FormAlgebra

open Matrix

variable {D : ℕ}

noncomputable def wdampedForm {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (β : ℝ) (ρ : Operator D)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) : ℂ :=
  ∑ a, ∑ b, (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
    hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)

noncomputable def wplainForm {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (ρ : Operator D)
    (A : ι → Operator D) (X : Operator D) : ℂ :=
  ∑ a, ∑ b, (↑(w a b / 2) : ℂ) *
    hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)

section Proofs

/-- Unit weights reduce the weighted damped form to the damped form. -/
theorem wdampedForm_one {ι : Type*} [Fintype ι] (β : ℝ) (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    wdampedForm (fun _ _ => (1 : ℝ)) β ρ ν A X = dampedForm β ρ ν A X := by
  simp [wdampedForm, dampedForm]

/-- Unit weights reduce the weighted plain form to the plain form. -/
theorem wplainForm_one {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) :
    wplainForm (fun _ _ => (1 : ℝ)) ρ A X = plainForm ρ A X := by
  rw [wplainForm, plainForm, parentFactor_sum, hsInner_sum_self]
  simp [Finset.mul_sum]

/-- When all frequencies coincide, the weighted damped form equals the weighted plain form. -/
theorem wdampedForm_of_const_freq {ι : Type*} [Fintype ι] {β : ℝ} {ρ : Operator D} {ν : ι → ℝ}
    {w : ι → ι → ℝ} (hν : ∀ a b, ν a = ν b) (A : ι → Operator D) (X : Operator D) :
    wdampedForm w β ρ ν A X = wplainForm w ρ A X := by
  have hker : ∀ a b, phaseKernel β (ν a - ν b) = 1 / 2 := by
    intro a b
    rw [show ν a - ν b = 0 from by rw [hν a b, sub_self]]
    exact phaseKernel_self β
  simp only [wdampedForm, wplainForm, hker]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

end Proofs

end Qatlib.Concepts.GibbsSource.FormAlgebra
