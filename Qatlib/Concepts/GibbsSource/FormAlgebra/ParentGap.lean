/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentForm

@[expose] public section


/-! Normalized Hilbert--Schmidt variance and form-gap predicates.
The supplied lower bounds remain hypotheses until proved by a concrete source consumer. -/
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GibbsSource.FormAlgebra

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

noncomputable def hsVar (W X : Operator D) : ℝ :=
  (hsInner X X).re - Complex.normSq (hsInner W X) / (hsInner W W).re

def FormGapAtLeast (E : Operator D → ℝ) (W : Operator D) (r : ℝ) : Prop :=
  ∀ X, r * hsVar W X ≤ E X

noncomputable def reDamped {ι : Type*} [Fintype ι] (β : ℝ) (ρ : Operator D)
    (ν : ι → ℝ) (A : ι → Operator D) : Operator D → ℝ :=
  fun X => (dampedForm β ρ ν A X).re

noncomputable def rePlain {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D) :
    Operator D → ℝ :=
  fun X => (plainForm ρ A X).re

section Proofs

/-- An upper comparison by a positive multiple transfers a form gap to the comparison form with
the gap divided by that multiple. -/
theorem formGap_transfer {E0 Eg : Operator D → ℝ} {W : Operator D} {α : ℝ} (hα : 0 < α)
    (hcmp : ∀ X, Eg X ≤ α * E0 X) {r : ℝ} (hgap : FormGapAtLeast Eg W r) :
    FormGapAtLeast E0 W (r / α) := by
  intro X
  have h1 := hgap X
  have h2 := hcmp X
  calc (r / α) * hsVar W X
      = (r * hsVar W X) / α := div_mul_eq_mul_div r α (hsVar W X)
    _ ≤ Eg X / α := div_le_div_of_nonneg_right h1 hα.le
    _ ≤ (α * E0 X) / α := div_le_div_of_nonneg_right h2 hα.le
    _ = E0 X := mul_div_cancel_left₀ (E0 X) (ne_of_gt hα)

/-- When all frequencies coincide, a gap for the real plain form gives the same gap for the real
damped form. -/
theorem formGap_congr_of_const_freq {ι : Type*} [Fintype ι] {β : ℝ} {ρ : Operator D} {ν : ι → ℝ}
    {W : Operator D} {r : ℝ} (hν : ∀ a b, ν a = ν b) (A : ι → Operator D)
    (hgap : FormGapAtLeast (rePlain ρ A) W r) :
    FormGapAtLeast (reDamped β ρ ν A) W r := by
  intro X
  have h := hgap X
  show r * hsVar W X ≤ (dampedForm β ρ ν A X).re
  rw [dampedForm_of_const_freq hν A X]
  exact h

section ExtraCommutant

/-- The Hilbert-Schmidt inner product distributes over subtraction in its right argument. -/
theorem hsInner_sub_right (U V W : Operator D) :
    hsInner U (V - W) = hsInner U V - hsInner U W := by
  simp [hsInner, Matrix.mul_sub, Matrix.trace_sub]

/-- A complex scalar in the right argument factors out of the Hilbert-Schmidt inner product. -/
theorem hsInner_smul_right (U : Operator D) (c : ℂ) (V : Operator D) :
    hsInner U (c • V) = c * hsInner U V := by
  simp [hsInner, Matrix.trace_smul]

/-- For positive definite `ρ`, multiplication by inverse fourth roots on both sides reverses
fourth-root conjugation. -/
theorem inv_conj_conj {ρ : Operator D} (hρ : ρ.PosDef) (Y : Operator D) :
    (fourthRoot ρ)⁻¹ * (fourthRoot ρ * Y * fourthRoot ρ) * (fourthRoot ρ)⁻¹ = Y := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, fourthRoot_inv_mul hρ, Matrix.one_mul,
    Matrix.mul_assoc, fourthRoot_mul_inv hρ, Matrix.mul_one]

/-- For positive definite `ρ`, conjugating an operator commuting with the jump by fourth roots
yields a zero parent factor. -/
theorem parentFactor_conj_mem_kernel {ρ : Operator D} (hρ : ρ.PosDef) {B Y : Operator D}
    (hcomm : B * Y = Y * B) :
    parentFactor ρ B (fourthRoot ρ * Y * fourthRoot ρ) = 0 := by
  rw [parentFactor_eq_zero_iff hρ, inv_conj_conj hρ Y]
  exact hcomm

/-- If fourth-root conjugation equals a scalar multiple of the square root of positive definite
`ρ`, the original operator is that scalar times the identity. -/
theorem conj_eq_scalar_iff {ρ : Operator D} (hρ : ρ.PosDef) {Y : Operator D} {c : ℂ}
    (h : fourthRoot ρ * Y * fourthRoot ρ = c • CFC.sqrt ρ) : Y = c • (1 : Operator D) := by
  have h1 := congrArg (fun Z : Operator D => (fourthRoot ρ)⁻¹ * Z * (fourthRoot ρ)⁻¹) h
  rw [inv_conj_conj hρ Y] at h1
  rw [h1]
  calc (fourthRoot ρ)⁻¹ * (c • CFC.sqrt ρ) * (fourthRoot ρ)⁻¹
      = c • ((fourthRoot ρ)⁻¹ * CFC.sqrt ρ * (fourthRoot ρ)⁻¹) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (1 : Operator D) := by
        rw [(fourthRoot_mul_self ρ).symm, ← Matrix.mul_assoc, fourthRoot_inv_mul hρ,
          Matrix.one_mul, fourthRoot_mul_inv hρ]

/-- A nonscalar common commutant yields a common parent-factor kernel element independent of the
square root of positive definite `ρ`. -/
theorem kernel_not_unique_of_extra_commutant {ι : Type*} {ρ : Operator D}
    (hρ : ρ.PosDef) (A : ι → Operator D) {Y : Operator D}
    (hY : ∀ c : ℂ, Y ≠ c • (1 : Operator D))
    (hcomm : ∀ j, A j * Y = Y * A j) :
    (∀ j, parentFactor ρ (A j) (CFC.sqrt ρ) = 0
      ∧ parentFactor ρ (A j) (fourthRoot ρ * Y * fourthRoot ρ) = 0)
    ∧ ∀ c : ℂ, fourthRoot ρ * Y * fourthRoot ρ ≠ c • CFC.sqrt ρ := by
  refine ⟨fun j => ⟨parentFactor_sqrt hρ, parentFactor_conj_mem_kernel hρ (hcomm j)⟩,
    fun c h => hY c (conj_eq_scalar_iff hρ h)⟩

end ExtraCommutant

end Proofs

end Qatlib.Concepts.GibbsSource.FormAlgebra
