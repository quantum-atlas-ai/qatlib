/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentHamiltonian

@[expose] public section


/-! Finite Hilbert--Schmidt parent forms and thermal-factor identities.
These are algebraic interfaces; no physical generator or spectral-gap conclusion is assumed. -/
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GibbsSource.FormAlgebra

open Matrix

variable {D : ℕ}

noncomputable def hsInner (U V : Operator D) : ℂ := Matrix.trace (Uᴴ * V)

noncomputable def dampedForm {ι : Type*} [Fintype ι] (β : ℝ) (ρ : Operator D)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) : ℂ :=
  ∑ a, ∑ b, (↑(phaseKernel β (ν a - ν b)) : ℂ) *
    hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)

noncomputable def plainForm {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) : ℂ :=
  (1 / 2 : ℂ) * hsInner (parentFactor ρ (∑ a, A a) X) (parentFactor ρ (∑ a, A a) X)

section Proofs

/-- The sharp transform preserves addition in its operator argument. -/
theorem sharp_add (ρ B B' : Operator D) : sharp ρ (B + B') = sharp ρ B + sharp ρ B' := by
  simp only [sharp, Matrix.mul_add, Matrix.add_mul]

/-- The flat transform preserves addition in its operator argument. -/
theorem flat_add (ρ B B' : Operator D) : flat ρ (B + B') = flat ρ B + flat ρ B' := by
  simp only [flat, Matrix.mul_add, Matrix.add_mul]

/-- The parent factor with zero jump operator vanishes. -/
theorem parentFactor_zero (ρ X : Operator D) : parentFactor ρ 0 X = 0 := by
  rw [parentFactor_apply]
  simp [sharp, flat]

/-- The parent factor preserves addition of jump operators. -/
theorem parentFactor_add (ρ B B' X : Operator D) :
    parentFactor ρ (B + B') X = parentFactor ρ B X + parentFactor ρ B' X := by
  simp only [parentFactor_apply, sharp_add, flat_add, Matrix.mul_add, Matrix.add_mul]
  abel

/-- The parent factor of a finite sum of jump operators is the sum of their parent factors. -/
theorem parentFactor_sum {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) :
    parentFactor ρ (∑ a, A a) X = ∑ a, parentFactor ρ (A a) X := by
  classical
  have key : ∀ s : Finset ι, parentFactor ρ (∑ a ∈ s, A a) X
      = ∑ a ∈ s, parentFactor ρ (A a) X := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [parentFactor_zero]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, parentFactor_add, ih]
  exact key Finset.univ

/-- Conjugate transpose commutes with finite sums of operators. -/
theorem conjTranspose_sum' {ι : Type*} [Fintype ι] (v : ι → Operator D) :
    (∑ a, v a)ᴴ = ∑ a, (v a)ᴴ := by
  classical
  have key : ∀ s : Finset ι, (∑ a ∈ s, v a)ᴴ = ∑ a ∈ s, (v a)ᴴ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Matrix.conjTranspose_add, ih]
  exact key Finset.univ

/-- The Hilbert-Schmidt inner product of a sum with itself expands into the double sum of
pairwise inner products. -/
theorem hsInner_sum_self {ι : Type*} [Fintype ι] (v : ι → Operator D) :
    hsInner (∑ a, v a) (∑ b, v b) = ∑ a, ∑ b, hsInner (v a) (v b) := by
  simp only [hsInner, conjTranspose_sum', Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum]

/-- When all frequencies coincide, the damped form equals the plain form. -/
theorem dampedForm_of_const_freq {ι : Type*} [Fintype ι] {β : ℝ} {ρ : Operator D} {ν : ι → ℝ}
    (hν : ∀ a b, ν a = ν b) (A : ι → Operator D) (X : Operator D) :
    dampedForm β ρ ν A X = plainForm ρ A X := by
  have hker : ∀ a b, (↑(phaseKernel β (ν a - ν b)) : ℂ) = 1 / 2 := by
    intro a b
    have h0 : ν a - ν b = 0 := by rw [hν a b, sub_self]
    rw [h0, phaseKernel_self]
    push_cast
    norm_num
  rw [plainForm, parentFactor_sum, hsInner_sum_self]
  simp only [dampedForm, hker]
  simp [Finset.mul_sum]

/-- The Hilbert-Schmidt inner product of an operator with itself is the sum of the squared norms
of its entries. -/
theorem hsInner_self_eq (U : Operator D) :
    hsInner U U = ∑ i, ∑ j, ((Complex.normSq (U i j)) : ℂ) := by
  classical
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  exact Finset.sum_comm

/-- The Hilbert-Schmidt inner product of an operator with itself has zero imaginary part. -/
theorem hsInner_self_re (U : Operator D) : (hsInner U U).im = 0 := by
  rw [hsInner_self_eq]
  simp

/-- The real part of the Hilbert-Schmidt squared norm is the sum of the squared norms of all
matrix entries. -/
theorem hsInner_self_re_sum (U : Operator D) :
    (hsInner U U).re = ∑ i, ∑ j, Complex.normSq (U i j) := by
  rw [hsInner_self_eq]
  simp [Complex.re_sum]

/-- The real part of the Hilbert-Schmidt inner product of an operator with itself is
nonnegative. -/
theorem hsInner_self_nonneg (U : Operator D) : 0 ≤ (hsInner U U).re := by
  rw [hsInner_self_re_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- The plain parent form has zero imaginary part. -/
theorem plainForm_re {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) : (plainForm ρ A X).im = 0 := by
  rw [plainForm, Complex.mul_im, hsInner_self_re]
  norm_num

/-- The real part of the plain parent form is nonnegative. -/
theorem plainForm_nonneg {ι : Type*} [Fintype ι] (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) : 0 ≤ (plainForm ρ A X).re := by
  rw [plainForm, Complex.mul_re, hsInner_self_re]
  have h := hsInner_self_nonneg (parentFactor ρ (∑ a, A a) X)
  norm_num
  linarith

/-- The real part of a complex number multiplied by a real scalar is that scalar times its real
part. -/
theorem ofReal_mul_re (c : ℝ) (z : ℂ) : ((c : ℂ) * z).re = c * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Negating the right argument negates the Hilbert-Schmidt inner product. -/
theorem hsInner_neg_right (U V : Operator D) : hsInner U (-V) = -(hsInner U V) := by
  simp [hsInner, Matrix.trace_neg]

/-- Negating the left argument negates the Hilbert-Schmidt inner product. -/
theorem hsInner_neg_left (U V : Operator D) : hsInner (-U) V = -(hsInner U V) := by
  simp [hsInner, Matrix.conjTranspose_neg, Matrix.trace_neg]

/-- A nonzero operator has strictly positive real Hilbert-Schmidt squared norm. -/
theorem hsInner_self_pos {U : Operator D} (hU : U ≠ 0) : 0 < (hsInner U U).re := by
  rw [hsInner_self_re_sum]
  by_contra hcon
  push Not at hcon
  have hzero : ∑ i, ∑ j, Complex.normSq (U i j) = 0 :=
    le_antisymm hcon
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have houter : ∀ i ∈ (Finset.univ : Finset (Fin D)), ∑ j, Complex.normSq (U i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _).mp hzero
  apply hU
  funext i j
  have hinner := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp
    (houter i (Finset.mem_univ i))
  exact Complex.normSq_eq_zero.mp (hinner j (Finset.mem_univ j))

/-- Negating the jump operator negates its parent factor. -/
theorem parentFactor_neg (ρ B X : Operator D) :
    parentFactor ρ (-B) X = -(parentFactor ρ B X) := by
  have h := parentFactor_add ρ B (-B) X
  rw [add_neg_cancel, parentFactor_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Opposite jumps have zero plain form but strictly positive damped form when the parent factor
and frequency-temperature product are nonzero. -/
theorem plainForm_zero_dampedForm_pos {β δ : ℝ} (ρ B X : Operator D)
    (hV : parentFactor ρ B X ≠ 0) (hδ : β * δ ≠ 0) :
    plainForm ρ (![B, -B]) X = 0 ∧ 0 < (dampedForm β ρ (![0, δ]) (![B, -B]) X).re := by
  classical
  have hsum : ∑ i : Fin 2, parentFactor ρ (![B, -B] i) X = 0 := by
    simp [parentFactor_neg]
  constructor
  · rw [plainForm, parentFactor_sum, hsum]
    simp [hsInner]
  · have hlt : phaseKernel β δ < 1 / 2 := phaseKernel_lt_half hδ
    have hpos : 0 < (hsInner (parentFactor ρ B X) (parentFactor ρ B X)).re :=
      hsInner_self_pos hV
    have hcalc : dampedForm β ρ (![0, δ]) (![B, -B]) X
        = ((1 - 2 * phaseKernel β δ : ℝ) : ℂ)
          * hsInner (parentFactor ρ B X) (parentFactor ρ B X) := by
      have hn : phaseKernel β (-δ) = phaseKernel β δ := phaseKernel_neg β δ
      rw [dampedForm]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
        sub_zero, hsInner_neg_right, hsInner_neg_left,
        neg_neg, phaseKernel_self, parentFactor_neg]
      rw [show (0 : ℝ) - δ = -δ by ring, hn]
      push_cast
      ring
    rw [hcalc, ofReal_mul_re]
    nlinarith [hlt, hpos]

end Proofs

end Qatlib.Concepts.GibbsSource.FormAlgebra
