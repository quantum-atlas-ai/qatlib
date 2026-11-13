/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Expectation values of finite matrix observables

This module fixes the paper-level expectation functional `⟨ψ|M|ψ⟩` used by
Jordan–Lee–Preskill, *Quantum Computation of Scattering in Scalar Quantum Field
Theories* (arXiv:1112.4833v1), on the finite-dimensional observable model of the
repository: an observable is a complex matrix `M` on a finite register `n` and a
state is a bare amplitude vector `ψ : QState n = n → ℂ`.

The conventions match the library's
`Qatlib.Concepts.MbqcFlow.FlowDecision.Inner`:
`⟨ψ|M|ψ⟩ = Inner ψ (M *ᵥ ψ)`, read in `ℝ` by taking the real part, which is the
whole value whenever `M` is Hermitian. The transport lemmas of
`Qatlib.Papers.QuantumPCA14.Discriminate.RepresentationBridge` identify
this with Mathlib's `EuclideanSpace` inner product, so Hilbert-space inequalities
(Cauchy–Schwarz in particular) can be used and then read back in matrix form.

Everything here is linearity and positivity bookkeeping for finite sums of local
terms; no spectral theory or unbounded operators are involved.
-/

namespace Qatlib.Papers.ScatteringQFT11.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The library inner product `⟨ψ|φ⟩ = ∑ᵢ conj(ψᵢ) φᵢ`, under a name that does not
collide with Mathlib's root type former `Inner`. Definitionally it is
`Qatlib.Concepts.MbqcFlow.FlowDecision.Inner`. -/
noncomputable def stateInner (ψ φ : QState n) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ψ φ

/-- The expectation `⟨ψ|M|ψ⟩` of the matrix observable `M` in the pure state `ψ`,
as a real number: the real part of `stateInner ψ (M *ᵥ ψ)`. For Hermitian `M` this
is the whole (real) expectation. -/
noncomputable def expectation (M : Matrix n n ℂ) (ψ : QState n) : ℝ :=
  (stateInner ψ (M *ᵥ ψ)).re

/-- The library inner product is conjugate-symmetric: `⟨φ|ψ⟩ = conj ⟨ψ|φ⟩`. -/
theorem stateInner_symm (ψ φ : QState n) : stateInner φ ψ = star (stateInner ψ φ) := by
  simp only [stateInner, Qatlib.Foundations.PureStateMath.Inner,
    dotProduct, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul, star_star]

/-- The expectation functional of a sum is the sum of the expectations. -/
theorem expectation_add (A B : Matrix n n ℂ) (ψ : QState n) :
    expectation (A + B) ψ = expectation A ψ + expectation B ψ := by
  simp only [expectation, stateInner, Qatlib.Foundations.PureStateMath.Inner,
    Matrix.add_mulVec, dotProduct_add, Complex.add_re]

/-- The expectation functional of a finite sum is the sum of the expectations. -/
theorem expectation_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ) (ψ : QState n) :
    expectation (∑ y ∈ s, A y) ψ = ∑ y ∈ s, expectation (A y) ψ := by
  classical
  induction s using Finset.induction with
  | empty => simp [expectation, stateInner, Qatlib.Foundations.PureStateMath.Inner]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, expectation_add, ih]

/-- Real scalars pull out of the expectation. -/
theorem expectation_smul_real (r : ℝ) (A : Matrix n n ℂ) (ψ : QState n) :
    expectation ((r : ℂ) • A) ψ = r * expectation A ψ := by
  simp only [expectation, stateInner, Qatlib.Foundations.PureStateMath.Inner,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A positive semidefinite observable has nonnegative expectation in every state. -/
theorem expectation_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (ψ : QState n) :
    0 ≤ expectation A ψ := by
  have h := hA.dotProduct_mulVec_nonneg ψ
  simp only [expectation, stateInner, Qatlib.Foundations.PureStateMath.Inner]
  exact (Complex.nonneg_iff.mp h).1

/-- The square of a Hermitian observable is positive semidefinite, so its expectation
is nonnegative. -/
theorem expectation_sq_nonneg {A : Matrix n n ℂ} (hA : Aᴴ = A) (ψ : QState n) :
    0 ≤ expectation (A * A) ψ := by
  have h' := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hA] at h'
  exact expectation_nonneg h' ψ

/-- A Hermitian observable has a real expectation: the imaginary part of
`⟨ψ|M|ψ⟩` vanishes. -/
theorem expectation_im_eq_zero {A : Matrix n n ℂ} (hA : Aᴴ = A) (ψ : QState n) :
    (stateInner ψ (A *ᵥ ψ)).im = 0 := by
  have hsymm : stateInner (A *ᵥ ψ) ψ = star (stateInner ψ (A *ᵥ ψ)) := stateInner_symm _ _
  have hadj : stateInner (A *ᵥ ψ) ψ = stateInner ψ (Aᴴ *ᵥ ψ) :=
    Qatlib.Foundations.PureStateMath.inner_mulVec_left_rect A ψ ψ
  rw [hadj, hA] at hsymm
  have him : (stateInner ψ (A *ᵥ ψ)).im = (star (stateInner ψ (A *ᵥ ψ))).im :=
    congrArg Complex.im hsymm
  rw [show (star (stateInner ψ (A *ᵥ ψ))).im = -(stateInner ψ (A *ᵥ ψ)).im from
    Complex.conj_im _] at him
  linarith

/-- For a Hermitian observable the absolute value of the expectation is the norm of
the complex number `⟨ψ|M|ψ⟩` (its imaginary part vanishes). -/
theorem abs_expectation_eq_norm {A : Matrix n n ℂ} (hA : Aᴴ = A) (ψ : QState n) :
    |expectation A ψ| = ‖stateInner ψ (A *ᵥ ψ)‖ := by
  have him := expectation_im_eq_zero hA ψ
  have hz : stateInner ψ (A *ᵥ ψ) = ((stateInner ψ (A *ᵥ ψ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [expectation, hz, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

/-- The fourth power of a Hermitian observable is positive semidefinite, so its
expectation is nonnegative. This is the positivity of the `λ₀ φ⁴/4!` lattice term. -/
theorem expectation_pow_four_nonneg {A : Matrix n n ℂ} (hA : Aᴴ = A) (ψ : QState n) :
    0 ≤ expectation (A ^ 4) ψ := by
  have hAA : (A * A).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self A
    rwa [hA] at h
  have h4 : ((A * A) ^ 2).PosSemidef := hAA.pow 2
  have hsq : A ^ 4 = (A * A) ^ 2 := by
    rw [pow_succ, pow_succ, pow_succ, pow_one, pow_two, ← mul_assoc]
  exact expectation_nonneg (hsq ▸ h4) ψ

end Qatlib.Papers.ScatteringQFT11.MainResults
