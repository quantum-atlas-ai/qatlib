/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessPhysical

/-!
# Matrix inner products and energy forms

This module defines `matInner`, the real quadratic form `matRayleigh`, and the eigenvalue
predicate `MatIsEigenvalue` for finite complex matrices. It supplies elementary additivity and
symmetry identities for these matrix-level quantities used in local Hamiltonian constructions.
See [KempeKitaevRegev2006].

## Main statements

* `matRayleigh`: The real part of the matrix quadratic form `matInner v (B.mulVec v)`, without
  division by the vector norm.
* `MatIsEigenvalue`: The predicate that the real number `μ` has a nonzero complex eigenvector
  for `H`.
* `matRayleigh_add`: The real matrix quadratic form is additive in the matrix argument.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical BigOperators Kronecker
open Matrix
open Qatlib.Papers.LocalHam06.MainResults

namespace Qatlib.Papers.LocalHam06.MainResults.TwoLocalGadget

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

set_option autoImplicit false

/-- The finite complex inner product, conjugate-linear in the first argument and linear in the
second. -/
def matInner {I : Type*} [Fintype I] (v w : I → ℂ) : ℂ :=
  ∑ i, starRingEnd ℂ (v i) * w i

/-- The real part of the matrix quadratic form `matInner v (B.mulVec v)`, without division by
the vector norm. -/
def matRayleigh {I : Type*} [Fintype I] (B : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  (matInner v (B.mulVec v)).re

/-- The predicate that the real number `μ` has a nonzero complex eigenvector for `H`. -/
def MatIsEigenvalue {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (μ : ℝ) : Prop :=
  ∃ v : I → ℂ, v ≠ 0 ∧ H.mulVec v = (μ : ℂ) • v

/-- The finite complex inner product is additive in its second argument. -/
theorem matInner_add_right {I : Type*} [Fintype I] (v x y : I → ℂ) :
    matInner v (x + y) = matInner v x + matInner v y := by
  simp [matInner, mul_add, Finset.sum_add_distrib]

/-- The finite complex inner product with zero in its first argument is zero. -/
theorem matInner_zero_left {I : Type*} [Fintype I] (w : I → ℂ) :
    matInner (0 : I → ℂ) w = 0 := by
  simp [matInner]

/-- The quadratic form of the zero matrix vanishes on every vector. -/
theorem matRayleigh_zero {I : Type*} [Fintype I] (v : I → ℂ) :
    matRayleigh (0 : Matrix I I ℂ) v = 0 := by
  simp [matRayleigh, matInner]

/-- The real matrix quadratic form is additive in the matrix argument. -/
theorem matRayleigh_add {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (v : I → ℂ) :
    matRayleigh (A + B) v = matRayleigh A v + matRayleigh B v := by
  unfold matRayleigh
  rw [Matrix.add_mulVec, matInner_add_right, Complex.add_re]

/-- Swapping the arguments of the finite complex inner product preserves its real part. -/
theorem matInner_re_comm {I : Type*} [Fintype I] (v w : I → ℂ) :
    (matInner v w).re = (matInner w v).re := by
  unfold matInner
  rw [Complex.re_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end Qatlib.Papers.LocalHam06.MainResults.TwoLocalGadget
