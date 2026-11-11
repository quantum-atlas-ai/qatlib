/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCellAutomata96.MainResults.ParityReduction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Normal forms of parity-invariant cell pairs

This module studies symmetric two-component matrices and proves their phase and trigonometric
normal forms under unitarity. It uses conjugate-product identities and exponential formulas to
express any parity-invariant unitary cell pair as a phase multiple of `cellPairMatrix`. See
[Meyer1996a].

## Main statements

* `parity_unitary_normal_form`: If `par2 x y` times its adjoint is the identity, its two
  coefficients have the form of a common phase times `(i * sin φ, cos φ)`.
* `parity_unitary_eq_phase_smul_cellPair`: Every two-component matrix invariant under the
  component swap and satisfying `S * star S = 1` is a phase multiple of `cellPairMatrix θ` for
  some real parameters.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Complex Matrix
open scoped Matrix
open Qatlib.Concepts.QcaDynamics.ParityWeights

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The symmetric two-by-two matrix with diagonal entry `x` and off-diagonal entry `y`. -/
def par2 (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![x, y; y, x]

/-- The `(0, 0)` entry of `par2 x y` is `x`. -/
@[simp] lemma par2_zero_zero (x y : ℂ) : par2 x y 0 0 = x := rfl

/-- The `(0, 1)` entry of `par2 x y` is `y`. -/
@[simp] lemma par2_zero_one (x y : ℂ) : par2 x y 0 1 = y := rfl

/-- The `(1, 0)` entry of `par2 x y` is `y`. -/
@[simp] lemma par2_one_zero (x y : ℂ) : par2 x y 1 0 = y := rfl

/-- The `(1, 1)` entry of `par2 x y` is `x`. -/
@[simp] lemma par2_one_one (x y : ℂ) : par2 x y 1 1 = x := rfl

/-- The product of `par2 x y` with its adjoint has diagonal `x * star x + y * star y` and
off-diagonal `x * star y + y * star x`. See [Meyer1996a]. -/
lemma par2_mul_conjTranspose (x y : ℂ) :
    par2 x y * (par2 x y)ᴴ =
      par2 (x * star x + y * star y) (x * star y + y * star x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [par2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The symmetric matrix `par2 x y` equals the identity exactly when `x = 1` and `y = 0`. -/
lemma par2_eq_one_iff (x y : ℂ) : par2 x y = 1 ↔ x = 1 ∧ y = 0 := by
  constructor
  · intro h
    have h00 : x = 1 := by simpa [par2] using congrFun (congrFun h 0) 0
    have h01 : y = 0 := by simpa [par2] using congrFun (congrFun h 0) 1
    exact ⟨h00, h01⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [par2]

/-- A complex number whose product with its conjugate is one has norm one. -/
lemma norm_eq_one_of_mul_conj {z : ℂ} (h : z * star z = 1) : ‖z‖ = 1 := by
  have hns : Complex.normSq z = 1 := by
    have h' : z * (starRingEnd ℂ) z = 1 := by simpa using h
    rw [Complex.mul_conj] at h'
    exact Complex.ofReal_inj.mp h'
  have h2 : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm, hns]
  nlinarith [norm_nonneg z]

/-- A complex number with conjugate product one equals the exponential of its argument times the
imaginary unit. -/
lemma eq_exp_arg_mul_I {z : ℂ} (h : z * star z = 1) :
    z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have h' := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_eq_one_of_mul_conj h] at h'
  simpa using h'.symm

/-- The exponential of `i * (s + t)` factors into the product of the two phase exponentials. -/
lemma exp_add_real_mul_I (s t : ℝ) :
    Complex.exp (((s + t : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((s : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exponential of `i * (s - t)` factors into the phase of `s` times the phase of `-t`. -/
lemma exp_sub_real_mul_I (s t : ℝ) :
    Complex.exp (((s - t : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((s : ℂ) * Complex.I) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The half-sum of opposite phase exponentials equals the complex embedding of the real cosine. -/
lemma exp_cos (t : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) / 2
      = (Real.cos t : ℂ) := by
  have e1 : Complex.exp ((t : ℂ) * Complex.I)
      = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := Complex.exp_ofReal_mul_I t
  have e2 : Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
      = (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    have h := Complex.exp_ofReal_mul_I (-t)
    rw [Real.cos_neg, Real.sin_neg] at h
    simpa using! h
  rw [e1, e2]
  ring

/-- The half-difference of opposite phase exponentials equals the imaginary unit times the real
sine. -/
lemma exp_sin (t : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) / 2
      = Complex.I * (Real.sin t : ℂ) := by
  have e1 : Complex.exp ((t : ℂ) * Complex.I)
      = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := Complex.exp_ofReal_mul_I t
  have e2 : Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
      = (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    have h := Complex.exp_ofReal_mul_I (-t)
    rw [Real.cos_neg, Real.sin_neg] at h
    simpa using! h
  rw [e1, e2]
  ring

/-- The half-sum of phases at `s + t` and `s - t` equals the phase at `s` times `cos t`. -/
lemma exp_cos_split (s t : ℝ) :
    (Complex.exp (((s + t : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((s - t : ℝ) : ℂ) * Complex.I)) / 2
      = Complex.exp ((s : ℂ) * Complex.I) * (Real.cos t : ℂ) := by
  rw [exp_add_real_mul_I, exp_sub_real_mul_I, ← exp_cos t]
  ring

/-- The half-difference of phases at `s + t` and `s - t` equals the phase at `s` times `i * sin
t`. -/
lemma exp_sin_split (s t : ℝ) :
    (Complex.exp (((s + t : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((s - t : ℝ) : ℂ) * Complex.I)) / 2
      = Complex.exp ((s : ℂ) * Complex.I) * (Complex.I * (Real.sin t : ℂ)) := by
  rw [exp_add_real_mul_I, exp_sub_real_mul_I, ← exp_sin t]
  ring

/-- Adding π to a real phase negates its complex exponential. -/
lemma exp_add_pi (w : ℝ) :
    Complex.exp ((((w + Real.pi) : ℝ) : ℂ) * Complex.I) = -Complex.exp ((w : ℂ) * Complex.I) := by
  rw [exp_add_real_mul_I, Complex.exp_pi_mul_I]
  ring

/-- If `par2 x y` times its adjoint is the identity, its two coefficients have the form of a
common phase times `(i * sin φ, cos φ)`. See [Meyer1996a]. -/
theorem parity_unitary_normal_form {x y : ℂ} (h : par2 x y * (par2 x y)ᴴ = 1) :
    ∃ ψ φ : ℝ, x = Complex.exp ((ψ : ℂ) * Complex.I) * (Complex.I * (Real.sin φ : ℂ)) ∧
      y = Complex.exp ((ψ : ℂ) * Complex.I) * (Real.cos φ : ℂ) := by
  have hpar : par2 (x * star x + y * star y) (x * star y + y * star x) = 1 := by
    rw [← par2_mul_conjTranspose x y]; exact h
  obtain ⟨h1, h2⟩ := (par2_eq_one_iff _ _).mp hpar
  have hlp : (x + y) * star (x + y) = 1 := by
    calc (x + y) * star (x + y) = (x * star x + y * star y) + (x * star y + y * star x) := by
          rw [star_add]; ring
      _ = 1 := by rw [h1, h2]; ring
  have hlm : (x - y) * star (x - y) = 1 := by
    calc (x - y) * star (x - y) = (x * star x + y * star y) - (x * star y + y * star x) := by
          rw [star_sub]; ring
      _ = 1 := by rw [h1, h2]; ring
  set A : ℝ := Complex.arg (x + y)
  set B : ℝ := Complex.arg (x - y)
  have hA : x + y = Complex.exp ((A : ℂ) * Complex.I) := eq_exp_arg_mul_I hlp
  have hB : x - y = Complex.exp ((B : ℂ) * Complex.I) := eq_exp_arg_mul_I hlm
  obtain ⟨ψ, φ, hψ, hφ⟩ : ∃ ψ φ : ℝ, ψ + φ = A ∧ ψ - φ = B - Real.pi :=
    ⟨(A + B) / 2 - Real.pi / 2, (A - B) / 2 + Real.pi / 2, by ring, by ring⟩
  refine ⟨ψ, φ, ?_, ?_⟩
  · have hA' : (A : ℂ) = ((ψ + φ : ℝ) : ℂ) := by rw [hψ]
    have hB' : (B : ℂ) = (((ψ - φ) + Real.pi : ℝ) : ℂ) := by
      have hB2 : B = (ψ - φ) + Real.pi := by linarith [hφ]
      rw [hB2]
    have hx : x = (Complex.exp ((A : ℂ) * Complex.I) + Complex.exp ((B : ℂ) * Complex.I)) / 2 := by
      rw [← hA, ← hB]; ring
    rw [hx, hA', hB', exp_add_pi]
    exact exp_sin_split ψ φ
  · have hA' : (A : ℂ) = ((ψ + φ : ℝ) : ℂ) := by rw [hψ]
    have hB' : (B : ℂ) = (((ψ - φ) + Real.pi : ℝ) : ℂ) := by
      have hB2 : B = (ψ - φ) + Real.pi := by linarith [hφ]
      rw [hB2]
    have hy : y = (Complex.exp ((A : ℂ) * Complex.I) - Complex.exp ((B : ℂ) * Complex.I)) / 2 := by
      rw [← hA, ← hB]; ring
    rw [hy, hA', hB', exp_add_pi]
    rw [sub_neg_eq_add]
    exact exp_cos_split ψ φ

/-- Every two-component matrix invariant under the component swap and satisfying `S * star S =
1` is a phase multiple of `cellPairMatrix θ` for some real parameters. See [Meyer1996a]. -/
theorem parity_unitary_eq_phase_smul_cellPair {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hpar : P2 * S * P2 = S) (hU : S * star S = 1) :
    ∃ (ψ θ : ℝ), S = (Complex.exp ((ψ : ℂ) * Complex.I)) • cellPairMatrix θ := by
  obtain ⟨h00, h01⟩ := (parity_iff_equal_entries S).mp hpar
  have hS : S = par2 (S 0 0) (S 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [par2, h00, h01]
  have hpar2 : par2 (S 0 0) (S 0 1) * (par2 (S 0 0) (S 0 1))ᴴ = 1 := by
    rw [← hS]
    simpa [Matrix.star_eq_conjTranspose] using hU
  obtain ⟨ψ, φ, hx, hy⟩ := parity_unitary_normal_form hpar2
  refine ⟨ψ, φ, ?_⟩
  rw [hS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [par2, cellPairMatrix, Matrix.smul_apply, hx, hy]

end Qatlib.Papers.QCellAutomata96.MainResults
