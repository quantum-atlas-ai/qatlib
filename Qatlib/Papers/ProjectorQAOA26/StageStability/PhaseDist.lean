/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Phase-aligned distance for finite complex vectors

This module defines explicit Euclidean norms, complex inner products, and `phaseDist` by
aligning the global phase of one vector to the other. It proves optimality of the alignment, the
squared-distance formula, and invariance under unitary matrix action, establishing the phase
geometry used in [ZhouAnLiu2026].

## Main statements

* `phaseDist_sq`: The squared phase distance is the sum of the squared vector norms minus twice
  the overlap magnitude. For normalized vectors this gives the phase geometry formula in
  [ZhouAnLiu2026].
* `phaseDist_le_of_unit`: Phase distance is no greater than the Euclidean distance obtained
  using any scalar phase of squared magnitude one.
* `phaseDist_mulVec`: A common unitary matrix action preserves phase distance.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I]

/-- The Euclidean norm of a finite complex vector, defined as the square root of the sum of
squared coordinate magnitudes. -/
noncomputable def l2norm (x : I → ℂ) : ℝ := Real.sqrt (∑ i, Complex.normSq (x i))

/-- The complex inner product obtained by summing `star (u i) * v i` over the coordinates. -/
def l2inner (u v : I → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- The magnitude of `l2inner u v`, expressed as the square root of its squared complex norm. -/
noncomputable def l2abs (u v : I → ℂ) : ℝ := Real.sqrt (Complex.normSq (l2inner u v))

/-- The explicit Euclidean vector norm is nonnegative. -/
theorem l2norm_nonneg (x : I → ℂ) : 0 ≤ l2norm x :=
  Real.sqrt_nonneg _

/-- The magnitude of the explicit inner product is nonnegative. -/
theorem l2abs_nonneg (u v : I → ℂ) : 0 ≤ l2abs u v := Real.sqrt_nonneg _

/-- The explicit inner product equals the dot product of the conjugate of the first vector with
the second. -/
theorem l2inner_eq_dotProduct (u v : I → ℂ) : l2inner u v = star u ⬝ᵥ v := rfl

/-- The squared Euclidean norm is the sum of squared coordinate magnitudes. -/
theorem l2norm_sq (x : I → ℂ) : l2norm x ^ 2 = ∑ i, Complex.normSq (x i) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- The squared inner-product magnitude equals the squared complex norm of the inner product. -/
theorem l2abs_sq (u v : I → ℂ) : l2abs u v ^ 2 = Complex.normSq (l2inner u v) :=
  Real.sq_sqrt (Complex.normSq_nonneg _)

/-- Two nonnegative real numbers with equal squares are equal. -/
theorem eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  have h1 := sq_nonneg (a - b)
  nlinarith

/-- A comparison of squares implies the corresponding real comparison when the upper number is
nonnegative. -/
theorem le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  by_contra hcon
  push Not at hcon
  have hlt : b ^ 2 < a ^ 2 := by nlinarith
  linarith

/-- The explicit Euclidean norm vanishes exactly for the zero vector. -/
theorem l2norm_eq_zero (x : I → ℂ) : l2norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : ∑ i, Complex.normSq (x i) = 0 := by
      have hsq := l2norm_sq x
      rw [h] at hsq
      simpa using hsq.symm
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hs i (Finset.mem_univ i))
  · intro h
    subst h
    simp [l2norm]

/-- The sum of squared magnitudes after multiplication by a complex scalar is its squared
magnitude times the original sum. -/
theorem normSq_sum_smul (z : ℂ) (v : I → ℂ) :
    ∑ i, Complex.normSq (z * v i) = Complex.normSq z * ∑ i, Complex.normSq (v i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_mul z (v i)

/-- The squared complex norm of a quotient equals the quotient of the squared norms. -/
private theorem normSq_div' (a b : ℂ) :
    Complex.normSq (a / b) = Complex.normSq a / Complex.normSq b := by
  rw [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv, div_eq_mul_inv]

/-- The real part of a complex number is at most the square root of its squared norm. -/
private theorem re_le_l2abs (z : ℂ) : z.re ≤ Real.sqrt (Complex.normSq z) := by
  by_cases hz : z.re ≤ Real.sqrt (Complex.normSq z)
  · exact hz
  · push Not at hz
    have hs2 : Real.sqrt (Complex.normSq z) ^ 2 = Complex.normSq z :=
      Real.sq_sqrt (Complex.normSq_nonneg z)
    have h1 : z.re ^ 2 ≤ Complex.normSq z := by
      rw [Complex.normSq_apply]
      nlinarith
    have hpos : 0 ≤ z.re := (Real.sqrt_nonneg _).trans hz.le
    have h0 : 0 ≤ Real.sqrt (Complex.normSq z) := Real.sqrt_nonneg _
    have key : (z.re - Real.sqrt (Complex.normSq z)) * (z.re + Real.sqrt (Complex.normSq z)) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith [key]

/-- Taking the real part commutes with a finite sum of complex numbers. -/
private theorem sum_re (f : I → ℂ) : (∑ i, f i).re = ∑ i, (f i).re := by
  classical
  have main : ∀ (t : Finset I), t ⊆ Finset.univ → (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
        intro _hsub
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re,
          ih (fun b _ => Finset.mem_univ b)]
  exact main Finset.univ (fun _ _ => Finset.mem_univ _)

/-- Summing the first vector times the conjugate of the second gives the conjugate of their
explicit inner product. -/
theorem l2inner_conj_right (u v : I → ℂ) :
    ∑ i, u i * star (v i) = star (l2inner u v) := by
  rw [l2inner, star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [star_mul, star_star]
    ring

/-- Interchanging the arguments of the explicit inner product conjugates its value. -/
theorem l2inner_symm (u v : I → ℂ) : l2inner v u = star (l2inner u v) := by
  rw [l2inner, l2inner, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul, star_star]

/-- The explicit inner product is additive in its second argument. -/
theorem l2inner_add_right (u v w : I → ℂ) :
    l2inner u (v + w) = l2inner u v + l2inner u w := by
  simp only [l2inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The explicit inner product is additive in its first argument. -/
theorem l2inner_add_left (u v w : I → ℂ) :
    l2inner (u + v) w = l2inner u w + l2inner v w := by
  simp only [l2inner, Pi.add_apply, add_mul, Finset.sum_add_distrib, star_add]

/-- Negating the second argument negates the explicit inner product. -/
theorem l2inner_neg_right (u v : I → ℂ) : l2inner u (-v) = -(l2inner u v) := by
  simp only [l2inner, Pi.neg_apply, mul_neg, ← Finset.sum_neg_distrib]

/-- The explicit inner product distributes over subtraction in its second argument. -/
theorem l2inner_sub_right (u v w : I → ℂ) :
    l2inner u (v - w) = l2inner u v - l2inner u w := by
  simp only [l2inner, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Scaling the second argument multiplies the explicit inner product by the same complex
scalar. -/
theorem l2inner_smul_right (u v : I → ℂ) (z : ℂ) :
    l2inner u (z • v) = z * l2inner u v := by
  have h1 : l2inner u (z • v) = ∑ i, z * (star (u i) * v i) := by
    simp only [l2inner, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, l2inner, ← Finset.mul_sum]

/-- Scaling the first argument multiplies the explicit inner product by the conjugate scalar. -/
theorem l2inner_smul_left (u v : I → ℂ) (z : ℂ) :
    l2inner (z • u) v = star z * l2inner u v := by
  have h1 : l2inner (z • u) v = ∑ i, star z * (star (u i) * v i) := by
    simp only [l2inner, Pi.smul_apply, smul_eq_mul, star_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, l2inner, ← Finset.mul_sum]

/-- Scaling a vector by a complex scalar multiplies its Euclidean norm by the scalar's
magnitude. -/
theorem l2norm_smul (z : ℂ) (x : I → ℂ) :
    l2norm (z • x) = Real.sqrt (Complex.normSq z) * l2norm x := by
  refine eq_of_sq_eq (l2norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2norm_nonneg x)) ?_
  have h2 : (Real.sqrt (Complex.normSq z) * l2norm x) ^ 2
      = Complex.normSq z * l2norm x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Complex.normSq_nonneg z)]
  rw [h2, l2norm_sq]
  show ∑ i, Complex.normSq (z * x i) = Complex.normSq z * l2norm x ^ 2
  rw [normSq_sum_smul, l2norm_sq]

/-- The sum of squared coordinate magnitudes equals the real part of the vector's inner product
with itself. -/
theorem sum_normSq_eq_re (y : I → ℂ) :
    ∑ i, Complex.normSq (y i) = (l2inner y y).re := by
  rw [l2inner_eq_dotProduct]
  show ∑ i, Complex.normSq (y i) = (∑ i, star (y i) * y i).re
  rw [sum_re (fun i => star (y i) * y i)]
  exact Finset.sum_congr rfl fun i _ => by
    have h0 := Complex.normSq_eq_conj_mul_self (z := y i)
    rw [Complex.star_def, ← h0, Complex.ofReal_re]

/-- The unit phase that makes the overlap of `u` with the scaled `v` real and nonnegative, using
one when the overlap vanishes. -/
noncomputable def phaseFactor (u v : I → ℂ) : ℂ :=
  if l2inner u v = 0 then 1 else star (l2inner u v) / (l2abs u v : ℂ)

/-- The second vector multiplied by its aligning phase factor relative to the first vector. -/
noncomputable def phaseAlign (u v : I → ℂ) : I → ℂ := phaseFactor u v • v

/-- The Euclidean distance from the first vector to the phase-aligned second vector. -/
noncomputable def phaseDist (u v : I → ℂ) : ℝ := l2norm (u - phaseAlign u v)

/-- The aligning phase factor has squared magnitude one. -/
theorem normSq_phaseFactor (u v : I → ℂ) : Complex.normSq (phaseFactor u v) = 1 := by
  unfold phaseFactor
  by_cases h : l2inner u v = 0
  · simp [h]
  · have hne : Complex.normSq (l2inner u v) ≠ 0 := fun hc =>
      h (Complex.normSq_eq_zero.mp hc)
    have hcast : Complex.normSq ((l2abs u v : ℂ)) = Complex.normSq (l2inner u v) := by
      rw [Complex.normSq_ofReal, ← pow_two, l2abs_sq]
    have hst : Complex.normSq (star (l2inner u v)) = Complex.normSq (l2inner u v) := by
      rw [Complex.star_def]
      exact Complex.normSq_conj _
    rw [if_neg h, normSq_div', hst, hcast, div_self hne]

/-- The inner product of `u` with `phaseAlign u v` is the nonnegative real overlap magnitude. -/
theorem l2inner_phaseAlign (u v : I → ℂ) :
    l2inner u (phaseAlign u v) = (l2abs u v : ℂ) := by
  rw [phaseAlign, l2inner_smul_right, phaseFactor]
  by_cases h : l2inner u v = 0
  · simp [h, l2abs]
  · have hcast : star (l2inner u v) * l2inner u v = (Complex.normSq (l2inner u v) : ℂ) := by
      rw [Complex.star_def]
      exact (Complex.normSq_eq_conj_mul_self).symm
    have hne : Complex.normSq (l2inner u v) ≠ 0 := fun hc =>
      h (Complex.normSq_eq_zero.mp hc)
    have hne2 : (l2abs u v : ℂ) ≠ 0 := by
      intro hc
      refine hne ?_
      rw [← l2abs_sq, Complex.ofReal_eq_zero.mp hc]
      simp
    rw [if_neg h, div_mul_eq_mul_div, hcast, ← l2abs_sq, Complex.ofReal_pow]
    field_simp

/-- Phase alignment preserves the Euclidean norm of the second vector. -/
theorem l2norm_phaseAlign (u v : I → ℂ) : l2norm (phaseAlign u v) = l2norm v := by
  rw [phaseAlign, l2norm_smul, normSq_phaseFactor, Real.sqrt_one, one_mul]

/-- The squared norm of a vector difference is the sum of the squared norms minus twice the real
part of their inner product. -/
theorem l2norm_sub_sq (x y : I → ℂ) :
    l2norm (x - y) ^ 2 = l2norm x ^ 2 + l2norm y ^ 2 - 2 * (l2inner x y).re := by
  rw [l2norm_sq (x - y), l2norm_sq x, l2norm_sq y]
  simp only [Pi.sub_apply, Complex.normSq_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hkey : ∑ i, (x i * (starRingEnd ℂ) (y i)).re = (l2inner x y).re := by
    have hc : ∑ i, x i * (starRingEnd ℂ) (y i) = star (l2inner x y) := by
      have h0 := l2inner_conj_right x y
      rw [Complex.star_def] at h0 ⊢
      exact h0
    rw [← sum_re (fun i => x i * (starRingEnd ℂ) (y i)), hc, Complex.star_def]
    exact Complex.conj_re _
  rw [hkey]

/-- Phase distance is nonnegative. -/
theorem phaseDist_nonneg (u v : I → ℂ) : 0 ≤ phaseDist u v := l2norm_nonneg _

/-- The squared phase distance is the sum of the squared vector norms minus twice the overlap
magnitude. For normalized vectors this gives the phase geometry formula in [ZhouAnLiu2026]. -/
theorem phaseDist_sq (u v : I → ℂ) :
    phaseDist u v ^ 2 = l2norm u ^ 2 + l2norm v ^ 2 - 2 * l2abs u v := by
  rw [phaseDist, l2norm_sub_sq, l2inner_phaseAlign, Complex.ofReal_re, l2norm_phaseAlign]

/-- Phase distance is no greater than the Euclidean distance obtained using any scalar phase of
squared magnitude one. -/
theorem phaseDist_le_of_unit (u v : I → ℂ) {z : ℂ} (hz : Complex.normSq z = 1) :
    phaseDist u v ≤ l2norm (u - z • v) := by
  refine le_of_sq_le (phaseDist_nonneg u v) (l2norm_nonneg _) ?_
  rw [phaseDist_sq, l2norm_sub_sq, l2norm_smul, Real.sqrt_eq_one.mpr hz, one_mul,
    l2inner_smul_right u v z]
  have hle : (z * l2inner u v).re ≤ l2abs u v := by
    have h0 : (z * l2inner u v).re ≤ Real.sqrt (Complex.normSq (z * l2inner u v)) :=
      re_le_l2abs _
    rw [Complex.normSq_mul, hz, one_mul] at h0
    exact h0
  linarith

/-- Multiplying the second vector by a unit phase preserves the inner-product magnitude. -/
theorem l2abs_smul_unit (u v : I → ℂ) {z : ℂ} (hz : Complex.normSq z = 1) :
    l2abs u (z • v) = l2abs u v := by
  rw [l2abs, l2inner_smul_right u v z, Complex.normSq_mul, hz, one_mul, l2abs]

/-- Multiplying the second vector by a unit phase preserves phase distance. -/
theorem phaseDist_smul_unit (u v : I → ℂ) {z : ℂ} (hz : Complex.normSq z = 1) :
    phaseDist u (z • v) = phaseDist u v := by
  refine eq_of_sq_eq (phaseDist_nonneg u (z • v)) (phaseDist_nonneg u v) ?_
  rw [phaseDist_sq, phaseDist_sq, l2norm_smul, Real.sqrt_eq_one.mpr hz, one_mul,
    l2abs_smul_unit u v hz]

/-- Phase distance is symmetric in its two arguments. -/
theorem phaseDist_symm (u v : I → ℂ) : phaseDist u v = phaseDist v u := by
  have habs : l2abs u v = l2abs v u := by
    rw [l2abs, l2abs, l2inner_symm, Complex.star_def]
    exact congrArg Real.sqrt (Complex.normSq_conj _)
  refine eq_of_sq_eq (phaseDist_nonneg u v) (phaseDist_nonneg v u) ?_
  rw [phaseDist_sq, phaseDist_sq, habs]
  ring

end Qatlib.Papers.ProjectorQAOA26.StageStability

section UnitaryAction

open scoped BigOperators Matrix

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A common unitary matrix action preserves the explicit inner product. -/
theorem l2inner_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (x y : I → ℂ) : l2inner (A *ᵥ x) (A *ᵥ y) = l2inner x y := by
  have hstar : Aᴴ * A = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hA
  rw [l2inner_eq_dotProduct, l2inner_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]

/-- Unitary matrix action preserves the explicit Euclidean norm. -/
theorem l2norm_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (x : I → ℂ) : l2norm (A *ᵥ x) = l2norm x := by
  refine eq_of_sq_eq (l2norm_nonneg _) (l2norm_nonneg _) ?_
  calc l2norm (A *ᵥ x) ^ 2 = (l2inner (A *ᵥ x) (A *ᵥ x)).re := by
        rw [l2norm_sq]
        exact sum_normSq_eq_re _
    _ = (l2inner x x).re := by rw [l2inner_mulVec hA x x]
    _ = l2norm x ^ 2 := by
        rw [l2norm_sq]
        exact (sum_normSq_eq_re x).symm

/-- A common unitary matrix action preserves the inner-product magnitude. -/
theorem l2abs_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (u v : I → ℂ) : l2abs (A *ᵥ u) (A *ᵥ v) = l2abs u v := by
  rw [l2abs, l2abs, l2inner_mulVec hA]

/-- A common unitary matrix action preserves phase distance. -/
theorem phaseDist_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (u v : I → ℂ) : phaseDist (A *ᵥ u) (A *ᵥ v) = phaseDist u v := by
  refine eq_of_sq_eq (phaseDist_nonneg (A *ᵥ u) (A *ᵥ v)) (phaseDist_nonneg u v) ?_
  rw [phaseDist_sq, phaseDist_sq, l2norm_mulVec hA, l2norm_mulVec hA, l2abs_mulVec hA]

end Qatlib.Papers.ProjectorQAOA26.StageStability

end UnitaryAction
