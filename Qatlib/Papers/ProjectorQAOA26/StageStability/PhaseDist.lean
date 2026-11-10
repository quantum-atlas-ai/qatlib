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

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I]

noncomputable def l2norm (x : I → ℂ) : ℝ := Real.sqrt (∑ i, Complex.normSq (x i))

def l2inner (u v : I → ℂ) : ℂ := ∑ i, star (u i) * v i

noncomputable def l2abs (u v : I → ℂ) : ℝ := Real.sqrt (Complex.normSq (l2inner u v))

theorem l2norm_nonneg (x : I → ℂ) : 0 ≤ l2norm x :=
  Real.sqrt_nonneg _

theorem l2abs_nonneg (u v : I → ℂ) : 0 ≤ l2abs u v := Real.sqrt_nonneg _

theorem l2inner_eq_dotProduct (u v : I → ℂ) : l2inner u v = star u ⬝ᵥ v := rfl

theorem l2norm_sq (x : I → ℂ) : l2norm x ^ 2 = ∑ i, Complex.normSq (x i) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

theorem l2abs_sq (u v : I → ℂ) : l2abs u v ^ 2 = Complex.normSq (l2inner u v) :=
  Real.sq_sqrt (Complex.normSq_nonneg _)

theorem eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  have h1 := sq_nonneg (a - b)
  nlinarith

theorem le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  by_contra hcon
  push Not at hcon
  have hlt : b ^ 2 < a ^ 2 := by nlinarith
  linarith

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

theorem normSq_sum_smul (z : ℂ) (v : I → ℂ) :
    ∑ i, Complex.normSq (z * v i) = Complex.normSq z * ∑ i, Complex.normSq (v i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_mul z (v i)

private theorem normSq_div' (a b : ℂ) :
    Complex.normSq (a / b) = Complex.normSq a / Complex.normSq b := by
  rw [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv, div_eq_mul_inv]

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

theorem l2inner_conj_right (u v : I → ℂ) :
    ∑ i, u i * star (v i) = star (l2inner u v) := by
  rw [l2inner, star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [star_mul, star_star]
    ring

theorem l2inner_symm (u v : I → ℂ) : l2inner v u = star (l2inner u v) := by
  rw [l2inner, l2inner, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul, star_star]

theorem l2inner_add_right (u v w : I → ℂ) :
    l2inner u (v + w) = l2inner u v + l2inner u w := by
  simp only [l2inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem l2inner_add_left (u v w : I → ℂ) :
    l2inner (u + v) w = l2inner u w + l2inner v w := by
  simp only [l2inner, Pi.add_apply, add_mul, Finset.sum_add_distrib, star_add]

theorem l2inner_neg_right (u v : I → ℂ) : l2inner u (-v) = -(l2inner u v) := by
  simp only [l2inner, Pi.neg_apply, mul_neg, ← Finset.sum_neg_distrib]

theorem l2inner_sub_right (u v w : I → ℂ) :
    l2inner u (v - w) = l2inner u v - l2inner u w := by
  simp only [l2inner, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem l2inner_smul_right (u v : I → ℂ) (z : ℂ) :
    l2inner u (z • v) = z * l2inner u v := by
  have h1 : l2inner u (z • v) = ∑ i, z * (star (u i) * v i) := by
    simp only [l2inner, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, l2inner, ← Finset.mul_sum]

theorem l2inner_smul_left (u v : I → ℂ) (z : ℂ) :
    l2inner (z • u) v = star z * l2inner u v := by
  have h1 : l2inner (z • u) v = ∑ i, star z * (star (u i) * v i) := by
    simp only [l2inner, Pi.smul_apply, smul_eq_mul, star_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, l2inner, ← Finset.mul_sum]

theorem l2norm_smul (z : ℂ) (x : I → ℂ) :
    l2norm (z • x) = Real.sqrt (Complex.normSq z) * l2norm x := by
  refine eq_of_sq_eq (l2norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2norm_nonneg x)) ?_
  have h2 : (Real.sqrt (Complex.normSq z) * l2norm x) ^ 2
      = Complex.normSq z * l2norm x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Complex.normSq_nonneg z)]
  rw [h2, l2norm_sq]
  show ∑ i, Complex.normSq (z * x i) = Complex.normSq z * l2norm x ^ 2
  rw [normSq_sum_smul, l2norm_sq]

theorem sum_normSq_eq_re (y : I → ℂ) :
    ∑ i, Complex.normSq (y i) = (l2inner y y).re := by
  rw [l2inner_eq_dotProduct]
  show ∑ i, Complex.normSq (y i) = (∑ i, star (y i) * y i).re
  rw [sum_re (fun i => star (y i) * y i)]
  exact Finset.sum_congr rfl fun i _ => by
    have h0 := Complex.normSq_eq_conj_mul_self (z := y i)
    rw [Complex.star_def, ← h0, Complex.ofReal_re]

noncomputable def phaseFactor (u v : I → ℂ) : ℂ :=
  if l2inner u v = 0 then 1 else star (l2inner u v) / (l2abs u v : ℂ)

noncomputable def phaseAlign (u v : I → ℂ) : I → ℂ := phaseFactor u v • v

noncomputable def phaseDist (u v : I → ℂ) : ℝ := l2norm (u - phaseAlign u v)

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

theorem l2norm_phaseAlign (u v : I → ℂ) : l2norm (phaseAlign u v) = l2norm v := by
  rw [phaseAlign, l2norm_smul, normSq_phaseFactor, Real.sqrt_one, one_mul]

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

theorem phaseDist_nonneg (u v : I → ℂ) : 0 ≤ phaseDist u v := l2norm_nonneg _

theorem phaseDist_sq (u v : I → ℂ) :
    phaseDist u v ^ 2 = l2norm u ^ 2 + l2norm v ^ 2 - 2 * l2abs u v := by
  rw [phaseDist, l2norm_sub_sq, l2inner_phaseAlign, Complex.ofReal_re, l2norm_phaseAlign]

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

theorem l2abs_smul_unit (u v : I → ℂ) {z : ℂ} (hz : Complex.normSq z = 1) :
    l2abs u (z • v) = l2abs u v := by
  rw [l2abs, l2inner_smul_right u v z, Complex.normSq_mul, hz, one_mul, l2abs]

theorem phaseDist_smul_unit (u v : I → ℂ) {z : ℂ} (hz : Complex.normSq z = 1) :
    phaseDist u (z • v) = phaseDist u v := by
  refine eq_of_sq_eq (phaseDist_nonneg u (z • v)) (phaseDist_nonneg u v) ?_
  rw [phaseDist_sq, phaseDist_sq, l2norm_smul, Real.sqrt_eq_one.mpr hz, one_mul,
    l2abs_smul_unit u v hz]

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

theorem l2inner_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (x y : I → ℂ) : l2inner (A *ᵥ x) (A *ᵥ y) = l2inner x y := by
  have hstar : Aᴴ * A = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hA
  rw [l2inner_eq_dotProduct, l2inner_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]

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

theorem l2abs_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (u v : I → ℂ) : l2abs (A *ᵥ u) (A *ᵥ v) = l2abs u v := by
  rw [l2abs, l2abs, l2inner_mulVec hA]

theorem phaseDist_mulVec {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (u v : I → ℂ) : phaseDist (A *ᵥ u) (A *ᵥ v) = phaseDist u v := by
  refine eq_of_sq_eq (phaseDist_nonneg (A *ᵥ u) (A *ᵥ v)) (phaseDist_nonneg u v) ?_
  rw [phaseDist_sq, phaseDist_sq, l2norm_mulVec hA, l2norm_mulVec hA, l2abs_mulVec hA]

end Qatlib.Papers.ProjectorQAOA26.StageStability

end UnitaryAction
