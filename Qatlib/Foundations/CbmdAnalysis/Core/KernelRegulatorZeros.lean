/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelContourBounds
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

noncomputable def integerLatticeExponential (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) - 1

noncomputable def integerContourDenominator (m : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  (z + Complex.I) * integerRegulator m z * integerLatticeExponential a z

private theorem row_normalization_ne_zero (r : ℤ) : -(r : ℂ) - 2 * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

private theorem top_normalization_ne_zero : (-3 : ℂ) * Complex.I ≠ 0 := by simp

theorem integerRegulator_differentiable (m : ℕ) : Differentiable ℂ (integerRegulator m) := by
  unfold integerRegulator
  apply Differentiable.mul
  · fun_prop
  · apply Differentiable.fun_finsetProd
    intro r _
    fun_prop

theorem integerRegulator_eq_zero_iff (m : ℕ) (z : ℂ) :
    integerRegulator m z = 0 ↔ z = 2 * Complex.I ∨
      ∃ r ∈ Finset.Icc (-(m : ℤ)) m, z = (r : ℂ) + Complex.I := by
  rw [integerRegulator, mul_eq_zero]
  simp only [div_eq_zero_iff, top_normalization_ne_zero, row_normalization_ne_zero,
    or_false, Finset.prod_eq_zero_iff]
  simp [sub_eq_iff_eq_add, add_comm]

theorem integerRegulator_real_ne_zero (m : ℕ) (x : ℝ) : integerRegulator m (x : ℂ) ≠ 0 := by
  intro h
  rcases (integerRegulator_eq_zero_iff m x).mp h with htop | ⟨r, _, hr⟩
  · have hi := congrArg Complex.im htop
    norm_num at hi
  · have hi := congrArg Complex.im hr
    norm_num at hi

theorem integerTopPoleProduct_ne_zero (m : ℕ) : integerTopPoleProduct m ≠ 0 := by
  unfold integerTopPoleProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  apply div_ne_zero _ (row_normalization_ne_zero r)
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem integerRowPoleProduct_ne_zero (m : ℕ) (r : ℤ)
    (_hr : r ∈ Finset.Icc (-(m : ℤ)) m) : integerRowPoleProduct m r ≠ 0 := by
  unfold integerRowPoleProduct
  apply mul_ne_zero
  · apply div_ne_zero _ top_normalization_ne_zero
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply div_ne_zero _ (row_normalization_ne_zero j)
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.I_re,
      add_zero, sub_zero, Complex.zero_re] at hreal
    have he : r = j := by exact_mod_cast (sub_eq_zero.mp hreal)
    exact (Finset.mem_erase.mp hj).1 he.symm

theorem integerRegulator_hasDerivAt_top (m : ℕ) :
    HasDerivAt (integerRegulator m)
      (integerTopPoleProduct m / (-3 * Complex.I)) (2 * Complex.I) := by
  let G : ℂ → ℂ := fun z => ∏ r ∈ Finset.Icc (-(m : ℤ)) m,
    (z - (r : ℂ) - Complex.I) / (-(r : ℂ) - 2 * Complex.I)
  have hG : Differentiable ℂ G := by
    apply Differentiable.fun_finsetProd
    intro r _
    fun_prop
  have h := (((hasDerivAt_id (2 * Complex.I)).sub_const (2 * Complex.I)).div_const
    (-3 * Complex.I)).mul (hG (2 * Complex.I)).hasDerivAt
  convert! h using 1
  simp only [id_eq, sub_self, zero_div, zero_mul, add_zero, G, integerTopPoleProduct]
  ring

theorem integerRegulator_hasDerivAt_row (m : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    HasDerivAt (integerRegulator m)
      (integerRowPoleProduct m r / (-(r : ℂ) - 2 * Complex.I)) ((r : ℂ) + Complex.I) := by
  let G : ℂ → ℂ := fun z => ((z - 2 * Complex.I) / (-3 * Complex.I)) *
    ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r,
      (z - (j : ℂ) - Complex.I) / (-(j : ℂ) - 2 * Complex.I)
  have hG : Differentiable ℂ G := by
    apply Differentiable.mul
    · fun_prop
    · apply Differentiable.fun_finsetProd
      intro j _
      fun_prop
  have heq : integerRegulator m = fun z =>
      ((z - (r : ℂ) - Complex.I) / (-(r : ℂ) - 2 * Complex.I)) * G z := by
    funext z
    unfold integerRegulator
    rw [← Finset.mul_prod_erase _
      (fun j : ℤ => (z - (j : ℂ) - Complex.I) / (-(j : ℂ) - 2 * Complex.I)) hr]
    dsimp [G]
    ring
  rw [heq]
  have h := ((((hasDerivAt_id ((r : ℂ) + Complex.I)).sub_const (r : ℂ)).sub_const Complex.I).div_const
    (-(r : ℂ) - 2 * Complex.I)).mul (hG ((r : ℂ) + Complex.I)).hasDerivAt
  convert! h using 1
  simp only [id_eq, add_sub_cancel_left, sub_self, zero_div, zero_mul, add_zero, G,
      integerRowPoleProduct]
  ring

theorem integerLatticeExponential_differentiable (a : ℝ) :
    Differentiable ℂ (integerLatticeExponential a) := by
  unfold integerLatticeExponential
  fun_prop

theorem integerLatticeExponential_eq_zero_iff {a : ℝ} (ha : 0 < a) (z : ℂ) :
    integerLatticeExponential a z = 0 ↔ ∃ k : ℤ, z = (((k : ℝ) / a : ℝ) : ℂ) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integerLatticeExponential, sub_eq_zero, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    push_cast
    have hh : -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) Complex.I_ne_zero) ha'
    apply (mul_left_cancel₀ hh)
    rw [hn]
    field_simp
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    push_cast
    field_simp

theorem integerContourDenominator_differentiable (m : ℕ) (a : ℝ) :
    Differentiable ℂ (integerContourDenominator m a) := by
  exact ((differentiable_id.add_const Complex.I).mul
    (integerRegulator_differentiable m)).mul (integerLatticeExponential_differentiable a)

theorem integerContourDenominator_eq_zero_iff (m : ℕ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    integerContourDenominator m a z = 0 ↔
      z = -Complex.I ∨ z = 2 * Complex.I ∨
      (∃ r ∈ Finset.Icc (-(m : ℤ)) m, z = (r : ℂ) + Complex.I) ∨
      ∃ k : ℤ, z = (((k : ℝ) / a : ℝ) : ℂ) := by
  simp only [integerContourDenominator, mul_eq_zero,
    integerRegulator_eq_zero_iff, integerLatticeExponential_eq_zero_iff ha,
    add_eq_zero_iff_eq_neg, or_assoc]

theorem integerLatticeExponential_ne_zero_of_im_ne_zero {a : ℝ} (ha : 0 < a)
    (z : ℂ) (hz : z.im ≠ 0) : integerLatticeExponential a z ≠ 0 := by
  intro he
  obtain ⟨k, hk⟩ := (integerLatticeExponential_eq_zero_iff ha z).mp he
  apply hz
  rw [hk]
  simp

theorem integerLatticeExponential_at_neg_I (a : ℝ) :
    integerLatticeExponential a (-Complex.I) =
      ((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) := by
  have he : -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (-Complex.I) =
      ((-2 * Real.pi * a : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [integerLatticeExponential, he, ← Complex.ofReal_exp]
  push_cast
  rfl

theorem integerLatticeExponential_at_lattice {a : ℝ} (ha : 0 < a) (k : ℤ) :
    integerLatticeExponential a (((k : ℝ) / a : ℝ) : ℂ) = 0 :=
  (integerLatticeExponential_eq_zero_iff ha _).mpr ⟨k, rfl⟩

theorem integerLatticeExponential_hasDerivAt (a : ℝ) (z : ℂ) :
    HasDerivAt (integerLatticeExponential a)
      (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) *
        (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) z := by
  simpa only [mul_one] using!
    (((hasDerivAt_id z).const_mul (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))).cexp.sub_const 1)

theorem integerContourDenominator_hasDerivAt (m : ℕ) (a : ℝ) (z : ℂ) :
    HasDerivAt (integerContourDenominator m a)
      ((integerRegulator m z + (z + Complex.I) * deriv (integerRegulator m) z) *
        integerLatticeExponential a z +
        (z + Complex.I) * integerRegulator m z *
          (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) *
            (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)))) z := by
  simpa only [one_mul] using!
    (((hasDerivAt_id z).add_const Complex.I).mul
      ((integerRegulator_differentiable m) z).hasDerivAt).mul
      (integerLatticeExponential_hasDerivAt a z)

theorem integerContourDenominator_hasDerivAt_neg_I (m : ℕ) {a : ℝ} (_ha : 0 < a) :
    HasDerivAt (integerContourDenominator m a)
      (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)) (-Complex.I) := by
  simpa only [neg_add_cancel, zero_mul, add_zero, zero_add,
    integerRegulator_at_neg_I, one_mul, integerLatticeExponential_at_neg_I] using!
    integerContourDenominator_hasDerivAt m a (-Complex.I)

theorem integerContourDenominator_hasDerivAt_lattice (m : ℕ) {a : ℝ} (ha : 0 < a) (k : ℤ) :
    let x : ℂ := (((k : ℝ) / a : ℝ) : ℂ)
    HasDerivAt (integerContourDenominator m a)
      ((-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) *
        (x + Complex.I) * integerRegulator m x) x := by
  (try dsimp only)
  have he := integerLatticeExponential_at_lattice ha k
  have hexp := sub_eq_zero.mp he
  have h := integerContourDenominator_hasDerivAt m a (((k : ℝ) / a : ℝ) : ℂ)
  rw [he, mul_zero, zero_add, hexp, one_mul] at h
  convert! h using 1
  ring

theorem integerContourDenominator_hasDerivAt_top (m : ℕ) {a : ℝ} (_ha : 0 < a) :
    HasDerivAt (integerContourDenominator m a)
      (-(integerTopPoleProduct m) * integerLatticeExponential a (2 * Complex.I))
      (2 * Complex.I) := by
  have hp : integerRegulator m (2 * Complex.I) = 0 :=
    (integerRegulator_eq_zero_iff m _).mpr (Or.inl rfl)
  have h := integerContourDenominator_hasDerivAt m a (2 * Complex.I)
  rw [hp, zero_add, mul_zero, zero_mul, add_zero,
    (integerRegulator_hasDerivAt_top m).deriv] at h
  convert! h using 1
  field_simp
  ring

theorem integerContourDenominator_hasDerivAt_row (m : ℕ) {a : ℝ} (_ha : 0 < a) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    HasDerivAt (integerContourDenominator m a)
      (-(integerRowPoleProduct m r) * integerLatticeExponential a ((r : ℂ) + Complex.I))
      ((r : ℂ) + Complex.I) := by
  have hp : integerRegulator m ((r : ℂ) + Complex.I) = 0 :=
    (integerRegulator_eq_zero_iff m _).mpr (Or.inr ⟨r, hr, rfl⟩)
  have h := integerContourDenominator_hasDerivAt m a ((r : ℂ) + Complex.I)
  rw [hp, zero_add, mul_zero, zero_mul, add_zero,
    (integerRegulator_hasDerivAt_row m r hr).deriv] at h
  convert! h using 1
  have hd := row_normalization_ne_zero r
  rw [show (r : ℂ) + Complex.I + Complex.I = -(-(r : ℂ) - 2 * Complex.I) by ring]
  simp only [neg_mul, mul_div_cancel₀ _ hd]

theorem integerContourDenominator_deriv_ne_zero_of_eq_zero (m : ℕ) {a : ℝ} (ha : 0 < a)
    (z : ℂ) (hz : integerContourDenominator m a z = 0) :
    deriv (integerContourDenominator m a) z ≠ 0 := by
  rcases (integerContourDenominator_eq_zero_iff m ha z).mp hz with
    hneg | htop | ⟨r, hr, hrow⟩ | ⟨k, hlat⟩
  · subst z
    rw [(integerContourDenominator_hasDerivAt_neg_I m ha).deriv,
      ← integerLatticeExponential_at_neg_I]
    exact integerLatticeExponential_ne_zero_of_im_ne_zero ha _ (by norm_num)
  · subst z
    rw [(integerContourDenominator_hasDerivAt_top m ha).deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (integerTopPoleProduct_ne_zero m))
      (integerLatticeExponential_ne_zero_of_im_ne_zero ha _ (by norm_num))
  · subst z
    rw [(integerContourDenominator_hasDerivAt_row m ha r hr).deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (integerRowPoleProduct_ne_zero m r hr))
      (integerLatticeExponential_ne_zero_of_im_ne_zero ha _ (by norm_num))
  · subst z
    rw [(integerContourDenominator_hasDerivAt_lattice m ha k).deriv]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) Complex.I_ne_zero) ha'
      · intro h
        have hi := congrArg Complex.im h
        norm_num at hi
    · exact integerRegulator_real_ne_zero m _

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
