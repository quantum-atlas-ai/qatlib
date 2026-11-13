/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelWeights
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Auxiliary residues of the integer kernel

The module defines the lattice factor and the residue coefficients at the auxiliary poles `2i`
and `r + i`. Integer separation products and factorial inequalities give uniform bounds on the
reciprocal pole products.

`integerAuxiliaryCorrection` combines these auxiliary evaluations of `U`. Its norm decays
exponentially in the spacing when the growth rate is compatible with that spacing, controlling
the correction term in [WangEtAl2026].

## Main statements

* `integerPole_separation_product`: evaluates the row separation product using factorials.
* `integerAuxiliary_norm_le`: bounds the auxiliary correction.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

/-- For integers `a ≤ r`, the product of the distances from `r` to integers in `Ico a r` is `(r
- a).toNat.factorial`. -/
private theorem prod_left_distances (a r : ℤ) (har : a ≤ r) :
    (∏ j ∈ Finset.Ico a r, |((r - j : ℤ) : ℝ)|) = ((r - a).toNat.factorial : ℝ) := by
  have hn : ((r - a).toNat : ℤ) = r - a := Int.toNat_of_nonneg (by omega)
  have hfac : (∏ i ∈ Finset.range (r - a).toNat, ((i : ℝ) + 1)) =
      ((r - a).toNat.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial (r - a).toNat
  rw [← hfac]
  symm
  apply Finset.prod_bij (fun (i : ℕ) _ => r - ((i : ℤ) + 1))
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [Finset.mem_Ico]
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨(r - j - 1).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · omega
  · intro i _
    push_cast
    rw [show (r : ℝ) - ((r : ℝ) - ((i : ℝ) + 1)) = (i : ℝ) + 1 by ring]
    rw [abs_of_nonneg (by positivity)]

/-- For integers `r ≤ b`, the product of the distances from `r` to integers in `Ioc r b` is `(b
- r).toNat.factorial`. -/
private theorem prod_right_distances (r b : ℤ) (hrb : r ≤ b) :
    (∏ j ∈ Finset.Ioc r b, |((r - j : ℤ) : ℝ)|) = ((b - r).toNat.factorial : ℝ) := by
  have hn : ((b - r).toNat : ℤ) = b - r := Int.toNat_of_nonneg (by omega)
  have hfac : (∏ i ∈ Finset.range (b - r).toNat, ((i : ℝ) + 1)) =
      ((b - r).toNat.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial (b - r).toNat
  rw [← hfac]
  symm
  apply Finset.prod_bij (fun (i : ℕ) _ => r + ((i : ℤ) + 1))
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [Finset.mem_Ioc]
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    have hj' := Finset.mem_Ioc.mp hj
    refine ⟨(j - r - 1).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · omega
  · intro i _
    push_cast
    rw [show (r : ℝ) - ((r : ℝ) + ((i : ℝ) + 1)) = -((i : ℝ) + 1) by ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]

/-- For `r ∈ [-m, m]`, the product of its distances to the other row indices equals `(r + m)! (m
- r)!`, with integer differences converted to natural numbers. -/
theorem integerPole_separation_product (m : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    (∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, |((r - j : ℤ) : ℝ)|) =
      (((r + m).toNat.factorial : ℝ) * ((m - r).toNat.factorial : ℝ)) := by
  have hr' := Finset.mem_Icc.mp hr
  have hs : (Finset.Icc (-(m : ℤ)) m).erase r =
      Finset.Ico (-(m : ℤ)) r ∪ Finset.Ioc r m := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
      Finset.mem_Ioc]
    omega
  rw [hs, Finset.prod_union (by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_Ioc] at hk
    omega), prod_left_distances _ _ hr'.1, prod_right_distances _ _ hr'.2]
  simp only [sub_neg_eq_add]

/-- For `n ≤ 2 * m`, the product `n! (2m - n)!` is at least `(m!)²`. -/
theorem factorial_pair_middle_le (m n : ℕ) (hn : n ≤ 2 * m) :
    m.factorial ^ 2 ≤ n.factorial * (2 * m - n).factorial := by
  have hc := Nat.choose_le_middle n (2 * m)
  rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)] at hc
  have hm : m ≤ 2 * m := by omega
  have hmid := Nat.choose_mul_factorial_mul_factorial hm
  have hend := Nat.choose_mul_factorial_mul_factorial hn
  have hpos := Nat.choose_pos hn
  have hsub : 2 * m - m = m := by omega
  rw [hsub] at hmid
  nlinarith

/-- For a row index in `[-m, m]`, the product of distances to all other row indices is at least
`(m!)²`. -/
theorem integerPole_separation_lower (m : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    (m.factorial : ℝ) ^ 2 ≤
      ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, |((r - j : ℤ) : ℝ)| := by
  rw [integerPole_separation_product m r hr]
  have hr' := Finset.mem_Icc.mp hr
  have hn : (r + m).toNat ≤ 2 * m := by omega
  have he : (m - r).toNat = 2 * m - (r + m).toNat := by omega
  rw [he]
  exact_mod_cast factorial_pair_middle_le m (r + m).toNat hn

/-- The normalized exponential lattice factor `-(exp (-2πa) - 1) / (exp (-2πiaz) - 1)` evaluated
at `p`. -/
noncomputable def latticePoleFactor (a : ℝ) (p : ℂ) : ℂ :=
  -(Real.exp (-2 * Real.pi * a) - 1 : ℝ) /
    (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p) - 1)

/-- For positive spacing and `p.im ≥ 1`, the lattice factor norm is at most `exp (-2πa * p.im)`. -/
theorem latticePoleFactor_norm_le {a : ℝ} (ha : 0 < a) (p : ℂ) (hp : 1 ≤ p.im) :
    ‖latticePoleFactor a p‖ ≤ Real.exp (-2 * Real.pi * a * p.im) := by
  let t : ℝ := 2 * Real.pi * a
  have ht : 0 < t := by dsimp [t]; positivity
  have hty : t ≤ t * p.im := by nlinarith
  have hty0 : 0 < t * p.im := ht.trans_le hty
  have hnorm : ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p)‖ =
      Real.exp (t * p.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    dsimp [t]
    ring
  have hden := norm_sub_norm_le
    (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p)) 1
  rw [hnorm, norm_one] at hden
  have hE : 1 < Real.exp (t * p.im) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hty0
  have hdenpos := (sub_pos.mpr hE).trans_le hden
  have hnum : ‖(-(Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)‖ =
      1 - Real.exp (-t) := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have he : Real.exp (-t) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr ht.le)
    have ht' : -2 * Real.pi * a = -t := by dsimp [t]; ring
    rw [ht', abs_of_nonpos (by linarith)]
    ring
  rw [latticePoleFactor, norm_div, hnum]
  have heq : -2 * Real.pi * a * p.im = -(t * p.im) := by dsimp [t]; ring
  rw [heq]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    1 - Real.exp (-t) ≤ 1 - Real.exp (-(t * p.im)) :=
      sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
    _ = Real.exp (-(t * p.im)) * (Real.exp (t * p.im) - 1) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

/-- The product of normalized row factors evaluated at the top pole `2i`. -/
noncomputable def integerTopPoleProduct (m : ℕ) : ℂ :=
  ∏ r ∈ Finset.Icc (-(m : ℤ)) m,
    (2 * Complex.I - (r : ℂ) - Complex.I) / (-(r : ℂ) - 2 * Complex.I)

/-- The product of the normalized top factor and all other normalized row factors evaluated at
the row pole `r + i`. -/
noncomputable def integerRowPoleProduct (m : ℕ) (r : ℤ) : ℂ :=
  (((r : ℂ) + Complex.I - 2 * Complex.I) / (-3 * Complex.I)) *
    ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r,
      (((r : ℂ) + Complex.I - (j : ℂ) - Complex.I) / (-(j : ℂ) - 2 * Complex.I))

/-- The lattice factor at `2i` divided by the top pole product. -/
noncomputable def integerTopResidueCoefficient (m : ℕ) (a : ℝ) : ℂ :=
  latticePoleFactor a (2 * Complex.I) / integerTopPoleProduct m

/-- The lattice factor at `r + i` divided by the row pole product. -/
noncomputable def integerRowResidueCoefficient (m : ℕ) (a : ℝ) (r : ℤ) : ℂ :=
  latticePoleFactor a ((r : ℂ) + Complex.I) / integerRowPoleProduct m r

/-- The reciprocal norm of the top pole product equals twice the normalization product divided
by the row-distance product at zero. -/
theorem integerTopPoleProduct_inv_norm (m : ℕ) :
    ‖integerTopPoleProduct m‖⁻¹ =
      2 * ((∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
        (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(0 : ℂ) - (r : ℂ) - Complex.I‖)) := by
  unfold integerTopPoleProduct
  rw [norm_prod]
  simp only [norm_div, Finset.prod_div_distrib, integerRegulator_normalization_norm]
  have he (r : ℤ) : ‖2 * Complex.I - (r : ℂ) - Complex.I‖ =
      ‖(0 : ℂ) - (r : ℂ) - Complex.I‖ := by
    have hc : 2 * Complex.I - (r : ℂ) - Complex.I =
        star ((0 : ℂ) - (r : ℂ) - Complex.I) := by
      simp only [star_sub, star_zero, map_intCast, Complex.star_def, Complex.conj_I]
      ring
    rw [hc, norm_star]
  simp_rw [he]
  simp only [inv_div]
  ring

/-- The reciprocal norm of the top pole product is bounded by `2 * sinh (2π) / (2π)`, uniformly
in `m`. -/
theorem integerTopPoleProduct_inv_norm_le (m : ℕ) :
    ‖integerTopPoleProduct m‖⁻¹ ≤ 2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) := by
  rw [integerTopPoleProduct_inv_norm]
  exact mul_le_mul_of_nonneg_left (regulator_numerator_ratio_upper m 0) (by norm_num)

/-- The reciprocal norm of a row pole product equals the explicit ratio of normalization
distances to the top distance and row separation product. -/
theorem integerRowPoleProduct_inv_norm (m : ℕ) (r : ℤ) :
    ‖integerRowPoleProduct m r‖⁻¹ =
      (3 * ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, ‖-(j : ℂ) - 2 * Complex.I‖) /
        (‖(r : ℂ) - Complex.I‖ *
          ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, |((r - j : ℤ) : ℝ)|) := by
  unfold integerRowPoleProduct
  have hn (j : ℤ) : ‖(r : ℂ) + Complex.I - (j : ℂ) - Complex.I‖ =
      |((r - j : ℤ) : ℝ)| := by
    rw [show (r : ℂ) + Complex.I - (j : ℂ) - Complex.I = ((r - j : ℤ) : ℂ) by
      push_cast; ring]
    simp only [Complex.norm_intCast]
  have he : (r : ℂ) + Complex.I - 2 * Complex.I = (r : ℂ) - Complex.I := by ring
  simp only [norm_mul, norm_div, norm_prod, hn, he, norm_neg, Complex.norm_I,
    mul_one, Finset.prod_div_distrib]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For a row index in `[-m, m]`, the reciprocal norm of its pole product is at most `6 * sinh
(2π) / (2π)`. -/
theorem integerRowPoleProduct_inv_norm_le (m : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    ‖integerRowPoleProduct m r‖⁻¹ ≤ 6 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) := by
  have hN₀ : 0 ≤ ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r,
      ‖-(j : ℂ) - 2 * Complex.I‖ := by positivity
  have hnr : 1 ≤ ‖-(r : ℂ) - 2 * Complex.I‖ := by
    have h := Complex.abs_im_le_norm (-(r : ℂ) - 2 * Complex.I)
    norm_num at h
    linarith
  have hN : (∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, ‖-(j : ℂ) - 2 * Complex.I‖) ≤
      2 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4) := by
    rw [← integerRegulator_normalization_norm]
    calc
      _ ≤ ‖-(r : ℂ) - 2 * Complex.I‖ *
          ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, ‖-(j : ℂ) - 2 * Complex.I‖ := by
        nlinarith
      _ = _ := Finset.mul_prod_erase _ (fun j : ℤ => ‖-(j : ℂ) - 2 * Complex.I‖) hr
  have hO : 1 ≤ ‖(r : ℂ) - Complex.I‖ := by
    have h := Complex.abs_im_le_norm ((r : ℂ) - Complex.I)
    norm_num at h
    exact h
  have hS := integerPole_separation_lower m r hr
  have hf : 0 < (m.factorial : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) 2
  have hD : (m.factorial : ℝ) ^ 2 ≤ ‖(r : ℂ) - Complex.I‖ *
      ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, |((r - j : ℤ) : ℝ)| := by
    nlinarith
  have hA := finite_euler_product_upper m (c := 2) (by norm_num)
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hA
  rw [integerRowPoleProduct_inv_norm]
  calc
    _ ≤ (3 * ∏ j ∈ (Finset.Icc (-(m : ℤ)) m).erase r, ‖-(j : ℂ) - 2 * Complex.I‖) /
        (m.factorial : ℝ) ^ 2 := div_le_div_of_nonneg_left (by positivity) hf hD
    _ ≤ (6 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
        (m.factorial : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hf.le
      nlinarith
    _ ≤ _ := by
      apply (div_le_iff₀ hf).mpr
      nlinarith

/-- For positive spacing, the top residue coefficient norm is at most `2 * sinh (2π) / (2π) *
exp (-4πa)`. -/
theorem integerTopResidueCoefficient_norm_le (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖integerTopResidueCoefficient m a‖ ≤
      2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * Real.exp (-4 * Real.pi * a) := by
  have hl := latticePoleFactor_norm_le ha (2 * Complex.I) (by norm_num)
  norm_num at hl
  rw [show -(2 * Real.pi * a * 2) = -2 * Real.pi * a * 2 by ring] at hl
  rw [integerTopResidueCoefficient, norm_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-2 * Real.pi * a * 2) *
        (2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2))) :=
      mul_le_mul hl (integerTopPoleProduct_inv_norm_le m) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [show -2 * Real.pi * a * 2 = -4 * Real.pi * a by ring]; ring

/-- For positive spacing and a row index in `[-m, m]`, the residue coefficient norm is at most
`6 * sinh (2π) / (2π) * exp (-2πa)`. -/
theorem integerRowResidueCoefficient_norm_le (m : ℕ) {a : ℝ} (ha : 0 < a) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
    ‖integerRowResidueCoefficient m a r‖ ≤
      6 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * Real.exp (-2 * Real.pi * a) := by
  have hl := latticePoleFactor_norm_le ha ((r : ℂ) + Complex.I) (by norm_num)
  simp only [Complex.add_im, Complex.intCast_im, Complex.I_im, zero_add, mul_one] at hl
  rw [integerRowResidueCoefficient, norm_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-2 * Real.pi * a) *
        (6 * (Real.sinh (Real.pi * 2) / (Real.pi * 2))) :=
      mul_le_mul hl (integerRowPoleProduct_inv_norm_le m r hr) (by positivity) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- The constant `12 * sinh (2π) / (2π)` used to bound the auxiliary residue correction. -/
noncomputable def kernelAuxiliaryConstant : ℝ :=
  12 * (Real.sinh (Real.pi * 2) / (Real.pi * 2))

/-- The auxiliary correction constant is at least twelve. -/
theorem kernelAuxiliaryConstant_ge_twelve : 12 ≤ kernelAuxiliaryConstant := by
  have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
  simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
  unfold kernelAuxiliaryConstant
  linarith

section Propagator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The top residue contribution at `2i` plus the sum of the row residue contributions at `r +
i` for `-m ≤ r ≤ m`. -/
noncomputable def integerAuxiliaryCorrection (m : ℕ) (a : ℝ) (U : ℂ → E) : E :=
  integerTopResidueCoefficient m a • U (2 * Complex.I) +
    ∑ r ∈ Finset.Icc (-(m : ℤ)) m,
      integerRowResidueCoefficient m a r • U ((r : ℂ) + Complex.I)

/-- Under the stated bounds on `U` at the auxiliary poles, the sum of the contribution norms is
bounded by the explicit top term proportional to `exp (2ρ - 4πa)` and row term proportional
to `(2m + 1) exp (ρ - 2πa)`. -/
theorem integerAuxiliary_total_norm_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a) (U : ℂ → E)
    (hUtop : ‖U (2 * Complex.I)‖ ≤ Real.exp (2 * ρ))
    (hUrow : ∀ r ∈ Finset.Icc (-(m : ℤ)) m,
      ‖U ((r : ℂ) + Complex.I)‖ ≤ Real.exp ρ) :
    ‖integerTopResidueCoefficient m a • U (2 * Complex.I)‖ +
      (∑ r ∈ Finset.Icc (-(m : ℤ)) m,
        ‖integerRowResidueCoefficient m a r • U ((r : ℂ) + Complex.I)‖) ≤
      2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * Real.exp (2 * ρ - 4 * Real.pi * a) +
      6 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * (2 * (m : ℝ) + 1) *
        Real.exp (ρ - 2 * Real.pi * a) := by
  have hQ : 0 ≤ Real.sinh (Real.pi * 2) / (Real.pi * 2) := by
    have h := kernelAuxiliaryConstant_ge_twelve
    unfold kernelAuxiliaryConstant at h
    linarith
  have ht : ‖integerTopResidueCoefficient m a • U (2 * Complex.I)‖ ≤
      2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * Real.exp (2 * ρ - 4 * Real.pi * a) := by
    rw [norm_smul]
    have h := mul_le_mul (integerTopResidueCoefficient_norm_le m ha) hUtop
      (norm_nonneg _) (by positivity)
    convert! h using 1
    rw [show -4 * Real.pi * a = -(4 * Real.pi * a) by ring, Real.exp_sub, Real.exp_neg]
    ring
  have hr (r : ℤ) (hr : r ∈ Finset.Icc (-(m : ℤ)) m) :
      ‖integerRowResidueCoefficient m a r • U ((r : ℂ) + Complex.I)‖ ≤
        6 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) * Real.exp (ρ - 2 * Real.pi * a) := by
    rw [norm_smul]
    have h := mul_le_mul (integerRowResidueCoefficient_norm_le m ha r hr) (hUrow r hr)
      (norm_nonneg _) (by positivity)
    convert! h using 1
    rw [show -2 * Real.pi * a = -(2 * Real.pi * a) by ring, Real.exp_sub, Real.exp_neg]
    ring
  have hsum := Finset.sum_le_sum hr
  have hc : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by rw [Int.card_Icc]; omega
  simp only [Finset.sum_const, hc, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] at hsum
  nlinarith

/-- For positive spacing with `ρ ≤ 2πa` and the stated auxiliary growth bounds, the correction
norm is at most `kernelAuxiliaryConstant * (m + 1) * exp (ρ - 2πa)`. -/
theorem integerAuxiliary_norm_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a) (hρa : ρ ≤ 2 * Real.pi * a)
    (U : ℂ → E) (hUtop : ‖U (2 * Complex.I)‖ ≤ Real.exp (2 * ρ))
    (hUrow : ∀ r ∈ Finset.Icc (-(m : ℤ)) m, ‖U ((r : ℂ) + Complex.I)‖ ≤ Real.exp ρ) :
    ‖integerAuxiliaryCorrection m a U‖ ≤
      kernelAuxiliaryConstant * ((m : ℝ) + 1) * Real.exp (ρ - 2 * Real.pi * a) := by
  have hQ : 0 ≤ Real.sinh (Real.pi * 2) / (Real.pi * 2) := by
    have h := kernelAuxiliaryConstant_ge_twelve
    unfold kernelAuxiliaryConstant at h
    linarith
  have he : Real.exp (2 * ρ - 4 * Real.pi * a) ≤ Real.exp (ρ - 2 * Real.pi * a) :=
    Real.exp_le_exp.mpr (by linarith)
  have hepos := (Real.exp_pos (ρ - 2 * Real.pi * a)).le
  calc
    _ ≤ ‖integerTopResidueCoefficient m a • U (2 * Complex.I)‖ +
        (∑ r ∈ Finset.Icc (-(m : ℤ)) m,
          ‖integerRowResidueCoefficient m a r • U ((r : ℂ) + Complex.I)‖) := by
      unfold integerAuxiliaryCorrection
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ _ := (integerAuxiliary_total_norm_le m ha U hUtop hUrow).trans (by
      unfold kernelAuxiliaryConstant
      nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 2 *
        (Real.sinh (Real.pi * 2) / (Real.pi * 2)) by positivity)])
end Propagator

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
