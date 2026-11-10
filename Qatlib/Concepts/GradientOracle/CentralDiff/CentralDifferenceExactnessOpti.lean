/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceAlgebra

namespace Qatlib.Concepts.GradientOracle.CentralDiff

theorem centralDiffCoeff_neg (m : ℕ) (ℓ : ℤ) :
    centralDiffCoeff m (-ℓ) = -centralDiffCoeff m ℓ := by
  by_cases hℓ : ℓ = 0
  · simp [hℓ, centralDiffCoeff]
  · simp only [centralDiffCoeff, neg_ne_zero.mpr hℓ, hℓ, if_false,
      Int.natAbs_neg, Int.cast_neg]
    ring

theorem centralDiffCoeff_outside (m : ℕ) (ℓ : ℤ) (hℓ : m < ℓ.natAbs) :
    centralDiffCoeff m ℓ = 0 := by
  simp [centralDiffCoeff, Nat.choose_eq_zero_of_lt hℓ]

theorem centralDiffCoeff_even_moment (m k : ℕ) :
    (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      centralDiffCoeff m ℓ * (ℓ : ℝ) ^ (2 * k)) = 0 := by
  classical
  have hs : (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      centralDiffCoeff m ℓ * (ℓ : ℝ) ^ (2 * k)) =
      ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
        centralDiffCoeff m (-ℓ) * ((-ℓ : ℤ) : ℝ) ^ (2 * k) := by
    apply Finset.sum_bij (fun ℓ _ => -ℓ)
    · intro ℓ hℓ
      simp only [Finset.mem_Ico] at hℓ ⊢
      omega
    · intro a _ b _ he
      exact neg_injective he
    · intro ℓ hℓ
      refine ⟨-ℓ, ?_, by simp⟩
      simp only [Finset.mem_Ico] at hℓ ⊢
      omega
    · intro ℓ _
      simp
  have hpow (r : ℝ) : (-r) ^ (2 * k) = r ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    congr 1
    ring
  simp only [centralDiffCoeff_neg, Int.cast_neg, hpow, neg_mul,
    Finset.sum_neg_distrib] at hs
  linarith

theorem centralDifferenceExactness_one (j : ℕ) (hj : j ≤ 2) :
    (∑ ℓ ∈ Finset.Ico (-1 : ℤ) 2, centralDiffCoeff 1 ℓ * (ℓ : ℝ) ^ j) =
      if j = 1 then 1 else 0 := by
  have hs : Finset.Ico (-1 : ℤ) 2 = {-1, 0, 1} := by decide
  interval_cases j <;> norm_num [hs, centralDiffCoeff]

private theorem centralDiff_neg_one_self (n : ℕ) : (-1 : ℝ)^n*(-1 : ℝ)^n=1 := by
  rw [← mul_pow]
  norm_num

theorem centralDiff_positive_weight (m l : ℕ) (hl : 0<l) (hlm : l≤m) :
    centralDiffCoeff m (l : ℤ)*(l : ℝ)=
      (-(-1 : ℝ)^m/(Nat.choose (2*m) m : ℝ))*(-1 : ℝ)^(m+l)*(Nat.choose (2*m) (m+l) : ℝ) := by
  have hlz : (l : ℤ)≠0 := by exact_mod_cast hl.ne'
  have hlr : (l : ℝ)≠0 := by exact_mod_cast hl.ne'
  have hc : centralDiffCoeff m (l : ℤ)*(l : ℝ)=
      (-1 : ℝ)^(l-1)*((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ)) := by
    simp only [centralDiffCoeff,if_neg hlz,Int.natAbs_natCast,Int.cast_natCast]
    field_simp
  rw [hc,centralDiff_choose_ratio m l hlm]
  have hs : (-1 : ℝ)^(l-1)=-(-1 : ℝ)^l := by
    have he : (-1 : ℝ)^l=(-1 : ℝ)^(l-1)*(-1) := by
      rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤l)]
    linarith
  rw [hs,pow_add]
  have hC : (Nat.choose (2*m) m : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos (by omega : m≤2*m)).ne'
  field_simp
  nlinarith [centralDiff_neg_one_self m]

theorem centralDiff_binomial_weight (m r : ℕ) (hr : r≤2*m) :
    centralDiffCoeff m ((r : ℤ)-(m : ℤ))*((r : ℝ)-(m : ℝ))=
      (-(-1 : ℝ)^m/(Nat.choose (2*m) m : ℝ))*(-1 : ℝ)^r*(Nat.choose (2*m) r : ℝ)+
        (if r=m then 1 else 0) := by
  by_cases he : r=m
  · subst r
    simp only [sub_self,centralDiffCoeff,if_true,mul_zero]
    have hC : (Nat.choose (2*m) m : ℝ)≠0 := by
      exact_mod_cast (Nat.choose_pos (by omega : m≤2*m)).ne'
    field_simp
    nlinarith [centralDiff_neg_one_self m]
  · rw [if_neg he,add_zero]
    by_cases hmr : m≤r
    · let l := r-m
      have hl : 0<l := by dsimp [l]; omega
      have hlm : l≤m := by dsimp [l]; omega
      have hrm : m+l=r := by dsimp [l]; omega
      have hz : (r : ℤ)-(m : ℤ)=(l : ℤ) := by dsimp [l]; omega
      have hx : (r : ℝ)-(m : ℝ)=(l : ℝ) := by
        have hcast := congrArg (fun z : ℕ => (z : ℝ)) hrm
        push_cast at hcast
        linarith
      rw [hz,hx,centralDiff_positive_weight m l hl hlm,hrm]
    · let l := m-r
      have hl : 0<l := by dsimp [l]; omega
      have hlm : l≤m := by dsimp [l]; omega
      have hml : m+l=2*m-r := by dsimp [l]; omega
      have hz : (r : ℤ)-(m : ℤ)=-(l : ℤ) := by dsimp [l]; omega
      have hx : (r : ℝ)-(m : ℝ)=-(l : ℝ) := by
        have hi : r+l=m := by dsimp [l]; omega
        have hc := congrArg (fun z : ℕ => (z : ℝ)) hi
        push_cast at hc
        linarith
      rw [hz,hx,centralDiffCoeff_neg,neg_mul_neg,centralDiff_positive_weight m l hl hlm,hml,
        Nat.choose_symm hr]
      have hs := centralDiff_alternating_sign (2*m) r hr
      have hn : (-1 : ℝ)^(2*m)=1 := by rw [pow_mul]; norm_num
      rw [hn,one_mul] at hs
      rw [hs]

theorem centralDiff_sum_reindex (m : ℕ) (F : ℤ → ℝ) :
    (∑ l ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),F l)=
      ∑ r ∈ Finset.range (2*m+1),F ((r : ℤ)-(m : ℤ)) := by
  apply Finset.sum_bij (fun l _ => (l+(m : ℤ)).toNat)
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    apply Finset.mem_range.mpr
    omega
  · intro x hx y hy he
    simp only [Finset.mem_Ico] at hx hy
    omega
  · intro r hr
    refine ⟨(r : ℤ)-(m : ℤ),?_,?_⟩
    · simp only [Finset.mem_Ico]
      have := Finset.mem_range.mp hr
      omega
    · omega
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    congr 1
    omega

theorem centralDifferenceExactness : CentralDifferenceExactness := by
  intro m hm j hj
  by_cases hj0 : j=0
  · subst j
    simpa using centralDiffCoeff_even_moment m 0
  · have hjp : 0<j := by omega
    let p := j-1
    have hpn : p<2*m := by dsimp [p]; omega
    have he (r : ℕ) (hr : r∈Finset.range (2*m+1)) :
        centralDiffCoeff m ((r : ℤ)-(m : ℤ))*(((r : ℤ)-(m : ℤ) : ℤ) : ℝ)^j=
          ((-(-1 : ℝ)^m/(Nat.choose (2*m) m : ℝ))*(-1 : ℝ)^r*(Nat.choose (2*m) r : ℝ)+
            (if r=m then 1 else 0))*((r : ℝ)-(m : ℝ))^p := by
      rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast]
      have hpow : j=p+1 := by dsimp [p]; omega
      rw [hpow,pow_succ]
      rw [mul_assoc, mul_comm (((r : ℝ)-(m : ℝ))^p) ((r : ℝ)-(m : ℝ)),← mul_assoc,
        centralDiff_binomial_weight m r (by have := Finset.mem_range.mp hr; omega)]
      ring
    rw [centralDiff_sum_reindex]
    rw [Finset.sum_congr rfl he]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    have hz := centralDiff_alternating_power_zero (2*m) p hpn (-(m : ℝ))
    have hz' : (∑ r ∈ Finset.range (2*m+1),(-1 : ℝ)^r*((Nat.choose (2*m) r : ℝ)*((r : ℝ)-(m : ℝ))^p))=0 := by
      simpa only [sub_eq_add_neg,add_comm,mul_assoc] using hz
    rw [hz',mul_zero,zero_add]
    simp only [ite_mul,one_mul,zero_mul]
    rw [Finset.sum_ite_eq']
    have hmem : m∈Finset.range (2*m+1) := Finset.mem_range.mpr (by omega)
    rw [if_pos hmem,sub_self]
    by_cases hj1 : j=1
    · subst j; simp [p]
    · have hp : p≠0 := by dsimp [p]; omega
      simp only [zero_pow hp,if_neg hj1]

end Qatlib.Concepts.GradientOracle.CentralDiff
