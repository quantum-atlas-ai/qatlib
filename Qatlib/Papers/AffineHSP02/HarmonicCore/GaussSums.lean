/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Roots of unity and Gauss sums

Defines `qroot` and the cyclic exponential sum `subgroupSum`, and evaluates Gauss sums over a
prime field in the four combinations of trivial and nontrivial characters. It also proves the
triangle-inequality bound for subgroup sums and their exact value for a generator of the full
multiplicative group. See [MooreEtAl2002].

## Main statements

* `gauss_norm_sqrt`: a Gauss sum with both characters nontrivial has norm `sqrt(p)`.
* `subgroupSum_generator_eq_neg_one`: the full multiplicative-group sum is −1 at nonzero
  frequency.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false

open AddChar MulChar BigOperators

namespace Qatlib.Papers.AffineHSP02.HarmonicCore

noncomputable section

/-- The complex exponential `exp(2πi / p)`. -/
def qroot (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

/-- For nonzero `p`, the `t`th power of `qroot p` is `exp(2πi * t / p)`. -/
theorem qroot_pow_eq' (p t : ℕ) (hp : p ≠ 0) :
    qroot p ^ t = Complex.exp (2 * Real.pi * Complex.I * t / p) := by
  unfold qroot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The definition of `qroot` at zero gives one. -/
theorem qroot_zero : qroot 0 = 1 := by simp [qroot]

/-- For `p ≥ 2`, `qroot p` is different from one. -/
theorem qroot_ne_one (p : ℕ) (hp : 2 ≤ p) : qroot p ≠ 1 := by
  have hp0 : p ≠ 0 := by omega
  have h : qroot p = Complex.exp (2 * Real.pi * Complex.I * 1 / p) := by
    simpa using qroot_pow_eq' p 1 hp0
  rw [h]
  intro he
  have he' : Complex.exp (2 * Real.pi * Complex.I * ↑(1 : ℕ) / ↑p) = 1 := by
    simpa using he
  have hdvd : p ∣ 1 :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) (N := p) hp0).mp he'
  have hp1 : p = 1 := Nat.dvd_one.mp hdvd
  omega

/-- The standard additive character of `ZMod p` at `j` is `qroot p` raised to `j.val`. -/
theorem stdAddChar_eq_qroot_pow (p : ℕ) [NeZero p] (j : ZMod p) :
    ZMod.stdAddChar j = qroot p ^ j.val := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [qroot_pow_eq' p j.val (NeZero.ne p)]

/-- For `p ≥ 2`, the standard additive character of `ZMod p` is nontrivial. -/
theorem stdAddChar_ne_one (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (ZMod.stdAddChar (N := p)) ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff]
  rw [stdAddChar_eq_qroot_pow]
  haveI : Fact (1 < p) := ⟨by omega⟩
  rw [ZMod.val_one, pow_one]
  exact qroot_ne_one p hp

/-- Every natural power of `qroot p` has complex norm one. -/
theorem norm_qroot_pow (p t : ℕ) : ‖qroot p ^ t‖ = 1 := by
  by_cases hp : p = 0
  · subst hp
    rw [qroot_zero, one_pow, norm_one]
  · rw [qroot_pow_eq' p t hp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * t / p) =
        ((2 * Real.pi * t / p : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]

variable {p : ℕ} [Fact p.Prime]

/-- Over a prime field, a Gauss sum with nontrivial multiplicative and additive characters has
norm equal to the square root of the field cardinality [Moore et al., Theorem
6][MooreEtAl2002]. -/
theorem gauss_norm_sqrt (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card (ZMod p)) := by
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hprod : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψp
  have hstar : star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := star_gaussSum_eq χ ψ
  have hmul : gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ) = (Fintype.card (ZMod p) : ℂ) := by
    change gaussSum χ ψ * star (gaussSum χ ψ) = _
    rw [hstar]; exact hprod
  have hmulc := Complex.mul_conj (gaussSum χ ψ)
  rw [hmul] at hmulc
  have hnsq : Complex.normSq (gaussSum χ ψ) = (Fintype.card (ZMod p) : ℝ) := by
    have h3 : ((Complex.normSq (gaussSum χ ψ) : ℝ) : ℂ) =
        ((Fintype.card (ZMod p) : ℝ) : ℂ) := by
      push_cast
      exact hmulc.symm
    exact Complex.ofReal_inj.mp h3
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card (ZMod p) : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, hnsq]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- The Gauss sum with both characters trivial is `p - 1` [Moore et al., Theorem
6][MooreEtAl2002]. -/
theorem gauss_one_one :
    gaussSum (1 : MulChar (ZMod p) ℂ) (1 : AddChar (ZMod p) ℂ) = (p : ℂ) - 1 := by
  rw [gaussSum]
  have hcongr : ∑ a : ZMod p, (1 : MulChar (ZMod p) ℂ) a * (1 : AddChar (ZMod p) ℂ) a
      = ∑ a : ZMod p, (if a = 0 then (0 : ℂ) else 1) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
      simp [ha, MulChar.one_apply hu]
  rw [hcongr]
  have hpt : ∀ a : ZMod p, (if a = 0 then (0 : ℂ) else 1) =
      1 - (if a = 0 then (1 : ℂ) else 0) := by
    intro a; by_cases h : a = 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun _ => (1 : ℂ))]
  simp [ZMod.card]

/-- The Gauss sum with trivial multiplicative character and nontrivial additive character is −1
[Moore et al., Theorem 6][MooreEtAl2002]. -/
theorem gauss_one_add (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    gaussSum (1 : MulChar (ZMod p) ℂ) ψ = -1 := by
  rw [gaussSum]
  have hcongr : ∑ a : ZMod p, (1 : MulChar (ZMod p) ℂ) a * ψ a
      = ∑ a : ZMod p, (if a = 0 then (0 : ℂ) else ψ a) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
      simp [ha, MulChar.one_apply hu]
  rw [hcongr]
  have hpt : ∀ a : ZMod p, (if a = 0 then (0 : ℂ) else ψ a) =
      ψ a - (if a = 0 then ψ 0 else 0) := by
    intro a; by_cases h : a = 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun _ => ψ 0),
    AddChar.sum_eq_zero_of_ne_one hψ]
  simp

/-- The Gauss sum with nontrivial multiplicative character and trivial additive character is
zero [Moore et al., Theorem 6][MooreEtAl2002]. -/
theorem gauss_mul_one (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    gaussSum χ (1 : AddChar (ZMod p) ℂ) = 0 := by
  rw [gaussSum]
  simp only [AddChar.one_apply, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- The sum of the standard additive character at `a^t * k` for `0 ≤ t < q`. -/
def subgroupSum (p : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) (q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range q, qroot p ^ (((a : ZMod p) ^ t * k).val)

/-- The norm of `subgroupSum p a k q` is at most the number `q` of its summands. -/
theorem subgroupSum_norm_le (p q : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) :
    ‖subgroupSum p a k q‖ ≤ (q : ℝ) := by
  unfold subgroupSum
  have h1 : ‖∑ t ∈ Finset.range q, qroot p ^ (((a : ZMod p) ^ t * k).val)‖
      ≤ ∑ t ∈ Finset.range q, ‖qroot p ^ (((a : ZMod p) ^ t * k).val)‖ :=
    norm_sum_le _ _
  have h2 : ∀ t ∈ Finset.range q, ‖qroot p ^ (((a : ZMod p) ^ t * k).val)‖ = 1 := by
    intro t _; rw [norm_qroot_pow]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at h1
  exact h1

/-- For prime `p`, a generator `a` of the multiplicative group and nonzero frequency `k` give
`subgroupSum p a k (p - 1) = -1`. -/
theorem subgroupSum_generator_eq_neg_one (p : ℕ) [Fact p.Prime] (hp : 2 ≤ p)
    (a : (ZMod p)ˣ) (ha : orderOf a = p - 1) (k : ZMod p) (hk : k ≠ 0) :
    subgroupSum p a k (p - 1) = -1 := by
  haveI : NeZero p := ⟨by omega⟩
  have hak : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero

  have hinj : ∀ t ∈ Finset.range (p - 1), ∀ s ∈ Finset.range (p - 1),
      (a : ZMod p) ^ t * k = (a : ZMod p) ^ s * k → t = s := by
    intro t ht s hs h
    have h' : (a : ZMod p) ^ t = (a : ZMod p) ^ s := by
      exact mul_right_cancel₀ hk h
    have hpow : a ^ t = a ^ s := Units.val_injective h'
    have ht' : t < orderOf a := by rw [ha]; exact Finset.mem_range.mp ht
    have hs' : s < orderOf a := by rw [ha]; exact Finset.mem_range.mp hs
    exact pow_injOn_Iio_orderOf ht' hs' hpow
  have hcard_filter : ((Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0)).card = p - 1 := by
    have hfilter : (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0) =
        (Finset.univ : Finset (ZMod p)).erase 0 := by
      ext x; simp [Finset.mem_erase]
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
  have hsum : subgroupSum p a k (p - 1) =
      ∑ x ∈ (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0),
        qroot p ^ x.val := by
    unfold subgroupSum
    refine Finset.sum_bij (fun t _ => (a : ZMod p) ^ t * k) ?_ ?_ ?_ ?_
    · intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero (pow_ne_zero t hak) hk⟩
    · intro t ht s hs h; exact hinj t ht s hs h
    · intro x hx
      have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2
      have himgcard : ((Finset.range (p - 1)).image (fun t => (a : ZMod p) ^ t * k)).card
          = (Finset.range (p - 1)).card := by
        rw [Finset.card_image_of_injOn]
        intro t ht s hs h
        exact hinj t (Finset.mem_coe.mp ht) s (Finset.mem_coe.mp hs) h
      have hsubset : (Finset.range (p - 1)).image (fun t => (a : ZMod p) ^ t * k) ⊆
          (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0) := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero (pow_ne_zero t hak) hk⟩
      have himg : (Finset.range (p - 1)).image (fun t => (a : ZMod p) ^ t * k) =
          (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0) := by
        refine Finset.eq_of_subset_of_card_le hsubset ?_
        rw [himgcard, Finset.card_range, hcard_filter]
      have hx' : x ∈ (Finset.range (p - 1)).image (fun t => (a : ZMod p) ^ t * k) := by
        rw [himg]; exact hx
      obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hx'
      exact ⟨t, ht, htx⟩
    · intro t ht; rfl
  rw [hsum]

  have hfull : (∑ x : ZMod p, qroot p ^ x.val) = 0 := by
    rw [Finset.sum_congr rfl (fun x _ => (stdAddChar_eq_qroot_pow p x).symm)]
    exact AddChar.sum_eq_zero_of_ne_one (stdAddChar_ne_one p hp)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (ZMod p))) (f := fun x => qroot p ^ x.val)
    (p := fun x => x = 0)
  have hzero : (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter (fun x => x = 0),
      qroot p ^ x.val) = 1 := by
    rw [Finset.sum_filter,
      Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun x => qroot p ^ x.val)]
    simp [ZMod.val_zero]
  rw [hzero, hfull] at hsplit
  have hnot : (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter (fun x => ¬ x = 0),
      qroot p ^ x.val) = -1 := by
    linear_combination hsplit
  have hpred : ((Finset.univ : Finset (ZMod p)).filter (fun x => ¬ x = 0)) =
      ((Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0)) := rfl
  rw [hpred] at hnot
  exact hnot

end

end Qatlib.Papers.AffineHSP02.HarmonicCore
