/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.DiscreteMixing
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Fourier bounds relative to a parity class

This module relates the true-coordinate parity character `wchar` to the full-subset character
`chi` and proves normalization and Fourier identities for parity mass functions. These
identities yield the parity version of the Fourier total variation bound used in
[MooreRussell2001], followed by a conditional discrete mixing theorem.

## Main statements

* `tvDistParity_sq_le`: bounds squared distance from the appropriate parity mass using only
  proper nonempty subsets.
* `discDist_tvDistParity_sq_le`: groups the discrete-walk bound by subset cardinality.
* `discreteWalk_mixing_of_parity_structure`: deduces mixing from supplied normalization, parity
  support, and coefficient bounds.

## References

* [Moore and Russell, 2001][MooreRussell2001]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

/-- The number of true coordinates of a cube vertex. -/
def trueWeight {n : ℕ} (x : Cube n) : ℕ := ∑ i, if x i then (1 : ℕ) else 0

/-- The product of coordinate signs, with true contributing `-1` and false contributing `1`. -/
def wchar {n : ℕ} (x : Cube n) : ℝ := ∏ i, if x i then (-1 : ℝ) else 1

/-- The true-coordinate weight equals the cardinality of the set of coordinates at which `x` is
true. -/
theorem trueWeight_eq_card {n : ℕ} (x : Cube n) :
    trueWeight x = (Finset.univ.filter (fun i => x i)).card := by
  rw [trueWeight, Finset.sum_boole]
  simp

/-- The power `(-1) ^ m` is one for even `m` and negative one for odd `m`. -/
theorem negOne_pow_eq {m : ℕ} : (-1 : ℝ) ^ m = if m % 2 = 0 then 1 else -1 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos h]; exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · rw [if_neg (by omega)]; exact Odd.neg_one_pow (Nat.odd_iff.mpr h)

/-- Every even natural power of negative one is one. -/
theorem negOne_pow_two_mul {k : ℕ} : (-1 : ℝ) ^ (2 * k) = 1 := by
  rw [pow_mul]; norm_num

/-- The parity character `wchar x` equals `(-1) ^ trueWeight x`. -/
theorem wchar_eq_pow {n : ℕ} (x : Cube n) : wchar x = (-1 : ℝ) ^ trueWeight x := by
  have hpt : ∀ i : Fin n, (if x i then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (if x i then (1 : ℕ) else 0) := by
    intro i; cases x i <;> simp
  rw [wchar, trueWeight, Finset.prod_congr rfl (fun i _ => hpt i)]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- The parity character is one on vertices of even true weight and negative one on vertices of
odd true weight. -/
theorem wchar_eq_pm {n : ℕ} (x : Cube n) :
    wchar x = if trueWeight x % 2 = 0 then (1 : ℝ) else -1 := by
  rw [wchar_eq_pow]
  exact negOne_pow_eq

/-- If the true weight of `x` has the same parity as `t`, then `wchar x = (-1) ^ t`. -/
theorem wchar_eq_negOne_pow {n : ℕ} {t : ℕ} {x : Cube n}
    (hx : trueWeight x % 2 = t % 2) : wchar x = (-1 : ℝ) ^ t := by
  rw [wchar_eq_pow, negOne_pow_eq (m := trueWeight x), negOne_pow_eq (m := t)]
  by_cases ht : t % 2 = 0
  · rw [if_pos ht, if_pos (by omega : trueWeight x % 2 = 0)]
  · rw [if_neg ht, if_neg (by omega : ¬ trueWeight x % 2 = 0)]

/-- The parity character equals `(-1) ^ n` times the full-subset character. -/
theorem wchar_eq_univ_chi {n : ℕ} (x : Cube n) :
    wchar x = (-1 : ℝ) ^ n * chi (Finset.univ) x := by
  have hpt : ∀ i : Fin n, (if x i then (-1 : ℝ) else 1) = (-1 : ℝ) * (if x i then (1 : ℝ) else -1) := by
    intro i; cases x i <;> norm_num
  have hchi : chi (Finset.univ : Finset (Fin n)) x = ∏ i : Fin n, (if x i then (1 : ℝ) else -1) := by
    simp [chi, cubeChar]
  rw [hchi, wchar, Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib,
    Finset.prod_const]
  simp [Finset.card_univ]

/-- The full-subset character equals `(-1) ^ n` times the parity character. -/
theorem chi_univ_eq_negOne_mul_wchar {n : ℕ} (x : Cube n) :
    chi (Finset.univ) x = (-1 : ℝ) ^ n * wchar x := by
  have hnn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n by ring, negOne_pow_two_mul]
  calc chi (Finset.univ) x = 1 * chi (Finset.univ) x := (one_mul _).symm
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * chi (Finset.univ) x := by rw [hnn]
    _ = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * chi (Finset.univ) x) := by ring
    _ = (-1 : ℝ) ^ n * wchar x := by rw [← wchar_eq_univ_chi]

/-- On the parity class corresponding to `t`, the full-subset character is the constant `(-1) ^
(n + t)`. -/
theorem chi_univ_eq_on_parityClass {n t : ℕ} {x : Cube n}
    (hx : trueWeight x % 2 = t % 2) : chi (Finset.univ) x = (-1 : ℝ) ^ (n + t) := by
  rw [chi_univ_eq_negOne_mul_wchar, wchar_eq_negOne_pow hx, ← pow_add]

/-- Multiplying `chi S` by the parity character gives `(-1) ^ n` times the character indexed by
the symmetric difference of `S` and the full coordinate set. -/
theorem wchar_mul_chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    wchar x * chi S x = (-1 : ℝ) ^ n * chi (S ∆ Finset.univ) x := by
  rw [wchar_eq_univ_chi, mul_assoc, chi_mul, symmDiff_comm]

/-- The finite set of cube vertices whose true weight has the same parity as `b`. -/
def parityClass (n b : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => trueWeight x % 2 = b % 2)

/-- Membership in `parityClass n b` is equivalent to equality of true-weight parity with `b`
modulo two. -/
theorem mem_parityClass {n b : ℕ} {x : Cube n} :
    x ∈ parityClass n b ↔ trueWeight x % 2 = b % 2 := by
  simp [parityClass]

/-- The indicator of the parity class of `b` equals `(1 + (-1) ^ b * wchar x) / 2`. -/
theorem indicator_parityClass {n b : ℕ} (x : Cube n) :
    (if trueWeight x % 2 = b % 2 then (1 : ℝ) else 0) = (1 + (-1 : ℝ) ^ b * wchar x) / 2 := by
  rw [negOne_pow_eq (m := b), wchar_eq_pm]
  by_cases hb : b % 2 = 0 <;> by_cases hx : trueWeight x % 2 = 0
  · rw [if_pos hb, if_pos hx, if_pos (by omega)]; norm_num
  · rw [if_pos hb, if_neg hx, if_neg (by omega)]; norm_num
  · rw [if_neg hb, if_pos hx, if_neg (by omega)]; norm_num
  · rw [if_neg hb, if_neg hx, if_pos (by omega)]; norm_num

/-- A sum restricted to a parity class equals the unrestricted sum weighted by its character
indicator. -/
theorem sum_parityClass_eq {n b : ℕ} (f : Cube n → ℝ) :
    (∑ x ∈ parityClass n b, f x) = ∑ x : Cube n, (1 + (-1 : ℝ) ^ b * wchar x) / 2 * f x := by
  rw [parityClass, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← indicator_parityClass (b := b) x]
  by_cases h : trueWeight x % 2 = b % 2 <;> simp [h]

/-- For positive dimension and a proper nonempty subset `S`, the sum of `chi S` over either
parity class is zero. -/
theorem sum_parityClass_chi_zero {n b : ℕ} (_hn : 1 ≤ n) {S : Finset (Fin n)}
    (hS : S ≠ ∅) (hSu : S ≠ Finset.univ) :
    (∑ x ∈ parityClass n b, chi S x) = 0 := by
  rw [sum_parityClass_eq]
  have h1 : (∑ x : Cube n, chi S x) = 0 :=
    sum_chi_eq_zero (Finset.nonempty_iff_ne_empty.mpr hS)
  have hSu' : (S ∆ Finset.univ).Nonempty := Finset.symmDiff_nonempty.mpr hSu
  have h2 : (∑ x : Cube n, chi (S ∆ Finset.univ) x) = 0 := sum_chi_eq_zero hSu'
  have hw : (∑ x : Cube n, wchar x * chi S x) = 0 := by
    have hstep : (∑ x : Cube n, wchar x * chi S x)
        = (-1 : ℝ) ^ n * ∑ x : Cube n, chi (S ∆ Finset.univ) x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => wchar_mul_chi S x
    rw [hstep, h2, mul_zero]
  have hsplit : (∑ x : Cube n, (1 + (-1 : ℝ) ^ b * wchar x) / 2 * chi S x)
      = (1 / 2) * (∑ x : Cube n, chi S x)
        + ((-1 : ℝ) ^ b / 2) * (∑ x : Cube n, wchar x * chi S x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, h1, hw]; ring

/-- In positive dimension, either parity class has `2 ^ (n - 1)` vertices. -/
theorem card_parityClass {n b : ℕ} (hn : 1 ≤ n) : (parityClass n b).card = 2 ^ (n - 1) := by
  have hw : (∑ x : Cube n, wchar x) = 0 := by
    have hstep : (∑ x : Cube n, wchar x)
        = (-1 : ℝ) ^ n * ∑ x : Cube n, chi (Finset.univ) x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => wchar_eq_univ_chi x
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    rw [hstep, sum_chi_eq_zero hne, mul_zero]
  have hsum : (∑ x : Cube n, (1 + (-1 : ℝ) ^ b * wchar x) / 2 * (1 : ℝ))
      = (2 : ℝ) ^ n / 2 := by
    have hsplit : (∑ x : Cube n, (1 + (-1 : ℝ) ^ b * wchar x) / 2 * (1 : ℝ))
        = (1 / 2) * (∑ x : Cube n, (1 : ℝ))
          + ((-1 : ℝ) ^ b / 2) * (∑ x : Cube n, wchar x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hcard : (∑ x : Cube n, (1 : ℝ)) = (2 : ℝ) ^ n := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_cube]
      simp
    rw [hsplit, hw, hcard]; ring
  have hpow : (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ (n - 1) := by
    have h2 : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := pow_sub_one_mul (by omega : n ≠ 0) 2
    linarith
  have hreal : ((parityClass n b).card : ℝ) = ((2 ^ (n - 1) : ℕ) : ℝ) := by
    have h1 : ((parityClass n b).card : ℝ) = ∑ x ∈ parityClass n b, (1 : ℝ) := by simp
    rw [h1, sum_parityClass_eq, hsum, hpow]
    simp
  exact_mod_cast hreal

/-- In positive dimension, the time-dependent parity mass function has total mass one. -/
theorem sum_parityParityMass {n t : ℕ} (hn : 1 ≤ n) :
    (∑ x : Cube n, parityParityMass n t x) = 1 := by
  have hcongr : (∑ x : Cube n, parityParityMass n t x)
      = ∑ x : Cube n, if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [parityParityMass, trueWeight]
  have hstep : (∑ x : Cube n,
        if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0)
      = ((2 : ℝ) ^ (n - 1))⁻¹ * ((parityClass n t).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [show (Finset.univ : Finset (Cube n)).filter (fun x => trueWeight x % 2 = t % 2)
        = parityClass n t from rfl]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcongr, hstep, card_parityClass hn]
  have hcast : (((2 ^ (n - 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (n - 1) := by push_cast; ring
  rw [hcast]
  exact inv_mul_cancel₀ (by positivity)

/-- The time-dependent parity mass vanishes at vertices with parity different from `t`. -/
theorem parityParityMass_eq_zero_of_notMem {n t : ℕ} {x : Cube n}
    (hx : trueWeight x % 2 ≠ t % 2) : parityParityMass n t x = 0 := by
  simp only [parityParityMass]
  rw [if_neg]
  simpa [trueWeight] using hx

/-- In positive dimension, the parity mass function has zero Fourier coefficient at every proper
nonempty subset. -/
theorem fourierCoeff_parityParityMass_zero {n t : ℕ} (hn : 1 ≤ n) {S : Finset (Fin n)}
    (hS : S ≠ ∅) (hSu : S ≠ Finset.univ) :
    fourierCoeff (parityParityMass n t) S = 0 := by
  have hmass_eq : ∀ x : Cube n, parityParityMass n t x
      = (if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0) := by
    intro x; simp [parityParityMass, trueWeight]
  have hcongr : (∑ x : Cube n, parityParityMass n t x * chi S x)
      = ∑ x ∈ (Finset.univ : Finset (Cube n)),
          (if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0) * chi S x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hmass_eq x]
  have hstep : (∑ x ∈ (Finset.univ : Finset (Cube n)),
        (if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0) * chi S x)
      = ((2 : ℝ) ^ (n - 1))⁻¹ * (∑ x ∈ parityClass n t, chi S x) := by
    have h1 : (∑ x ∈ (Finset.univ : Finset (Cube n)),
          (if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0) * chi S x)
        = ∑ x ∈ (Finset.univ : Finset (Cube n)),
            if trueWeight x % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ * chi S x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : trueWeight x % 2 = t % 2 <;> simp [h]
    rw [h1, ← Finset.sum_filter]
    rw [show (Finset.univ : Finset (Cube n)).filter (fun x => trueWeight x % 2 = t % 2)
        = parityClass n t from rfl]
    rw [Finset.mul_sum]
  rw [fourierCoeff, hcongr, hstep, sum_parityClass_chi_zero hn hS hSu, mul_zero]

/-- A real function of total mass one supported on the parity class of `t` has full-subset
Fourier coefficient `(-1) ^ (n + t)`. -/
theorem fourierCoeff_univ_eq_of_paritySupport {n t : ℕ} {P : Cube n → ℝ}
    (hmass : ∑ x, P x = 1)
    (hsupp : ∀ x : Cube n, trueWeight x % 2 ≠ t % 2 → P x = 0) :
    fourierCoeff P (Finset.univ) = (-1 : ℝ) ^ (n + t) := by
  have hcollapseP : (∑ x : Cube n, P x) = ∑ x ∈ parityClass n t, P x := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    exact hsupp x (by
      intro h
      exact hx (mem_parityClass.mpr h))
  have hcollapse : (∑ x : Cube n, P x * chi (Finset.univ) x)
      = ∑ x ∈ parityClass n t, P x * chi (Finset.univ) x := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have hx' : trueWeight x % 2 ≠ t % 2 := by
      intro h; exact hx (mem_parityClass.mpr h)
    rw [hsupp x hx', zero_mul]
  rw [fourierCoeff, hcollapse]
  calc (∑ x ∈ parityClass n t, P x * chi (Finset.univ) x)
      = ∑ x ∈ parityClass n t, P x * (-1 : ℝ) ^ (n + t) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [chi_univ_eq_on_parityClass (mem_parityClass.mp hx)]
    _ = (∑ x ∈ parityClass n t, P x) * (-1 : ℝ) ^ (n + t) := by
        rw [Finset.sum_mul]
    _ = 1 * (-1 : ℝ) ^ (n + t) := by rw [← hcollapseP, hmass]
    _ = (-1 : ℝ) ^ (n + t) := one_mul _

/-- In positive dimension, the full-subset Fourier coefficient of the parity mass function is
`(-1) ^ (n + t)`. -/
theorem fourierCoeff_parityParityMass_univ {n t : ℕ} (hn : 1 ≤ n) :
    fourierCoeff (parityParityMass n t) (Finset.univ) = (-1 : ℝ) ^ (n + t) :=
  fourierCoeff_univ_eq_of_paritySupport (sum_parityParityMass hn)
    (fun _ hx => parityParityMass_eq_zero_of_notMem hx)

/-- For positive dimension and a real function of total mass one supported on the parity class
of `t`, squared distance to the parity mass is at most one quarter of the sum of squared
coefficients over proper nonempty subsets. -/
theorem tvDistParity_sq_le {n t : ℕ} (hn : 1 ≤ n) (P : Cube n → ℝ)
    (hmass : ∑ x, P x = 1)
    (hsupp : ∀ x : Cube n, trueWeight x % 2 ≠ t % 2 → P x = 0) :
    (tvDistParityAt n t P) ^ 2
      ≤ (1 / 4) * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
          (fourierCoeff P S) ^ 2 := by
  classical
  set f : Cube n → ℝ := fun x => P x - parityParityMass n t x with hf
  have hf_supp : ∀ x : Cube n, trueWeight x % 2 ≠ t % 2 → f x = 0 := by
    intro x hx
    rw [hf]
    simp only [hsupp x hx, parityParityMass_eq_zero_of_notMem hx, sub_zero]
  have hfmass : (∑ x : Cube n, f x) = 0 := by
    rw [hf]
    rw [Finset.sum_sub_distrib, hmass, sum_parityParityMass hn, sub_self]

  have hf_empty : fourierCoeff f (∅ : Finset (Fin n)) = 0 := by
    rw [fourierCoeff_empty]; exact hfmass
  have hf_univ : fourierCoeff f (Finset.univ) = 0 := by
    rw [hf, fourierCoeff_sub, fourierCoeff_univ_eq_of_paritySupport hmass hsupp,
      fourierCoeff_parityParityMass_univ hn, sub_self]

  have hf_eq : ∀ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
      fourierCoeff f S = fourierCoeff P S := by
    intro S hS
    have hSu : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
    have hS0 : S ≠ ∅ := (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
    rw [hf, fourierCoeff_sub, fourierCoeff_parityParityMass_zero hn hS0 hSu, sub_zero]

  have hparse := sum_fourierCoeff_sq f
  have hsq : (∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2)
      = ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
          (fourierCoeff P S) ^ 2 := by
    have hout : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
        S ∉ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ →
          (fourierCoeff f S) ^ 2 = 0 := by
      intro S _ hS
      by_cases hS0 : S = ∅
      · subst hS0; rw [hf_empty]; ring
      · have hSu : S = Finset.univ := by
          by_contra hSu
          exact hS (by
            rw [Finset.mem_erase]
            exact ⟨hSu, by rw [Finset.mem_erase]; exact ⟨hS0, Finset.mem_univ _⟩⟩)
        subst hSu; rw [hf_univ]; ring
    have hcollapse : (∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2)
        = ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
            (fourierCoeff f S) ^ 2 :=
      (Finset.sum_subset (Finset.subset_univ _) hout).symm
    rw [hcollapse]
    exact Finset.sum_congr rfl fun S hS => by rw [hf_eq S hS]
  have hfsq : (∑ x : Cube n, (f x) ^ 2)
      = ((2 : ℝ) ^ n)⁻¹
          * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
              (fourierCoeff P S) ^ 2 := by
    rw [hsq] at hparse
    rw [hparse, ← mul_assoc, inv_mul_cancel₀ (by positivity : ((2 : ℝ) ^ n) ≠ 0), one_mul]

  have hcs : (∑ x : Cube n, |f x|) ^ 2
      ≤ (2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cube n)))
      (f := fun x => |f x|)
    have hcard : ((Finset.univ : Finset (Cube n)).card : ℝ) = (2 : ℝ) ^ n := by
      rw [Finset.card_univ, card_cube]; push_cast; ring
    have habs : (∑ x : Cube n, |f x| ^ 2) = ∑ x : Cube n, (f x) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sq_abs]
    calc (∑ x : Cube n, |f x|) ^ 2
        ≤ ((Finset.univ : Finset (Cube n)).card : ℝ) * ∑ x : Cube n, |f x| ^ 2 := h
      _ = (2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2 := by rw [hcard, habs]
  have htv : (tvDistParityAt n t P) ^ 2 = (1 / 4) * (∑ x : Cube n, |f x|) ^ 2 := by
    rw [tvDistParityAt, hf]
    ring
  rw [htv]
  calc (1 / 4) * (∑ x : Cube n, |f x|) ^ 2
      ≤ (1 / 4) * ((2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = (1 / 4) * ((2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹
          * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
              (fourierCoeff P S) ^ 2)) := by rw [hfsq]
    _ = (1 / 4) * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
          (fourierCoeff P S) ^ 2 := by
        have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
        calc (1 / 4) * ((2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹
              * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
                  (fourierCoeff P S) ^ 2))
            = (1 / 4) * (((2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹)
              * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
                  (fourierCoeff P S) ^ 2) := by ring
          _ = (1 / 4) * (1
              * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
                  (fourierCoeff P S) ^ 2) := by rw [mul_inv_cancel₀ h2]
          _ = (1 / 4) * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
                  (fourierCoeff P S) ^ 2 := by ring

/-- For positive dimension, a cardinality-dependent sum over proper nonempty subsets equals the
binomially weighted sum over sizes from one to `n - 1`. -/
theorem sum_by_card_middle {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℝ) :
    (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ, g S.card)
      = ∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ) * g (k + 1) := by
  classical
  have hA := sum_by_card_nonempty (n := n) g
  have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    intro h
    have hc : (Finset.univ : Finset (Fin n)).card = 0 := by rw [h]; simp
    rw [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hmem : (Finset.univ : Finset (Fin n)) ∈ Finset.univ.erase (∅ : Finset (Fin n)) := by
    rw [Finset.mem_erase]
    exact ⟨hne, Finset.mem_univ _⟩
  have hstep := Finset.sum_erase_add (Finset.univ.erase (∅ : Finset (Fin n)))
    (fun S => g S.card) hmem
  simp only [Finset.card_univ, Fintype.card_fin] at hstep
  have hsplit : (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℝ) * g (k + 1))
      = (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ) * g (k + 1)) + g n := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    simp only [show n - 1 + 1 = n by omega, Nat.choose_self, Nat.cast_one, one_mul]
  linarith

/-- For positive dimension, assuming total mass one and support on the time-`t` parity class,
the squared parity distance of `discDist n t` is bounded by one quarter of its interior
binomially weighted squared coefficients. -/
theorem discDist_tvDistParity_sq_le (n t : ℕ) (hn : 1 ≤ n)
    (hmass : ∑ x, discDist n t x = 1)
    (hsupp : ∀ x : Cube n, trueWeight x % 2 ≠ t % 2 → discDist n t x = 0) :
    (tvDistParityAt n t (discDist n t)) ^ 2
      ≤ (1 / 4) * ∑ k ∈ Finset.range (n - 1),
          (Nat.choose n (k + 1) : ℝ) * (discCoeff n t (k + 1)) ^ 2 := by
  calc (tvDistParityAt n t (discDist n t)) ^ 2
      ≤ (1 / 4) * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
            (fourierCoeff (discDist n t) S) ^ 2 :=
        tvDistParity_sq_le hn _ hmass hsupp
    _ = (1 / 4) * ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ,
            (fun k => (discCoeff n t k) ^ 2) S.card := by
        congr 1
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [discDist_fourierCoeff]
    _ = (1 / 4) * ∑ k ∈ Finset.range (n - 1),
            (Nat.choose n (k + 1) : ℝ) * (discCoeff n t (k + 1)) ^ 2 := by
        rw [sum_by_card_middle hn (fun k => (discCoeff n t k) ^ 2)]

/-- Assuming normalization and parity support of `discDist` in positive dimension and the stated
uniform coefficient estimate, its parity distance is at most `C * n ^ (-7 / 6)` at rounded
odd multiples of `π * n / 4` for all sufficiently large `n`. This is the conditional mixing
conclusion associated with [Moore and Russell, Theorem 1][MooreRussell2001]. -/
theorem discreteWalk_mixing_of_parity_structure
    (hpar : ∀ (n t : ℕ), 1 ≤ n →
      ((∑ x, discDist n t x) = 1 ∧
        (∀ x : Cube n, trueWeight x % 2 ≠ t % 2 → discDist n t x = 0)))
    (hB : ∃ K : ℝ, 0 < K ∧ ∀ (n t k : ℕ), 0 < k → k < n →
        (discCoeff n t k)^2 ≤ K * (n:ℝ)^(-(4/3):ℝ) *
          (2 * |Real.cos (2*(t:ℝ)/(n:ℝ))|^(2*k) +
            2 * |Real.cos (2*(t:ℝ)/(n:ℝ))|^n)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ k : ℕ, Odd k →
      IsInstantaneousMixingAt n ⌈(k : ℝ) * (Real.pi / 4) * (n : ℝ)⌉₊
        (C * (n : ℝ) ^ (-(7 / 6) : ℝ))
        (discDist n ⌈(k : ℝ) * (Real.pi / 4) * (n : ℝ)⌉₊) := by
  refine discreteWalk_mixing_of_coeff_estimate ?_ hB
  intro n t hn
  obtain ⟨hmass, hsupp⟩ := hpar n t hn
  exact discDist_tvDistParity_sq_le n t hn hmass hsupp

end Qatlib.Papers.HypercubeWalk01.MainResults
