/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Proposition3Presentation
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Finite power descriptions of cyclic subgroups

The module derives positive periods for normal-form elements of the shift semidirect product and
uses them to enumerate generated cyclic subgroups. `proposition4_cyclic_subgroup` gives two
finite power ranges according to whether `p ^ r` divides the left exponent and the right
exponent is nonzero. See [ChiKimLee2006] for the mathematical setting.

## Main statements

* `zpowers_eq_range_of_pow_eq_one`: enumerates a cyclic subgroup using any positive period.
* `proposition4_cyclic_subgroup`: specializes this enumeration to the two arithmetic branches of
  a normal-form element.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

/-- For prime `p`, `2 * p ^ r` divides `a * (2 * p ^ r / Nat.gcd a (2 * p ^ r))`. -/
lemma dvd_mul_div_gcd (hp : p.Prime) (a : ℕ) :
    2 * p ^ r ∣ a * (2 * p ^ r / Nat.gcd a (2 * p ^ r)) := by
  have hNpos : 0 < 2 * p ^ r := Nat.mul_pos (by norm_num) (pow_pos hp.pos r)
  set g := Nat.gcd a (2 * p ^ r) with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a _
  have hgb : g ∣ 2 * p ^ r := Nat.gcd_dvd_right a _
  obtain ⟨d, hd⟩ := hga
  obtain ⟨c, hc⟩ := hgb
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a hNpos
  have hdiv : 2 * p ^ r / g = c := by
    rw [hc]
    exact Nat.mul_div_right c hgpos
  rw [hdiv, hd, hc]
  exact ⟨d, by ring⟩

/-- For prime `p`, `2 * p ^ r` divides `a * (2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r))`. -/
lemma dvd_mul_div_gcd_mul_p (hp : p.Prime) (a : ℕ) :
    2 * p ^ r ∣ a * (2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)) := by
  have h2p : 2 * p ^ (r + 1) = p * (2 * p ^ r) := by
    rw [pow_succ']; ring
  rw [h2p, Nat.mul_div_assoc p (Nat.gcd_dvd_right a (2 * p ^ r))]
  have h2 := dvd_mul_div_gcd (p := p) (r := r) hp a
  have heq : a * (p * (2 * p ^ r / Nat.gcd a (2 * p ^ r))) =
      p * (a * (2 * p ^ r / Nat.gcd a (2 * p ^ r))) := by ring
  rw [heq]
  exact dvd_mul_of_dvd_right h2 p

/-- The integer `p` divides `2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)`. -/
lemma p_dvd_div_gcd_mul_p (a : ℕ) :
    p ∣ 2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r) := by
  have h2p : 2 * p ^ (r + 1) = p * (2 * p ^ r) := by
    rw [pow_succ']; ring
  rw [h2p, Nat.mul_div_assoc p (Nat.gcd_dvd_right a (2 * p ^ r))]
  exact dvd_mul_right p _

/-- For prime `p` and `r ≥ 1`, if `p ^ r` does not divide `a`, then `p` divides `2 * p ^ r /
Nat.gcd a (2 * p ^ r)`. -/
lemma p_dvd_div_gcd {a : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hpr : ¬ p ^ r ∣ a) :
    p ∣ 2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  have hNpos : 0 < 2 * p ^ r := Nat.mul_pos (by norm_num) (pow_pos hp.pos r)
  set g := Nat.gcd a (2 * p ^ r) with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a _
  have hgb : g ∣ 2 * p ^ r := Nat.gcd_dvd_right a _
  have hgpred : g ∣ 2 * p ^ (r - 1) := by
    by_contra h
    exact hpr (Nat.dvd_trans (dvd_two_pow_pred_of_dvd hp hr hgb h) hga)
  have h2p : 2 * p ^ r = p * (2 * p ^ (r - 1)) := by
    rw [pow_eq_mul_pred (p := p) hr]; ring
  have hdiv : 2 * p ^ r / g = p * (2 * p ^ (r - 1) / g) := by
    rw [h2p, Nat.mul_div_assoc p hgpred]
  rw [hdiv]
  exact dvd_mul_right p _

/-- For prime `p`, the quotient `2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)` is positive. -/
lemma pos_div_gcd_mul_p (hp : p.Prime) (a : ℕ) :
    0 < 2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r) := by
  have hNpos : 0 < 2 * p ^ r := Nat.mul_pos (by norm_num) (pow_pos hp.pos r)
  set g := Nat.gcd a (2 * p ^ r) with hg
  have hgle : g ≤ 2 * p ^ r := Nat.le_of_dvd hNpos (Nat.gcd_dvd_right a _)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a hNpos
  have hcpos : 0 < 2 * p ^ r / g := Nat.div_pos hgle hgpos
  have h2p : 2 * p ^ (r + 1) = p * (2 * p ^ r) := by
    rw [pow_succ']; ring
  have hdiv : 2 * p ^ (r + 1) / g = p * (2 * p ^ r / g) := by
    rw [h2p, Nat.mul_div_assoc p (Nat.gcd_dvd_right a (2 * p ^ r))]
  rw [hdiv]
  exact Nat.mul_pos hp.pos hcpos

/-- For prime `p`, the quotient `2 * p ^ r / Nat.gcd a (2 * p ^ r)` is positive. -/
lemma pos_div_gcd (hp : p.Prime) (a : ℕ) :
    0 < 2 * p ^ r / Nat.gcd a (2 * p ^ r) :=
  Nat.div_pos
    (Nat.le_of_dvd (Nat.mul_pos (by norm_num) (pow_pos hp.pos r))
      (Nat.gcd_dvd_right a _))
    (Nat.gcd_pos_of_pos_right a (Nat.mul_pos (by norm_num) (pow_pos hp.pos r)))

/-- Under the shift-action hypothesis, a mixed element has `N`th power one if `p` divides `b *
N` and `2 * p ^ r` divides `a * N`. -/
lemma pow_genX_mul_genY_eq_one (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) {a b N : ℕ}
    (hy : p ∣ b * N) (hx : 2 * p ^ r ∣ a * N) :
    (genX p r φ ^ a * genY p r φ ^ b) ^ N = 1 := by
  rw [pow_genX_mul_genY hp hr φ hφ a b N]
  have hY : genY p r φ ^ (b * N) = 1 := (genY_pow_eq_one_iff φ (b * N)).mpr hy
  have hX : genX p r φ ^ (a * N * ((N - 1) * b * p ^ (r - 1) + 1)) = 1 := by
    rw [genX_pow_eq_one_iff]
    exact Nat.dvd_trans hx (dvd_mul_right (a * N) _)
  rw [hY, hX, mul_one]

/-- Under the shift-action hypothesis, the mixed element raised to `2 * p ^ (r + 1) / Nat.gcd a
(2 * p ^ r)` is one. -/
lemma pow_eq_one_branch1 {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (a b : ℕ) :
    (genX p r φ ^ a * genY p r φ ^ b) ^
      (2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)) = 1 := by
  apply pow_genX_mul_genY_eq_one hp hr φ hφ
  · exact dvd_mul_of_dvd_right (p_dvd_div_gcd_mul_p a) b
  · exact dvd_mul_div_gcd_mul_p hp a

/-- Under the shift-action hypothesis and `p ^ r` not dividing `a`, the mixed element raised to
`2 * p ^ r / Nat.gcd a (2 * p ^ r)` is one. -/
lemma pow_eq_one_branch2 {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) {a b : ℕ}
    (hpr : ¬ p ^ r ∣ a) :
    (genX p r φ ^ a * genY p r φ ^ b) ^
      (2 * p ^ r / Nat.gcd a (2 * p ^ r)) = 1 := by
  apply pow_genX_mul_genY_eq_one hp hr φ hφ
  · exact dvd_mul_of_dvd_right (p_dvd_div_gcd hp (by omega) hpr) b
  · exact dvd_mul_div_gcd hp a

/-- For prime `p`, the element `genX ^ a * genY ^ 0` raised to `2 * p ^ r / Nat.gcd a (2 * p ^
r)` is one. -/
lemma pow_eq_one_branch2_zero {p r : ℕ} (hp : p.Prime)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (a : ℕ) :
    (genX p r φ ^ a * genY p r φ ^ 0) ^
      (2 * p ^ r / Nat.gcd a (2 * p ^ r)) = 1 := by
  rw [pow_zero, mul_one, ← pow_mul, genX_pow_eq_one_iff]
  exact dvd_mul_div_gcd hp a

/-- If `g ^ N = 1` for positive `N`, the subgroup generated by `g` consists of its natural
powers with exponents strictly below `N`. -/
lemma zpowers_eq_range_of_pow_eq_one {G : Type*} [Group G] (g : G) {N : ℕ} (hN : 0 < N)
    (h : g ^ N = 1) :
    (Subgroup.zpowers g : Set G) = {x | ∃ i : ℕ, i < N ∧ x = g ^ i} := by
  ext x
  constructor
  · intro hx
    change x ∈ Subgroup.zpowers g at hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨(m % (N : ℤ)).toNat, ?_, ?_⟩
    · have h1 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg m (by exact_mod_cast hN.ne')
      have h2 : m % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hN)
      omega
    · rw [← hm, zpow_eq_zpow_emod' m h, ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hN.ne'))]
  · rintro ⟨i, -, rfl⟩
    change g ^ i ∈ Subgroup.zpowers g
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(i : ℤ), zpow_natCast g i⟩

/-- For prime `p`, `r ≥ 2`, the shift action, and bounded representatives, the cyclic subgroup
of a mixed element is enumerated by powers through one less than the specified quotient in
each arithmetic branch. See [Chi et al., 2006, Proposition 4][ChiKimLee2006]. -/
theorem proposition4_cyclic_subgroup
    {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    (a b : ℕ) (ha : a ≤ 2 * p ^ r - 1) (hb : b ≤ p - 1) :
    (Subgroup.zpowers (genX p r φ ^ a * genY p r φ ^ b) : Set (SDP p r φ)) =
      if p ^ r ∣ a ∧ b ≠ 0 then
        {g | ∃ i : ℕ,
            i ≤ 2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r) - 1 ∧
              g = (genX p r φ ^ a * genY p r φ ^ b) ^ i}
      else
        {g | ∃ i : ℕ,
            i ≤ 2 * p ^ r / Nat.gcd a (2 * p ^ r) - 1 ∧
              g = (genX p r φ ^ a * genY p r φ ^ b) ^ i} := by
  by_cases hc : p ^ r ∣ a ∧ b ≠ 0
  · rw [if_pos hc]
    have hN : 0 < 2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r) := pos_div_gcd_mul_p hp a
    have hone := pow_eq_one_branch1 hp hr φ hφ a b
    rw [zpowers_eq_range_of_pow_eq_one _ hN hone]
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩
  · rw [if_neg hc]
    have hN : 0 < 2 * p ^ r / Nat.gcd a (2 * p ^ r) := pos_div_gcd hp a
    rcases not_and_or.mp hc with hpr | hb0
    · have hone := pow_eq_one_branch2 hp hr φ hφ (a := a) (b := b) hpr
      rw [zpowers_eq_range_of_pow_eq_one _ hN hone]
      ext x
      constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, by omega, rfl⟩
    · have hbzero : b = 0 := by
        by_contra h
        exact hb0 h
      subst hbzero
      have hone := pow_eq_one_branch2_zero hp φ a
      rw [zpowers_eq_range_of_pow_eq_one _ hN hone]
      ext x
      constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, by omega, rfl⟩

end Qatlib.Papers.SemiDirectHSP06.MainResults
