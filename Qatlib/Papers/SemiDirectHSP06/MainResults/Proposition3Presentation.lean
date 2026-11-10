/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Defs
import Mathlib.GroupTheory.OrderOfElement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

lemma pow_eq_mul_pred (hr : 1 ≤ r) : p ^ r = p * p ^ (r - 1) := by
  rw [← pow_succ']
  congr 1
  omega

lemma dvd_two_pow_pred_of_dvd (hp : p.Prime) (hr : 1 ≤ r)
    {d : ℕ} (hd : d ∣ 2 * p ^ r) (hnd : ¬ d ∣ 2 * p ^ (r - 1)) : p ^ r ∣ d := by
  obtain ⟨k, hk⟩ := hd
  have h2p : 2 * p ^ r = p * (2 * p ^ (r - 1)) := by
    rw [pow_eq_mul_pred (p := p) hr]; ring
  have hnp : ¬ p ∣ k := by
    intro hpk
    obtain ⟨k', hk'⟩ := hpk
    apply hnd
    refine ⟨k', ?_⟩
    have hEq : p * (2 * p ^ (r - 1)) = p * (d * k') := by
      rw [← h2p, hk, hk']; ring
    exact Nat.mul_left_cancel hp.pos hEq
  have hdiv : p ^ r ∣ d * k := ⟨2, by rw [← hk]; ring⟩
  exact ((hp.coprime_iff_not_dvd.mpr hnp).pow_left r).dvd_of_dvd_mul_right hdiv

lemma gcd_two_pow_pred_eq {a : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (h : ¬ p ^ r ∣ a) :
    Nat.gcd a (2 * p ^ (r - 1)) = Nat.gcd a (2 * p ^ r) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact Nat.dvd_trans (Nat.gcd_dvd_right _ _)
      (Nat.mul_dvd_mul_left 2 (Nat.pow_dvd_pow p (by omega)))
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    by_contra hnd
    exact h (Nat.dvd_trans
      (dvd_two_pow_pred_of_dvd hp hr (Nat.gcd_dvd_right _ _) hnd) (Nat.gcd_dvd_left _ _))

lemma gcd_two_pow_mul_eq (a : ℕ) (hr : 1 ≤ r) :
    Nat.gcd (2 * p ^ r) (a * p) = p * Nat.gcd (2 * p ^ (r - 1)) a := by
  have h2p : 2 * p ^ r = p * (2 * p ^ (r - 1)) := by
    rw [pow_eq_mul_pred (p := p) hr]; ring
  rw [h2p, Nat.mul_comm a p, Nat.gcd_mul_left]

lemma orderOf_ofAdd_eq_p (hp : p.Prime) {b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ p - 1) :
    orderOf (Multiplicative.ofAdd (b : ZMod p)) = p := by
  have hb1 : 1 ≤ b := by omega
  have hdvd : orderOf (Multiplicative.ofAdd (b : ZMod p)) ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hbp : ((b * p : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_left p b
    calc (Multiplicative.ofAdd (b : ZMod p)) ^ p
        = ((Multiplicative.ofAdd (1 : ZMod p)) ^ b) ^ p := by
          rw [ofAdd_one_pow]
      _ = (Multiplicative.ofAdd (1 : ZMod p)) ^ (b * p) := by rw [pow_mul]
      _ = Multiplicative.ofAdd ((b * p : ℕ) : ZMod p) := ofAdd_one_pow p (b * p)
      _ = 1 := by rw [hbp]; rfl
  have hne : orderOf (Multiplicative.ofAdd (b : ZMod p)) ≠ 1 := by
    intro hone
    have hbmod : ((b : ℕ) : ZMod p) = 0 := by
      have := congrArg Multiplicative.toAdd ((orderOf_eq_one_iff).mp hone)
      simpa using this
    have hpdvd : p ∣ b := by
      rwa [ZMod.natCast_eq_zero_iff] at hbmod
    have hle : p ≤ b := Nat.le_of_dvd (by omega) hpdvd
    omega
  exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne

lemma p_dvd_orderOf_genX_mul_genY (hp : p.Prime)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {a b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ p - 1) :
    p ∣ orderOf (genX p r φ ^ a * genY p r φ ^ b) := by
  have hmap : SemidirectProduct.rightHom (genX p r φ ^ a * genY p r φ ^ b) =
      Multiplicative.ofAdd (b : ZMod p) := by
    simp [genX, genY, map_mul, map_pow, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, ofAdd_one_pow]
  have hdvd := orderOf_map_dvd (SemidirectProduct.rightHom) (genX p r φ ^ a * genY p r φ ^ b)
  rw [hmap, orderOf_ofAdd_eq_p hp hb0 hb] at hdvd
  exact hdvd

lemma genY_pow (m : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    genY p r φ ^ m = inr (Multiplicative.ofAdd (m : ZMod p)) := by
  rw [genY, ← map_pow, ofAdd_one_pow]

lemma phi_ofAdd_pow (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (b : ℕ) :
    φ (Multiplicative.ofAdd (b : ZMod p)) = shiftAut p r hp hr ^ b := by
  rw [← ofAdd_one_pow, map_pow, hφ]

lemma genY_mul_genX_pow (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (n : ℕ) :
    genY p r φ * genX p r φ ^ n =
      genX p r φ ^ (n * shiftVal p r) * genY p r φ := by
  have h := SemidirectProduct.inl_aut (φ := φ)
    (Multiplicative.ofAdd (1 : ZMod p))
    (Multiplicative.ofAdd (n : ZMod (2 * p ^ r)))
  have hφg : φ (Multiplicative.ofAdd (1 : ZMod p))
      (Multiplicative.ofAdd (n : ZMod (2 * p ^ r))) =
      Multiplicative.ofAdd ((n * shiftVal p r : ℕ) : ZMod (2 * p ^ r)) := by
    rw [hφ, shiftAut, mulAutOfUnit_apply, toAdd_ofAdd, coe_shiftUnit,
      ← Nat.cast_mul, Nat.mul_comm (shiftVal p r) n]
  have h1 : (inr (Multiplicative.ofAdd (1 : ZMod p)) *
      inl (Multiplicative.ofAdd (n : ZMod (2 * p ^ r))) : SDP p r φ) =
      inl (φ (Multiplicative.ofAdd (1 : ZMod p))
        (Multiplicative.ofAdd (n : ZMod (2 * p ^ r)))) *
      inr (Multiplicative.ofAdd (1 : ZMod p)) := by
    have hh := congrArg (fun t : SDP p r φ =>
      t * inr (Multiplicative.ofAdd (1 : ZMod p))) h
    simpa [mul_assoc] using hh.symm
  have h' : (inr (Multiplicative.ofAdd (1 : ZMod p)) *
      inl (Multiplicative.ofAdd (n : ZMod (2 * p ^ r))) : SDP p r φ) =
      inl (Multiplicative.ofAdd ((n * shiftVal p r : ℕ) : ZMod (2 * p ^ r))) *
      inr (Multiplicative.ofAdd (1 : ZMod p)) := by
    rw [h1, hφg]
  rw [genY, genX_pow, h']
  simp only [genX_pow]

lemma genY_pow_mul_genX_pow (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (a b : ℕ) :
    genY p r φ ^ b * genX p r φ ^ a =
      genX p r φ ^ (a * shiftVal p r ^ b) * genY p r φ ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc,
      genY_mul_genX_pow hp hr φ hφ (a * shiftVal p r ^ b), mul_assoc]
    have hY : genY p r φ * genY p r φ ^ b = genY p r φ ^ (b + 1) :=
      (pow_succ' (genY p r φ) b).symm
    have hX : a * shiftVal p r ^ b * shiftVal p r =
        a * shiftVal p r ^ (b + 1) := by
      conv_rhs => rw [pow_succ]
      ring
    rw [hY, hX]

lemma shiftVal_pow_mod (hp : p.Prime) (hr : 2 ≤ r) (b : ℕ) :
    ((shiftVal p r : ℕ) : ZMod (2 * p ^ r)) ^ b =
      ((2 * b * p ^ (r - 1) + 1 : ℕ) : ZMod (2 * p ^ r)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, ih, ← Nat.cast_mul]
    have hpow : p ^ (r - 1) * p ^ (r - 1) = p ^ (2 * r - 2) := by
      rw [← pow_add]; congr 1; omega
    have hprod : (2 * b * p ^ (r - 1) + 1) * shiftVal p r =
        2 * (b + 1) * p ^ (r - 1) + 1 + 4 * b * p ^ (2 * r - 2) := by
      unfold shiftVal
      have h1 : (2 * b * p ^ (r - 1) + 1) * (2 * p ^ (r - 1) + 1)
          = 2 * (b + 1) * p ^ (r - 1) + 1 +
            4 * b * (p ^ (r - 1) * p ^ (r - 1)) := by ring
      rw [h1, hpow]
    rw [hprod]
    have hD : ((4 * b * p ^ (2 * r - 2) : ℕ) : ZMod (2 * p ^ r)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      have hexp : r ≤ 2 * r - 2 := by omega
      obtain ⟨k, hk⟩ := Nat.pow_dvd_pow p hexp
      refine ⟨2 * b * k, ?_⟩
      rw [hk]; ring
    rw [Nat.cast_add, hD, add_zero]

lemma genX_pow_of_zmod_eq
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) {m n : ℕ}
    (h : (m : ZMod (2 * p ^ r)) = (n : ZMod (2 * p ^ r))) :
    genX p r φ ^ m = genX p r φ ^ n := by
  rw [genX_pow, genX_pow, h]

lemma genY_pow_mul_genX_pow_paper (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (a b : ℕ) :
    genY p r φ ^ b * genX p r φ ^ a =
      genX p r φ ^ (a * 2 * b * p ^ (r - 1) + a) * genY p r φ ^ b := by
  rw [genY_pow_mul_genX_pow hp hr φ hφ]
  have h : genX p r φ ^ (a * shiftVal p r ^ b) =
      genX p r φ ^ (a * 2 * b * p ^ (r - 1) + a) := by
    apply genX_pow_of_zmod_eq
    rw [Nat.cast_mul, Nat.cast_pow, shiftVal_pow_mod hp hr b]
    push_cast
    ring
  rw [h]

lemma pow_genX_mul_genY (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (a b k : ℕ) :
    (genX p r φ ^ a * genY p r φ ^ b) ^ k =
      genX p r φ ^ (a * k * ((k - 1) * b * p ^ (r - 1) + 1)) *
        genY p r φ ^ (b * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [mul_assoc]
    rw [← mul_assoc (genY p r φ ^ (b * k)) (genX p r φ ^ a) (genY p r φ ^ b)]
    rw [genY_pow_mul_genX_pow hp hr φ hφ a (b * k)]
    simp only [mul_assoc]
    rw [← mul_assoc]
    rw [← pow_add, ← pow_add]
    have hY : genY p r φ ^ (b * k + b) = genY p r φ ^ (b * (k + 1)) := by
      rw [genY_pow, genY_pow, show b * k + b = b * (k + 1) from by ring]
    rw [hY]
    have hX : genX p r φ ^ (a * (k * ((k - 1) * (b * p ^ (r - 1)) + 1)) +
        a * shiftVal p r ^ (b * k)) =
        genX p r φ ^ (a * ((k + 1) * ((k + 1 - 1) * (b * p ^ (r - 1)) + 1))) := by
      apply genX_pow_of_zmod_eq
      rcases k with _ | j
      · simp
      · have hk1 : (j + 1 - 1) = j := by simp
        have hk2 : (j + 1 + 1 - 1) = j + 1 := by simp
        rw [hk1, hk2]
        push_cast
        rw [shiftVal_pow_mod hp hr (b * (j + 1))]
        push_cast
        ring
    rw [hX]

lemma genX_pow_eq_one_iff
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (m : ℕ) :
    genX p r φ ^ m = 1 ↔ 2 * p ^ r ∣ m := by
  have key : (Multiplicative.ofAdd ((m : ZMod (2 * p ^ r)))) = 1 ↔
      (2 * p ^ r ∣ m) := by
    rw [← ZMod.natCast_eq_zero_iff m (2 * p ^ r)]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      simpa using this
    · intro h
      have : ((m : ZMod (2 * p ^ r))) = 0 := h
      rw [this]
      rfl
  rw [genX_pow]
  constructor
  · intro h
    have h1 : inl (φ := φ) (Multiplicative.ofAdd ((m : ZMod (2 * p ^ r)))) =
        inl (φ := φ) (1 : Multiplicative (ZMod (2 * p ^ r))) := by
      rw [map_one]
      exact h
    exact key.mp ((SemidirectProduct.inl_inj (φ := φ)).mp h1)
  · intro h
    have h1 : (Multiplicative.ofAdd ((m : ZMod (2 * p ^ r)))) = 1 := key.mpr h
    exact congrArg (inl (φ := φ)) h1

lemma genY_pow_eq_one_iff
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (m : ℕ) :
    genY p r φ ^ m = 1 ↔ p ∣ m := by
  have key : (Multiplicative.ofAdd ((m : ZMod p))) = 1 ↔ (p ∣ m) := by
    rw [← ZMod.natCast_eq_zero_iff m p]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      simpa using this
    · intro h
      have : ((m : ZMod p)) = 0 := h
      rw [this]
      rfl
  rw [genY_pow]
  constructor
  · intro h
    have h1 : inr (φ := φ) (Multiplicative.ofAdd ((m : ZMod p))) =
        inr (φ := φ) (1 : Multiplicative (ZMod p)) := by
      rw [map_one]
      exact h
    exact key.mp ((SemidirectProduct.inr_inj (φ := φ)).mp h1)
  · intro h
    have h1 : (Multiplicative.ofAdd ((m : ZMod p))) = 1 := key.mpr h
    exact congrArg (inr (φ := φ)) h1

instance fintypeSDP (p r : ℕ) [NeZero p] [NeZero (2 * p ^ r)]
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    Fintype (SDP p r φ) :=
  Fintype.ofEquiv _ (SemidirectProduct.equivProd).symm

lemma orderOf_genX (_hp : p.Prime) (_hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) :
    orderOf (genX p r φ) = 2 * p ^ r := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (genX_pow_eq_one_iff φ _).mpr dvd_rfl
  · exact (genX_pow_eq_one_iff φ _).mp (pow_orderOf_eq_one _)

lemma orderOf_pow_genX (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (a : ℕ) :
    orderOf (genX p r φ ^ a) = 2 * p ^ r / Nat.gcd (2 * p ^ r) a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (2 * p ^ r) := ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero)⟩
  rw [orderOf_pow, orderOf_genX hp hr]

lemma orderOf_genX_pow_eq (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (a : ℕ) :
    orderOf (genX p r φ ^ a) = 2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  rw [orderOf_pow_genX hp hr, Nat.gcd_comm]

lemma pow_p_eq (hp : p.Prime) (hr : 2 ≤ r) (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) (a b : ℕ) :
    (genX p r φ ^ a * genY p r φ ^ b) ^ p = genX p r φ ^ (a * p) := by
  rw [pow_genX_mul_genY hp hr φ hφ a b p]
  have hy : genY p r φ ^ (b * p) = 1 := by
    rw [genY_pow_eq_one_iff]
    exact dvd_mul_left p b
  rw [hy, mul_one]
  apply genX_pow_of_zmod_eq
  have hp1 : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]; congr 1; omega
  have hdecomp : a * p * ((p - 1) * b * p ^ (r - 1) + 1) =
      a * p + a * b * (p - 1) * p ^ r := by
    rw [← hp1]; ring
  rw [hdecomp, Nat.cast_add]
  have hzero : ((a * b * (p - 1) * p ^ r : ℕ) : ZMod (2 * p ^ r)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hp.even_sub_one hodd
    exact ⟨a * b * t, by rw [ht]; ring⟩
  rw [hzero, add_zero]

lemma orderOf_genX_mul_genY_ne_zero (hp : p.Prime) (hr : 2 ≤ r)
    (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    {a b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ p - 1) :
    orderOf (genX p r φ ^ a * genY p r φ ^ b) =
      p * (2 * p ^ r / Nat.gcd (2 * p ^ r) (a * p)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (2 * p ^ r) :=
    ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero)⟩
  have hpdvd := p_dvd_orderOf_genX_mul_genY (a := a) hp φ hb0 hb
  calc orderOf (genX p r φ ^ a * genY p r φ ^ b)
      = p * (orderOf (genX p r φ ^ a * genY p r φ ^ b) / p) :=
        (Nat.mul_div_cancel' hpdvd).symm
    _ = p * orderOf ((genX p r φ ^ a * genY p r φ ^ b) ^ p) := by
        rw [orderOf_pow, Nat.gcd_eq_right hpdvd]
    _ = p * orderOf (genX p r φ ^ (a * p)) := by
        rw [pow_p_eq hp hr hodd φ hφ a b]
    _ = p * (2 * p ^ r / Nat.gcd (2 * p ^ r) (a * p)) := by
        rw [orderOf_pow_genX hp hr φ (a * p)]

lemma arith_order_other {a : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hpr : ¬ p ^ r ∣ a) :
    p * (2 * p ^ r / Nat.gcd (2 * p ^ r) (a * p)) =
      2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  have h2p : 2 * p ^ r = p * (2 * p ^ (r - 1)) := by
    rw [pow_eq_mul_pred (p := p) hr]; ring
  rw [gcd_two_pow_mul_eq a hr]
  have hstep : p * (2 * p ^ r / (p * Nat.gcd (2 * p ^ (r - 1)) a)) =
      p * ((2 * p ^ (r - 1)) / Nat.gcd (2 * p ^ (r - 1)) a) := by
    rw [h2p, Nat.mul_div_mul_left _ _ hp.pos]
  rw [hstep]
  have hstep2 : p * ((2 * p ^ (r - 1)) / Nat.gcd (2 * p ^ (r - 1)) a) =
      2 * p ^ r / Nat.gcd (2 * p ^ (r - 1)) a := by
    rw [(Nat.mul_div_assoc p (Nat.gcd_dvd_left (2 * p ^ (r - 1)) a)).symm, h2p]
  rw [hstep2]
  have hg'' : Nat.gcd (2 * p ^ (r - 1)) a = Nat.gcd a (2 * p ^ r) := by
    rw [Nat.gcd_comm (2 * p ^ (r - 1)) a]
    exact gcd_two_pow_pred_eq hp hr hpr
  rw [hg'']

lemma orderOf_formula_other {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    {a b : ℕ} (hb : b ≤ p - 1) (hb0 : b ≠ 0)
    (hpr : ¬ p ^ r ∣ a) :
    orderOf (genX p r φ ^ a * genY p r φ ^ b) =
      2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  rw [orderOf_genX_mul_genY_ne_zero hp hr hodd φ hφ hb0 hb]
  exact arith_order_other hp (by omega) hpr

lemma eq_pow_of_dvd_and_le {p r a : ℕ} (hp : p.Prime) (ha : a ≤ 2 * p ^ r - 1)
    (h0 : a ≠ 0) (hd : p ^ r ∣ a) : a = p ^ r := by
  obtain ⟨m, rfl⟩ := hd
  have hpos : 0 < p ^ r := pow_pos hp.pos r
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp at h0
    · exact hm
  have hlt : m < 2 := by
    have h2 : p ^ r * m < 2 * p ^ r := by omega
    rw [Nat.mul_comm 2 (p ^ r)] at h2
    exact (Nat.mul_lt_mul_left hpos).mp h2
  have hm : m = 1 := by omega
  rw [hm, mul_one]

lemma orderOf_genX_pow_mul_genY_zero {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r)))) (a : ℕ) :
    orderOf (genX p r φ ^ a * genY p r φ ^ 0) =
      2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  rw [pow_zero, mul_one, orderOf_pow_genX hp hr, Nat.gcd_comm]

lemma orderOf_genY_pow_eq_p {p r : ℕ} (hp : p.Prime)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ p - 1) :
    orderOf (genX p r φ ^ 0 * genY p r φ ^ b) = p := by
  rw [pow_zero, one_mul, genY_pow]
  rw [orderOf_injective (SemidirectProduct.inr (φ := φ)) SemidirectProduct.inr_injective]
  exact orderOf_ofAdd_eq_p hp hb0 hb

lemma orderOf_genX_pow_r_mul_genY {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    {b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ p - 1) :
    orderOf (genX p r φ ^ (p ^ r) * genY p r φ ^ b) = 2 * p := by
  rw [orderOf_genX_mul_genY_ne_zero hp hr hodd φ hφ hb0 hb]
  have hgcd : Nat.gcd (2 * p ^ r) (p ^ r * p) = p ^ r := by
    have h1 : p ^ r * p = p * p ^ r := Nat.mul_comm _ _
    rw [h1, Nat.gcd_mul_right]
    have h2 : Nat.gcd 2 p = 1 := by
      rw [Nat.gcd_comm]
      exact hp.coprime_iff_not_dvd.mpr
        (fun hd => hodd ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp hd).symm)
    rw [h2, one_mul]
  rw [hgcd, Nat.mul_div_cancel _ (pow_pos hp.pos r)]
  ring

lemma orderOf_genX_mul_genY_formula {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    {a b : ℕ} (ha : a ≤ 2 * p ^ r - 1) (hb : b ≤ p - 1) :
    orderOf (genX p r φ ^ a * genY p r φ ^ b) =
      if p ^ r ∣ a ∧ b ≠ 0 then
        2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)
      else 2 * p ^ r / Nat.gcd a (2 * p ^ r) := by
  by_cases h : p ^ r ∣ a ∧ b ≠ 0
  · rw [if_pos h]
    obtain ⟨hd, hb0⟩ := h
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      rw [orderOf_genY_pow_eq_p hp φ hb0 hb]
      have hg : Nat.gcd 0 (2 * p ^ r) = 2 * p ^ r := Nat.gcd_zero_left _
      rw [hg]
      have h2 : 2 * p ^ (r + 1) = p * (2 * p ^ r) := by rw [pow_succ']; ring
      rw [h2, Nat.mul_div_cancel p (Nat.mul_pos (by norm_num) (pow_pos hp.pos r))]
    · have haeq : a = p ^ r := eq_pow_of_dvd_and_le hp ha (by omega) hd
      subst haeq
      rw [orderOf_genX_pow_r_mul_genY hp hr hodd φ hφ hb0 hb]
      have hgcd : Nat.gcd (p ^ r) (2 * p ^ r) = p ^ r :=
        (Nat.gcd_eq_left_iff_dvd).mpr ⟨2, Nat.mul_comm 2 (p ^ r)⟩
      have h2pr : 2 * p ^ (r + 1) = 2 * p * p ^ r := by
        rw [pow_succ]
        ring
      rw [hgcd, h2pr, Nat.mul_div_cancel (2 * p) (pow_pos hp.pos r)]
  · rw [if_neg h]
    by_cases hb0 : b = 0
    · subst hb0
      exact orderOf_genX_pow_mul_genY_zero hp hr φ a
    · exact orderOf_formula_other hp hr hodd φ hφ hb hb0 (fun hd => h ⟨hd, hb0⟩)

theorem proposition3_presentation
    {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) :
    (∀ a b : ℕ,
        genY p r φ ^ b * genX p r φ ^ a =
          genX p r φ ^ (a * 2 * b * p ^ (r - 1) + a) * genY p r φ ^ b) ∧
    (∀ a b k : ℕ,
        (genX p r φ ^ a * genY p r φ ^ b) ^ k =
          genX p r φ ^ (a * k * ((k - 1) * b * p ^ (r - 1) + 1)) *
            genY p r φ ^ (b * k)) ∧
    (∀ a b : ℕ,
        (genX p r φ ^ a * genY p r φ ^ b) ^ p = genX p r φ ^ (a * p)) ∧
    (∀ a b : ℕ, a ≤ 2 * p ^ r - 1 → b ≤ p - 1 →
        orderOf (genX p r φ ^ a * genY p r φ ^ b) =
          if p ^ r ∣ a ∧ b ≠ 0 then
            2 * p ^ (r + 1) / Nat.gcd a (2 * p ^ r)
          else
            2 * p ^ r / Nat.gcd a (2 * p ^ r)) :=
  ⟨fun a b => genY_pow_mul_genX_pow_paper hp hr φ hφ a b,
   fun a b k => pow_genX_mul_genY hp hr φ hφ a b k,
   fun a b => pow_p_eq hp hr hodd φ hφ a b,
   fun a b ha hb => orderOf_genX_mul_genY_formula hp hr hodd φ hφ ha hb⟩

end Qatlib.Papers.SemiDirectHSP06.MainResults
