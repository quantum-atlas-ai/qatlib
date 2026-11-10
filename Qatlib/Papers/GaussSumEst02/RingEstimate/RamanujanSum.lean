/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.RingEstimate.CharacterSums
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Totient
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.RingEstimate

open Qatlib.Papers.GaussSumEst02.MainResults.Source

theorem sum_zmod_eq_sum_range {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    (∑ x : ZMod n, f x) = ∑ i ∈ Finset.range n, f (i : ZMod n) := by
  refine Finset.sum_nbij (fun x : ZMod n => x.val) ?_ ?_ ?_ ?_
  · intro x _; simpa using ZMod.val_lt x
  · intro a _ b _ h; exact ZMod.val_injective n h
  · intro b hb
    refine ⟨(b : ZMod n), by simp, ?_⟩
    exact ZMod.val_natCast_of_lt (by simpa using hb)
  · intro a _; rw [ZMod.natCast_zmod_val]

theorem pow_pred_mul {p r : ℕ} (hr : 1 ≤ r) : p ^ (r - 1) * p = p ^ r := by
  calc p ^ (r - 1) * p = p ^ ((r - 1) + 1) := (pow_succ _ _).symm
    _ = p ^ r := by congr 1; omega

theorem sum_range_dvd {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range (p ^ (r - 1)), f (p * j))
      = ∑ i ∈ (Finset.range (p ^ r)).filter (fun i => p ∣ i), f i := by
  have hpr : p ^ r = p ^ (r - 1) * p := (pow_pred_mul hr).symm
  refine Finset.sum_nbij (fun j => p * j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at *
    exact ⟨by rw [hpr]; simpa [mul_comm] using Nat.mul_lt_mul_of_pos_left hj hp.pos,
      dvd_mul_right p j⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hlt, hdvd⟩ := hi
    refine ⟨i / p, ?_, Nat.mul_div_cancel' hdvd⟩
    rw [hpr] at hlt
    rw [Finset.mem_coe, Finset.mem_range]
    exact (Nat.div_lt_iff_lt_mul hp.pos).mpr hlt
  · intro a _; rfl

def IsPrimitiveAddChar {n : ℕ} (e : AddChar (ZMod n)) : Prop :=
  ∀ x : ZMod n, e.toFun x = 1 → x = 0

theorem sum_primitive_shift {n : ℕ} [NeZero n] (e : AddChar (ZMod n))
    (he : IsPrimitiveAddChar e) (β : ZMod n) :
    (∑ x : ZMod n, e.toFun (β * x)) = if β = 0 then (n : ℂ) else 0 := by
  have hpow : ∀ i : ℕ, e.toFun (β * (i : ZMod n)) = (e.toFun β) ^ i := by
    intro i
    rw [show β * (i : ZMod n) = i • β by rw [nsmul_eq_mul, mul_comm]]
    exact e.pow_apply i β
  have hzero : (n : ℕ) • β = 0 := by
    simp
  have hθn : (e.toFun β) ^ n = 1 := by
    rw [← e.pow_apply n β, hzero, e.map_zero']
  have hval : (∑ x : ZMod n, e.toFun (β * x))
      = ∑ i ∈ Finset.range n, (e.toFun β) ^ i := by
    rw [sum_zmod_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => hpow i
  rw [hval]
  by_cases hθ : e.toFun β = 1
  · rw [if_pos (he β hθ)]
    simp [hθ]
  · rw [if_neg (fun h => hθ (by rw [h]; exact e.map_zero'))]
    have hmul : (∑ i ∈ Finset.range n, (e.toFun β) ^ i) * (e.toFun β - 1) = 0 := by
      rw [geom_sum_mul, hθn, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hθ)

theorem sum_nonunit_shift {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p ^ r)]
    (e : AddChar (ZMod (p ^ r))) (β : ZMod (p ^ r)) :
    (∑ x : ZMod (p ^ r), if ¬ IsUnit x then e.toFun (β * x) else 0)
      = ∑ j ∈ Finset.range (p ^ (r - 1)), (e.toFun (β * (p : ZMod (p ^ r)))) ^ j := by
  have hcond : ∀ i : ℕ, (¬ IsUnit ((i : ZMod (p ^ r)))) ↔ p ∣ i := by
    intro i
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hr]
    simp
  rw [sum_zmod_eq_sum_range]
  simp only [hcond]
  rw [← Finset.sum_filter]
  rw [← sum_range_dvd hp hr (fun i => e.toFun (β * (i : ZMod (p ^ r))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcast : β * ((p * j : ℕ) : ZMod (p ^ r))
      = j • (β * (p : ZMod (p ^ r))) := by
    rw [Nat.cast_mul, nsmul_eq_mul]
    ring
  rw [hcast]
  exact e.pow_apply j (β * (p : ZMod (p ^ r)))

theorem mul_pow_eq_zero_of_dvd {p r a : ℕ} (hr : 1 ≤ r) (ha : p ^ (r - 1) ∣ a) :
    ((a * p : ℕ) : ZMod (p ^ r)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  rw [hk, ← pow_pred_mul hr]
  ring

theorem dvd_of_mul_pow_eq_zero {p r a : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : ((a * p : ℕ) : ZMod (p ^ r)) = 0) : p ^ (r - 1) ∣ a := by
  rw [ZMod.natCast_eq_zero_iff] at h
  have hpr : p ^ r = p ^ (r - 1) * p := (pow_pred_mul hr).symm
  rw [hpr] at h
  exact (Nat.mul_dvd_mul_iff_right hp.pos).mp h

theorem sum_nonunit_primitive {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p ^ r)]
    (e : AddChar (ZMod (p ^ r))) (he : IsPrimitiveAddChar e) (β : ZMod (p ^ r)) :
    (∑ x : ZMod (p ^ r), if ¬ IsUnit x then e.toFun (β * x) else 0)
      = if (p ^ (r - 1) : ℕ) ∣ β.val then (p ^ (r - 1) : ℂ) else 0 := by
  rw [sum_nonunit_shift hp hr e β]

  have hkey : e.toFun (β * (p : ZMod (p ^ r))) = 1 ↔ (p ^ (r - 1) : ℕ) ∣ β.val := by
    constructor
    · intro hc
      have h1 : β * (p : ZMod (p ^ r)) = 0 := he _ hc
      have h2 : ((β.val * p : ℕ) : ZMod (p ^ r)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        exact h1
      exact dvd_of_mul_pow_eq_zero hp hr h2
    · intro hd
      have h2 : ((β.val * p : ℕ) : ZMod (p ^ r)) = 0 := mul_pow_eq_zero_of_dvd hr hd
      have h3 : β * (p : ZMod (p ^ r)) = 0 := by
        rw [← ZMod.natCast_zmod_val β, ← Nat.cast_mul, h2]
      rw [h3, e.map_zero']
  by_cases hβ : (p ^ (r - 1) : ℕ) ∣ β.val
  · rw [if_pos hβ]
    simp [hkey.mpr hβ]
  · rw [if_neg hβ]
    have hθn : (e.toFun (β * (p : ZMod (p ^ r)))) ^ (p ^ (r - 1)) = 1 := by
      rw [← e.pow_apply (p ^ (r - 1)) (β * (p : ZMod (p ^ r)))]
      have hzero : (p ^ (r - 1) : ℕ) • (β * (p : ZMod (p ^ r))) = 0 := by
        rw [nsmul_eq_mul]
        have hpn : ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) * (p : ZMod (p ^ r)) = 0 := by
          rw [← Nat.cast_mul, pow_pred_mul hr, ZMod.natCast_self]
        calc ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) * (β * (p : ZMod (p ^ r)))
            = β * (((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) * (p : ZMod (p ^ r))) := by ring
          _ = β * 0 := by rw [hpn]
          _ = 0 := mul_zero β
      rw [hzero, e.map_zero']
    have hθ : e.toFun (β * (p : ZMod (p ^ r))) ≠ 1 := fun hc => hβ (hkey.mp hc)
    have hmul : (∑ j ∈ Finset.range (p ^ (r - 1)),
        (e.toFun (β * (p : ZMod (p ^ r)))) ^ j) * (e.toFun (β * (p : ZMod (p ^ r))) - 1)
        = 0 := by
      rw [geom_sum_mul, hθn, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hθ)

def zmodAddChar (n : ℕ) [NeZero n] (hn : 1 < n) : AddChar (ZMod n) where
  toFun := ⇑(ZMod.stdAddChar (N := n))
  map_zero' := ZMod.stdAddChar.map_zero_eq_one
  map_add' x y := ZMod.stdAddChar.map_add_eq_mul x y
  nontrivial := by
    refine ⟨1, ?_⟩
    intro h
    have h1 : ((1 : ℕ) : ZMod n) = 0 :=
      ZMod.injective_stdAddChar (by simpa using h)
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp h1
    have hn1 : n = 1 := Nat.dvd_one.mp hd
    omega

theorem zmodAddChar_primitive (n : ℕ) [NeZero n] (hn : 1 < n) :
    IsPrimitiveAddChar (zmodAddChar n hn) := by
  intro x hx
  have hx' : (zmodAddChar n hn).toFun x = (zmodAddChar n hn).toFun 0 := by
    rw [hx]
    exact (ZMod.stdAddChar.map_zero_eq_one).symm
  exact ZMod.injective_stdAddChar hx'

theorem ringGaussSum_trivial_ramanujan {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    [NeZero (p ^ r)] (χ : DirichletChar (p ^ r)) (e : AddChar (ZMod (p ^ r)))
    (he : IsPrimitiveAddChar e) (hχ : IsTrivialChar χ) (β : ZMod (p ^ r)) :
    ringGaussSum χ e β
      = (if β = 0 then (p : ℂ) ^ r else 0)
        - (if (p ^ (r - 1) : ℕ) ∣ β.val then (p ^ (r - 1) : ℂ) else 0) := by
  have hsplit : ringGaussSum χ e β
      = (∑ x : ZMod (p ^ r), e.toFun (β * x))
        - (∑ x : ZMod (p ^ r), if ¬ IsUnit x then e.toFun (β * x) else 0) := by
    rw [ringGaussSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : IsUnit x
    · rw [if_neg (not_not.mpr hx), hχ x hx, one_mul, sub_zero]
    · rw [if_pos hx, χ.map_zero_of_not_unit x hx, zero_mul, sub_self]
  rw [hsplit, sum_primitive_shift e he β, sum_nonunit_primitive hp hr e he β,
    Nat.cast_pow]

theorem ringGaussSum_trivial_ramanujan_cases {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    [NeZero (p ^ r)] (χ : DirichletChar (p ^ r)) (e : AddChar (ZMod (p ^ r)))
    (he : IsPrimitiveAddChar e) (hχ : IsTrivialChar χ) :
    (ringGaussSum χ e 0 = (p ^ (r - 1) * (p - 1) : ℕ)) ∧
    (∀ β : ZMod (p ^ r), β ≠ 0 → (p ^ (r - 1) : ℕ) ∣ β.val →
      ringGaussSum χ e β = -(p ^ (r - 1) : ℂ)) ∧
    (∀ β : ZMod (p ^ r), β ≠ 0 → ¬ (p ^ (r - 1) : ℕ) ∣ β.val →
      ringGaussSum χ e β = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ringGaussSum_trivial_ramanujan hp hr χ e he hχ 0]
    have h0 : (0 : ZMod (p ^ r)).val = 0 := by simp
    rw [if_pos rfl, h0, if_pos (dvd_zero _)]
    have hp1 : p ^ (r - 1) ≤ p ^ r := by
      rw [← pow_pred_mul hr]; exact Nat.le_mul_of_pos_right _ hp.pos
    have hnat : p ^ r - p ^ (r - 1) = p ^ (r - 1) * (p - 1) := by
      rw [← pow_pred_mul hr, Nat.mul_sub_left_distrib, mul_one]
    have hcast : ((p ^ r - p ^ (r - 1) : ℕ) : ℂ)
        = ((p ^ (r - 1) * (p - 1) : ℕ) : ℂ) := by rw [hnat]
    rw [Nat.cast_sub hp1] at hcast
    simp only [Nat.cast_pow] at hcast
    exact hcast
  · intro β hβ hd
    rw [ringGaussSum_trivial_ramanujan hp hr χ e he hχ β, if_neg hβ, if_pos hd]
    ring
  · intro β hβ hd
    rw [ringGaussSum_trivial_ramanujan hp hr χ e he hχ β, if_neg hβ, if_neg hd]
    ring

end Qatlib.Papers.GaussSumEst02.RingEstimate
