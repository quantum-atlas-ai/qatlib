/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace Qatlib.Papers.GaussSumEst02.MainResults.Source

structure MultChar (K : Type*) [Field K] where
  toFun : K → ℂ
  map_zero' : toFun 0 = 0
  map_one' : toFun 1 = 1
  map_mul' : ∀ x y : K, toFun (x * y) = toFun x * toFun y
  norm_eq_one : ∀ x : K, x ≠ 0 → ‖toFun x‖ = 1

namespace MultChar

variable {K : Type*} [Field K] (χ : MultChar K)

lemma toFun_ne_zero {x : K} (hx : x ≠ 0) : χ.toFun x ≠ 0 := by
  intro h
  have h1 := χ.map_mul' x x⁻¹
  rw [mul_inv_cancel₀ hx, χ.map_one'] at h1
  rw [h, zero_mul] at h1
  exact one_ne_zero h1

lemma conj_eq_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have h2 : conj z * z = 1 := by
    have h := Complex.normSq_eq_conj_mul_self (z := z)
    rw [hsq] at h
    exact h.symm
  exact eq_inv_of_mul_eq_one_left h2

lemma conj_apply {x : K} (hx : x ≠ 0) : conj (χ.toFun x) = (χ.toFun x)⁻¹ :=
  conj_eq_inv_of_norm_one (χ.norm_eq_one x hx)

lemma inv_apply {x : K} (hx : x ≠ 0) : χ.toFun x⁻¹ = (χ.toFun x)⁻¹ := by
  have h := χ.map_mul' x x⁻¹
  rw [mul_inv_cancel₀ hx, χ.map_one'] at h
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

lemma pow_apply (x : K) (n : ℕ) : χ.toFun (x ^ n) = χ.toFun x ^ n := by
  induction n with
  | zero => simp [χ.map_one']
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

def IsNontrivial : Prop := ∃ x : K, x ≠ 0 ∧ χ.toFun x ≠ 1

end MultChar

structure AddChar (K : Type*) [AddCommGroup K] where
  toFun : K → ℂ
  map_zero' : toFun 0 = 1
  map_add' : ∀ x y : K, toFun (x + y) = toFun x * toFun y
  nontrivial : ∃ x : K, toFun x ≠ 1

namespace AddChar

variable {K : Type*} [AddCommGroup K] (e : AddChar K)

lemma pow_apply (n : ℕ) (x : K) : e.toFun (n • x) = e.toFun x ^ n := by
  induction n with
  | zero => simp [e.map_zero']
  | succ n ih => rw [succ_nsmul, e.map_add', ih, pow_succ]

lemma apply_ne_zero (x : K) : e.toFun x ≠ 0 := by
  intro h
  have hh : e.toFun x * e.toFun (-x) = 1 := by
    rw [← e.map_add', add_neg_cancel, e.map_zero']
  rw [h, zero_mul] at hh
  exact zero_ne_one hh

lemma norm_eq_one [Fintype K] (x : K) : ‖e.toFun x‖ = 1 := by
  have hpow := e.pow_apply (Fintype.card K) x
  rw [card_nsmul_eq_zero, e.map_zero'] at hpow
  have hN : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  have hnorm : ‖e.toFun x‖ ^ Fintype.card K = 1 := by
    rw [← norm_pow, ← hpow]
    simp
  have hnn : 0 ≤ ‖e.toFun x‖ := norm_nonneg _
  rcases (pow_eq_one_iff_of_ne_zero (a := ‖e.toFun x‖) (n := Fintype.card K) hN).mp hnorm
    with h | ⟨h, _⟩
  · exact h
  · rw [h] at hnn; norm_num at hnn

lemma conj_apply [Fintype K] (x : K) : conj (e.toFun x) = e.toFun (-x) := by
  rw [MultChar.conj_eq_inv_of_norm_one (e.norm_eq_one x)]
  exact (eq_inv_of_mul_eq_one_right (by rw [← e.map_add', add_neg_cancel, e.map_zero'])).symm

lemma sum_mul_eq_zero {F : Type*} [Field F] [Fintype F] (e' : AddChar F) {c : F}
    (hc : c ≠ 0) : (∑ x : F, e'.toFun (c * x)) = 0 := by
  obtain ⟨z, hz⟩ := e'.nontrivial
  obtain ⟨y, hy⟩ : ∃ y : F, c * y = z := ⟨c⁻¹ * z, by field_simp⟩
  rw [← hy] at hz
  have hstep : e'.toFun (c * y) * (∑ x : F, e'.toFun (c * x))
      = ∑ x : F, e'.toFun (c * x) := by
    rw [Finset.mul_sum]
    calc ∑ x : F, e'.toFun (c * y) * e'.toFun (c * x)
        = ∑ x : F, e'.toFun (c * y + c * x) := by
          exact Finset.sum_congr rfl fun x _ => (e'.map_add' _ _).symm
      _ = ∑ x : F, e'.toFun (c * (x + y)) := by
          exact Finset.sum_congr rfl fun x _ => by congr 1; ring
      _ = ∑ x : F, e'.toFun (c * x) := by
          have h := Equiv.sum_comp (Equiv.addRight y) (fun x : F => e'.toFun (c * x))
          simpa using h
  have h2 : (e'.toFun (c * y) - 1) * (∑ x : F, e'.toFun (c * x)) = 0 := by
    rw [sub_mul, one_mul, hstep, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hz)

end AddChar

def gaussSum {K : Type*} [Field K] [Fintype K] (χ : K → ℂ) (e : AddChar K) (β : K) : ℂ :=
  ∑ x : K, χ x * e.toFun (β * x)

theorem multChar_sum_eq_zero {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (hnt : χ.IsNontrivial) : (∑ x : K, χ.toFun x) = 0 := by
  obtain ⟨a, ha0, ha⟩ := hnt
  have hmul : χ.toFun a * (∑ x : K, χ.toFun x) = ∑ x : K, χ.toFun x := by
    rw [Finset.mul_sum]
    calc ∑ x : K, χ.toFun a * χ.toFun x
        = ∑ x : K, χ.toFun (a * x) := by
          exact Finset.sum_congr rfl fun x _ => (χ.map_mul' a x).symm
      _ = ∑ x : K, χ.toFun x := by
          have h := Equiv.sum_comp (Equiv.mulLeft₀ a ha0) (fun x : K => χ.toFun x)
          simpa using h
  have h2 : (χ.toFun a - 1) * (∑ x : K, χ.toFun x) = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

theorem gaussSum_scale {K : Type*} [Field K] [Fintype K] (χ : MultChar K) (e : AddChar K)
    {β δ : K} (hβ : β ≠ 0) :
    gaussSum χ.toFun e (β * δ) = χ.toFun β⁻¹ * gaussSum χ.toFun e δ := by
  rw [gaussSum, gaussSum, Finset.mul_sum]
  calc ∑ x : K, χ.toFun x * e.toFun (β * δ * x)
      = ∑ x : K, χ.toFun β⁻¹ * (χ.toFun (β * x) * e.toFun (δ * (β * x))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hx : β⁻¹ * (β * x) = x := by field_simp
        have hχ : χ.toFun x = χ.toFun β⁻¹ * χ.toFun (β * x) := by
          rw [← χ.map_mul', hx]
        have he : e.toFun (β * δ * x) = e.toFun (δ * (β * x)) := by
          congr 1
          ring
        rw [hχ, he]
        ring
    _ = ∑ z : K, χ.toFun β⁻¹ * (χ.toFun z * e.toFun (δ * z)) := by
        have h := Equiv.sum_comp (Equiv.mulLeft₀ β hβ)
          (fun z : K => χ.toFun β⁻¹ * (χ.toFun z * e.toFun (δ * z)))
        simpa using h

theorem gaussSum_normSq {K : Type*} [Field K] [Fintype K] (χ : MultChar K) (e : AddChar K)
    (hnt : χ.IsNontrivial) {β : K} (hβ : β ≠ 0) :
    Complex.normSq (gaussSum χ.toFun e β) = (Fintype.card K : ℝ) := by
  set G : ℂ := gaussSum χ.toFun e β with hGdef
  set term : K → ℂ := fun x => χ.toFun x * e.toFun (β * x) with hterm
  set conjTerm : K → ℂ := fun y => χ.toFun y⁻¹ * e.toFun (-(β * y)) with hconjTerm
  have hconj : conj G = ∑ y : K, conjTerm y := by
    rw [hGdef, gaussSum, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y = 0
    · subst hy
      simp [conjTerm, χ.map_zero']
    · simp only [conjTerm, map_mul, χ.conj_apply hy, e.conj_apply, χ.inv_apply hy]
  have hInner (y : K) :
      (∑ x : K, conjTerm y * term x)
        = ∑ t : K, χ.toFun t * e.toFun (β * y * (t - 1)) := by
    by_cases hy : y = 0
    · subst hy
      have hL : (∑ x : K, conjTerm 0 * term x) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [conjTerm, χ.map_zero']
      have hR : (∑ t : K, χ.toFun t * e.toFun (β * 0 * (t - 1))) = 0 := by
        have h1 : (fun t : K => χ.toFun t * e.toFun (β * 0 * (t - 1)))
            = (fun t : K => χ.toFun t) := by
          funext t
          rw [show β * 0 * (t - 1) = 0 by ring, e.map_zero', mul_one]
        rw [h1]
        exact multChar_sum_eq_zero χ hnt
      rw [hL, hR]
    · have hre : (∑ x : K, conjTerm y * term x)
          = ∑ x : K, conjTerm y * term (y * x) := by
        have h := Equiv.sum_comp (Equiv.mulLeft₀ y hy)
          (fun x : K => conjTerm y * term x)
        simpa using h.symm
      rw [hre]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [conjTerm, term]
      have hyinv : χ.toFun y⁻¹ * χ.toFun y = 1 := by
        rw [← χ.map_mul', inv_mul_cancel₀ hy, χ.map_one']
      have he : e.toFun (-(β * y)) * e.toFun (β * (y * t)) = e.toFun (β * y * (t - 1)) := by
        rw [← e.map_add']
        congr 1
        ring
      calc χ.toFun y⁻¹ * e.toFun (-(β * y)) * (χ.toFun (y * t) * e.toFun (β * (y * t)))
          = (χ.toFun y⁻¹ * χ.toFun y) * χ.toFun t
              * (e.toFun (-(β * y)) * e.toFun (β * (y * t))) := by
            rw [χ.map_mul']; ring
        _ = χ.toFun t * e.toFun (β * y * (t - 1)) := by
            rw [hyinv, he]; ring
  have hswap : (∑ y : K, ∑ x : K, conjTerm y * term x)
      = ∑ t : K, χ.toFun t * ∑ y : K, e.toFun (β * y * (t - 1)) := by
    calc (∑ y : K, ∑ x : K, conjTerm y * term x)
        = ∑ y : K, ∑ t : K, χ.toFun t * e.toFun (β * y * (t - 1)) := by
          exact Finset.sum_congr rfl fun y _ => hInner y
      _ = ∑ t : K, ∑ y : K, χ.toFun t * e.toFun (β * y * (t - 1)) := Finset.sum_comm
      _ = ∑ t : K, χ.toFun t * ∑ y : K, e.toFun (β * y * (t - 1)) := by
          exact Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]
  have hFinal : (∑ t : K, χ.toFun t * ∑ y : K, e.toFun (β * y * (t - 1)))
      = (Fintype.card K : ℂ) := by
    rw [Finset.sum_eq_single (1 : K)]
    · have h1 : (∑ y : K, e.toFun (β * y * ((1 : K) - 1))) = (Fintype.card K : ℂ) := by
        simp [e.map_zero']
      rw [h1, χ.map_one', one_mul]
    · intro t _ ht
      have hc : β * (t - 1) ≠ 0 := mul_ne_zero hβ (sub_ne_zero.mpr ht)
      have hsum : (∑ y : K, e.toFun (β * y * (t - 1))) = 0 := by
        have hpt : ∀ y : K, e.toFun (β * y * (t - 1))
            = e.toFun ((β * (t - 1)) * y) := by
          intro y
          congr 1
          ring
        calc ∑ y : K, e.toFun (β * y * (t - 1))
            = ∑ y : K, e.toFun ((β * (t - 1)) * y) :=
              Finset.sum_congr rfl fun y _ => hpt y
          _ = 0 := e.sum_mul_eq_zero hc
      rw [hsum, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ (1 : K)) h1
  have hval : conj G * G = (Fintype.card K : ℂ) := by
    have hstep : conj G * G = ∑ y : K, ∑ x : K, conjTerm y * term x := by
      rw [hconj, hGdef, gaussSum, Fintype.sum_mul_sum]
    rw [hstep, hswap, hFinal]
  apply Complex.ofReal_inj.mp
  rw [Complex.normSq_eq_conj_mul_self (z := G)]
  exact hval

theorem gaussSum_norm {K : Type*} [Field K] [Fintype K] (χ : MultChar K) (e : AddChar K)
    (hnt : χ.IsNontrivial) {β : K} (hβ : β ≠ 0) :
    ‖gaussSum χ.toFun e β‖ = Real.sqrt (Fintype.card K) := by
  have hsq := gaussSum_normSq χ e hnt hβ
  rw [Complex.normSq_eq_norm_sq] at hsq
  calc ‖gaussSum χ.toFun e β‖
      = Real.sqrt (‖gaussSum χ.toFun e β‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (Fintype.card K) := by rw [hsq]

theorem gaussSum_polar {K : Type*} [Field K] [Fintype K] (χ : MultChar K) (e : AddChar K)
    (hnt : χ.IsNontrivial) {β : K} (hβ : β ≠ 0) :
    ∃ γ : ℝ, gaussSum χ.toFun e β
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γ * Complex.I) := by
  set G := gaussSum χ.toFun e β with hGdef
  have hNpos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.mpr hNpos
  have hc_ne : ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact hsqrt_pos.ne'
  have hunit : ‖G / ((Real.sqrt (Fintype.card K) : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, gaussSum_norm χ e hnt hβ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt_pos, div_self hsqrt_pos.ne']
  obtain ⟨γ, _, hγ⟩ := Complex.norm_eq_one_iff'.mp hunit
  refine ⟨γ, ?_⟩
  rw [hγ]
  field_simp

def trivialMultChar (K : Type*) [Field K] : MultChar K where
  toFun := fun x => by classical exact (if x = 0 then 0 else 1)
  map_zero' := by classical exact if_pos rfl
  map_one' := by classical simp
  map_mul' x y := by
    classical
    by_cases hx : x = 0
    · subst hx
      simp
    · by_cases hy : y = 0
      · subst hy
        simp
      · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        simp [hx, hy, hxy]
  norm_eq_one x hx := by classical simp [hx]

theorem trivialMultChar_apply_ne_zero {K : Type*} [Field K] {x : K} (hx : x ≠ 0) :
    (trivialMultChar K).toFun x = 1 := by
  classical
  simp [trivialMultChar, hx]

theorem gaussSum_trivial_zero {K : Type*} [Field K] [Fintype K] (e : AddChar K) :
    gaussSum (trivialMultChar K).toFun e 0 = ((Fintype.card K - 1 : ℕ) : ℂ) := by
  classical
  rw [gaussSum]
  have hterm : ∀ x : K, (trivialMultChar K).toFun x * e.toFun (0 * x)
      = (trivialMultChar K).toFun x := by
    intro x
    rw [zero_mul, e.map_zero', mul_one]
  simp only [hterm]
  have hpt : ∀ x : K, (trivialMultChar K).toFun x
      = 1 - (if x = 0 then (1 : ℂ) else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [trivialMultChar]
    · simp [trivialMultChar, hx]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ (0 : K))]
  have hc : 1 ≤ Fintype.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact Fintype.card_pos
  rw [Nat.cast_sub hc]
  push_cast
  ring

theorem gaussSum_trivial_ne {K : Type*} [Field K] [Fintype K] (e : AddChar K) {β : K}
    (hβ : β ≠ 0) : gaussSum (trivialMultChar K).toFun e β = -1 := by
  classical
  rw [gaussSum]
  have hterm : ∀ x : K, (trivialMultChar K).toFun x * e.toFun (β * x)
      = if x = 0 then (0 : ℂ) else e.toFun (β * x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [trivialMultChar]
    · simp [trivialMultChar, hx]
  simp only [hterm]
  have hleft : (∑ x : K, (if x = 0 then (0 : ℂ) else e.toFun (β * x)))
      = ∑ x ∈ Finset.univ.erase (0 : K), e.toFun (β * x) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset K)
      (fun x : K => if x = 0 then (0 : ℂ) else e.toFun (β * x))
      (Finset.mem_univ (0 : K))]
    rw [if_pos rfl, add_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [if_neg (Finset.mem_erase.mp hx).1]
  rw [hleft]
  have hfull : (∑ x : K, e.toFun (β * x)) = 0 := e.sum_mul_eq_zero hβ
  have hsplit : (∑ x : K, e.toFun (β * x))
      = (∑ x ∈ Finset.univ.erase (0 : K), e.toFun (β * x)) + 1 := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset K)
      (fun x : K => e.toFun (β * x)) (Finset.mem_univ (0 : K))]
    rw [mul_zero, e.map_zero']
  have hσ : (∑ x ∈ Finset.univ.erase (0 : K), e.toFun (β * x)) + 1 = 0 := by
    rw [← hsplit, hfull]
  have := congrArg (fun z : ℂ => z - 1) hσ
  simpa using this

theorem gaussSum_nontrivial_zero {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (e : AddChar K) (hnt : χ.IsNontrivial) : gaussSum χ.toFun e 0 = 0 := by
  rw [gaussSum]
  simp only [zero_mul, e.map_zero', mul_one]
  exact multChar_sum_eq_zero χ hnt

def chiState {K : Type*} [Field K] [Fintype K] (χ : MultChar K) : K → ℂ :=
  fun x => χ.toFun x / ((Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ)) : ℂ)

def fourierChi {K : Type*} [Field K] [Fintype K] (χ : MultChar K) (e : AddChar K) (β : K) :
    K → ℂ :=
  fun y => ((Real.sqrt (Fintype.card K : ℝ) : ℂ))⁻¹
    * ∑ x : K, chiState χ x * e.toFun (β * y * x)

theorem algorithm1_phase_change {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (e : AddChar K) (hnt : χ.IsNontrivial) {β : K} (hβ : β ≠ 0) :
    (fun y => (χ.toFun y) ^ 2 * fourierChi χ e β y)
      = (gaussSum χ.toFun e β / ((Real.sqrt (Fintype.card K : ℝ)) : ℂ)) • chiState χ := by
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K); omega
  have hNpos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden_pos : 0 < Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < ((Fintype.card K - 1 : ℕ) : ℝ) := by
      have : 0 < Fintype.card K - 1 := by omega
      exact_mod_cast this
    exact this
  have hden_ne : ((Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact hden_pos.ne'
  have hsqrt_ne : ((Real.sqrt (Fintype.card K : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hNpos).ne'
  funext y
  by_cases hy : y = 0
  · subst hy
    simp [fourierChi, chiState, χ.map_zero']
  · have hscale : gaussSum χ.toFun e (β * y) = χ.toFun y⁻¹ * gaussSum χ.toFun e β := by
      rw [mul_comm β y]
      exact gaussSum_scale χ e hy
    have hinner : (∑ x : K, chiState χ x * e.toFun (β * y * x))
        = (((Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ)) : ℂ))⁻¹
            * gaussSum χ.toFun e (β * y) := by
      rw [gaussSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [chiState]
      rw [div_eq_mul_inv]
      ring
    have hy_ne : χ.toFun y ≠ 0 := χ.toFun_ne_zero hy
    have hyinv : χ.toFun y⁻¹ = (χ.toFun y)⁻¹ := χ.inv_apply hy
    simp only [fourierChi, Pi.smul_apply, smul_eq_mul]
    rw [hinner, hscale, hyinv]
    unfold chiState
    field_simp

end Qatlib.Papers.GaussSumEst02.MainResults.Source
