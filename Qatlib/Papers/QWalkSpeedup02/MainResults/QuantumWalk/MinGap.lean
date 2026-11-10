/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.MinGap

def edgeWeight (n c : ℕ) : ℝ := if c = n then Real.sqrt 2 else 1

lemma edgeWeight_at (n : ℕ) : edgeWeight n n = Real.sqrt 2 := by
  simp [edgeWeight]

lemma edgeWeight_off {n c : ℕ} (h : c ≠ n) : edgeWeight n c = 1 := by
  simp [edgeWeight, h]

def IsPathEigen (n : ℕ) (f : ℕ → ℝ) (lam : ℝ) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 2 * n →
    edgeWeight n (c - 1) * f (c - 1) + edgeWeight n c * f (c + 1) = lam * f c

def IsEigenvalue (n : ℕ) (lam : ℝ) : Prop :=
  ∃ f : ℕ → ℝ, f 0 = 0 ∧ f (2 * n + 1) = 0 ∧ f ≠ 0 ∧ IsPathEigen n f lam

def reflectFun (n : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := fun c => f (2 * n + 1 - c)

lemma reflectFun_involutive_on (n : ℕ) (f : ℕ → ℝ) {c : ℕ} (hc : c ≤ 2 * n + 1) :
    reflectFun n (reflectFun n f) c = f c := by
  simp only [reflectFun]
  congr 1
  omega

lemma edgeWeight_reflect (n : ℕ) (hn : 0 < n) (c : ℕ) :
    edgeWeight n c = edgeWeight n (2 * n - c) := by
  by_cases h : c = n
  · rw [h]
    have h2 : 2 * n - n = n := by omega
    rw [h2]
  · simp [edgeWeight, h, show ¬(2 * n - c = n) by omega]

lemma reflectFun_pathEigen (n : ℕ) (hn : 0 < n) {f : ℕ → ℝ} {lam : ℝ}
    (h : IsPathEigen n f lam) : IsPathEigen n (reflectFun n f) lam := by
  intro c hc1 hc2
  have hc := h (2 * n + 1 - c) (by omega) (by omega)
  have ek1 : 2 * n + 1 - c - 1 = 2 * n - c := by omega
  have ek2 : 2 * n + 1 - c + 1 = 2 * n + 2 - c := by omega
  rw [ek1, ek2] at hc
  simp only [reflectFun]
  have g1 : 2 * n + 1 - (c - 1) = 2 * n + 2 - c := by omega
  have g2 : 2 * n + 1 - (c + 1) = 2 * n - c := by omega
  rw [g1, g2]
  rw [edgeWeight_reflect n hn c, edgeWeight_reflect n hn (c - 1)]
  rw [show 2 * n - (c - 1) = 2 * n + 1 - c by omega]
  linarith [hc]

lemma reflectFun_pathEigen_rev (n : ℕ) (hn : 0 < n) {f : ℕ → ℝ} {lam : ℝ}
    (h : IsPathEigen n (reflectFun n f) lam) : IsPathEigen n f lam := by
  intro c hc1 hc2
  have hc := h (2 * n + 1 - c) (by omega) (by omega)
  have ek1 : 2 * n + 1 - c - 1 = 2 * n - c := by omega
  have ek2 : 2 * n + 1 - c + 1 = 2 * n + 2 - c := by omega
  rw [ek1, ek2] at hc
  simp only [reflectFun] at hc
  have q1 : 2 * n + 1 - (2 * n - c) = c + 1 := by omega
  have q2 : 2 * n + 1 - (2 * n + 2 - c) = c - 1 := by omega
  have q3 : 2 * n + 1 - (2 * n + 1 - c) = c := by omega
  rw [q1, q2, q3] at hc
  rw [edgeWeight_reflect n hn c, edgeWeight_reflect n hn (c - 1)]
  rw [show 2 * n - (c - 1) = 2 * n + 1 - c by omega]
  linarith [hc]

lemma reflectFun_pathEigen_iff (n : ℕ) (hn : 0 < n) (f : ℕ → ℝ) (lam : ℝ) :
    IsPathEigen n (reflectFun n f) lam ↔ IsPathEigen n f lam :=
  ⟨reflectFun_pathEigen_rev n hn, reflectFun_pathEigen n hn⟩

def ansatzFun (n : ℕ) (p s : ℝ) : ℕ → ℝ :=
  fun c =>
    if c = 0 then 0
    else if c ≤ n then Real.sin (p * (c : ℝ))
    else s * Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)))

lemma ansatzFun_zero (n : ℕ) (p s : ℝ) : ansatzFun n p s 0 = 0 := by
  simp [ansatzFun]

lemma ansatzFun_left {n : ℕ} {p s : ℝ} {c : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n) :
    ansatzFun n p s c = Real.sin (p * (c : ℝ)) := by
  simp only [ansatzFun, if_neg (show c ≠ 0 by omega), if_pos hcn]

lemma ansatzFun_right {n : ℕ} {p s : ℝ} {c : ℕ} (hc : 1 ≤ c) (hcn : n < c) :
    ansatzFun n p s c = s * Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ))) := by
  simp only [ansatzFun, if_neg (show c ≠ 0 by omega), if_neg (show ¬ c ≤ n by omega)]

lemma sin_shift_add (p : ℝ) (c : ℝ) :
    Real.sin (p * (c - 1)) + Real.sin (p * (c + 1)) = 2 * Real.cos p * Real.sin (p * c) := by
  rw [Real.sin_add_sin]
  rw [show (p * (c - 1) + p * (c + 1)) / 2 = p * c by ring]
  rw [show (p * (c - 1) - p * (c + 1)) / 2 = -p by ring]
  rw [Real.cos_neg]
  ring

lemma sin_pair_n (n : ℕ) (p : ℝ) :
    Real.sin (p * ((n : ℝ) + 1)) + Real.sin (p * ((n : ℝ) - 1))
      = 2 * Real.cos p * Real.sin (p * (n : ℝ)) := by
  have h := sin_shift_add p (n : ℝ)
  linarith [h]

lemma matching_iff (n : ℕ) (p s : ℝ) :
    (s * Real.sqrt 2 * Real.sin (p * (n : ℝ)) + Real.sin (p * ((n : ℝ) - 1))
        = 2 * Real.cos p * Real.sin (p * (n : ℝ)))
      ↔ Real.sin (p * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sin (p * (n : ℝ)) := by
  have hpair := sin_pair_n n p
  constructor
  · intro h; linarith [hpair, h]
  · intro h; linarith [hpair, h]

theorem ansatz_path_eigen {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hs : s ^ 2 = 1)
    (hmatch : Real.sin (p * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sin (p * (n : ℝ))) :
    IsPathEigen n (ansatzFun n p s) (2 * Real.cos p) := by
  intro c hc1 hc2
  by_cases hcase1 : c = 1
  · subst hcase1
    have h0 : (1 : ℕ) - 1 = 0 := by norm_num
    have h2 : (1 : ℕ) + 1 = 2 := by norm_num
    rw [h0, h2]
    rw [ansatzFun_zero]
    rw [ansatzFun_left (c := 2) (by omega) (by omega)]
    rw [ansatzFun_left (c := 1) (by omega) (by omega)]
    rw [edgeWeight_off (n := n) (c := 0) (by omega),
        edgeWeight_off (n := n) (c := 1) (by omega)]
    simp only [zero_add, one_mul]
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2]
    simp only [Nat.cast_one, mul_one]
    rw [show p * 2 = 2 * p by ring, Real.sin_two_mul]
    ring
  · have hc2' : 2 ≤ c := by omega
    by_cases hleft : c ≤ n - 1
    · rw [ansatzFun_left (c := c - 1) (by omega) (by omega)]
      rw [ansatzFun_left (c := c + 1) (by omega) (by omega)]
      rw [ansatzFun_left (c := c) hc1 (by omega)]
      rw [edgeWeight_off (n := n) (c := c - 1) (by omega),
          edgeWeight_off (n := n) (c := c) (by omega)]
      simp only [one_mul]
      have e1 : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ c)]; norm_num
      have e2 : ((c + 1 : ℕ) : ℝ) = (c : ℝ) + 1 := by push_cast; ring
      rw [e1, e2]
      exact sin_shift_add p (c : ℝ)
    · have hcn : n ≤ c := by omega
      by_cases hcaseN : c = n
      · rw [hcaseN]
        rw [ansatzFun_left (c := n - 1) (by omega) (by omega)]
        rw [ansatzFun_right (c := n + 1) (by omega) (by omega)]
        rw [ansatzFun_left (c := n) (by omega) (by omega)]
        rw [edgeWeight_off (n := n) (c := n - 1) (by omega), edgeWeight_at n]
        simp only [one_mul]
        have e1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
          push_cast; ring
        rw [e1, e2]
        have hpair := sin_pair_n n p
        have h53 := (matching_iff n p s).mpr hmatch
        linarith [hpair, h53]
      · have hn1 : n + 1 ≤ c := by omega
        by_cases hcaseN1 : c = n + 1
        · subst hcaseN1
          have hsub : (n + 1) - 1 = n := by omega
          rw [hsub]
          rw [ansatzFun_left (c := n) (by omega) (by omega)]
          rw [ansatzFun_right (c := n + 1 + 1) (by omega) (by omega)]
          rw [ansatzFun_right (c := n + 1) (by omega) (by omega)]
          rw [edgeWeight_at n, edgeWeight_off (n := n) (c := n + 1) (by omega)]
          simp only [one_mul]
          have e1 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 + 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
            push_cast; ring
          have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
            push_cast; ring
          rw [e1, e2]
          have h53 := (matching_iff n p s).mpr hmatch
          have hs1 : s = 1 ∨ s = -1 := by
            have hfac : (s - 1) * (s + 1) = 0 := by nlinarith [hs]
            rcases mul_eq_zero.mp hfac with h | h
            · left; linarith
            · right; linarith
          rcases hs1 with rfl | rfl <;> nlinarith [h53]
        · have hn2 : n + 2 ≤ c := by omega
          rw [ansatzFun_right (c := c - 1) (by omega) (by omega)]
          rw [ansatzFun_right (c := c + 1) (by omega) (by omega)]
          rw [ansatzFun_right (c := c) (by omega) (by omega)]
          rw [edgeWeight_off (n := n) (c := c - 1) (by omega),
              edgeWeight_off (n := n) (c := c) (by omega)]
          simp only [one_mul]
          have e1 : (((2 * n + 1 : ℕ) : ℝ) - ((c - 1 : ℕ) : ℝ))
              = (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)) + 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ c)]; ring
          have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((c + 1 : ℕ) : ℝ))
              = (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)) - 1 := by
            push_cast; ring
          rw [e1, e2]
          rw [show s * Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) + 1))
                + s * Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) - 1))
              = s * (Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) - 1))
                + Real.sin (p * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) + 1))) by ring]
          rw [sin_shift_add p (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ))]
          ring

theorem ansatz_eigenvalue {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hs : s ^ 2 = 1)
    (hsinp : Real.sin p ≠ 0)
    (hmatch : Real.sin (p * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sin (p * (n : ℝ))) :
    IsEigenvalue n (2 * Real.cos p) := by
  refine ⟨ansatzFun n p s, ansatzFun_zero n p s, ?_, ?_, ansatz_path_eigen hn hs hmatch⟩
  · have h := ansatzFun_right (n := n) (p := p) (s := s) (c := 2 * n + 1)
      (by omega) (by omega)
    rw [h]
    rw [show (((2 * n + 1 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ)) = 0 by ring,
      mul_zero, Real.sin_zero, mul_zero]
  · intro hzero
    have h1 := congrFun hzero 1
    rw [ansatzFun_left (c := 1) (by omega) (by omega)] at h1
    simp only [Nat.cast_one, mul_one] at h1
    exact hsinp h1

theorem matching_of_path_eigen {n : ℕ} (hn : 2 ≤ n) {p s lam : ℝ}
    (hsinp : Real.sin p ≠ 0) (h : IsPathEigen n (ansatzFun n p s) lam) :
    lam = 2 * Real.cos p ∧
      Real.sin (p * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sin (p * (n : ℝ)) := by
  have hzero : ansatzFun n p s 0 = 0 := ansatzFun_zero n p s
  have hc1 := h 1 (by norm_num) (by omega)
  rw [show ((1 : ℕ) - 1) = 0 by norm_num,
      show ((1 : ℕ) + 1) = 2 by norm_num, hzero,
      edgeWeight_off (n := n) (c := 0) (by omega),
      edgeWeight_off (n := n) (c := 1) (by omega)] at hc1
  rw [ansatzFun_left (c := 2) (by norm_num) (by omega),
      ansatzFun_left (c := 1) (by norm_num) (by omega)] at hc1
  simp only [zero_add, one_mul] at hc1
  have hcast1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast1, mul_one, hcast2] at hc1
  have hlam : lam = 2 * Real.cos p := by
    have h3 : Real.sin (p * 2) = 2 * Real.cos p * Real.sin p := by
      rw [show p * 2 = 2 * p by ring, Real.sin_two_mul]; ring
    rw [h3] at hc1
    exact mul_right_cancel₀ hsinp (by linarith [hc1])
  refine ⟨hlam, ?_⟩
  have hcn := h n (by omega) (by omega)
  rw [ansatzFun_left (c := n - 1) (by omega) (by omega),
      ansatzFun_right (c := n + 1) (by omega) (by omega),
      ansatzFun_left (c := n) (by omega) (by omega),
      edgeWeight_off (n := n) (c := n - 1) (by omega), edgeWeight_at n] at hcn
  simp only [one_mul] at hcn
  have e1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
    push_cast; ring
  rw [e1, e2, hlam] at hcn
  have h53' : s * Real.sqrt 2 * Real.sin (p * (n : ℝ))
      + Real.sin (p * ((n : ℝ) - 1)) = 2 * Real.cos p * Real.sin (p * (n : ℝ)) := by
    linarith [hcn]
  exact (matching_iff n p s).mp h53'

def sinhFun (n : ℕ) (k s : ℝ) : ℕ → ℝ :=
  fun c =>
    if c = 0 then 0
    else if c ≤ n then Real.sinh (k * (c : ℝ))
    else s * Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)))

lemma sinhFun_zero (n : ℕ) (k s : ℝ) : sinhFun n k s 0 = 0 := by
  simp [sinhFun]

lemma sinhFun_left {n : ℕ} {k s : ℝ} {c : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n) :
    sinhFun n k s c = Real.sinh (k * (c : ℝ)) := by
  simp only [sinhFun, if_neg (show c ≠ 0 by omega), if_pos hcn]

lemma sinhFun_right {n : ℕ} {k s : ℝ} {c : ℕ} (hc : 1 ≤ c) (hcn : n < c) :
    sinhFun n k s c = s * Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ))) := by
  simp only [sinhFun, if_neg (show c ≠ 0 by omega), if_neg (show ¬ c ≤ n by omega)]

lemma sinh_shift_add (k c : ℝ) :
    Real.sinh (k * (c - 1)) + Real.sinh (k * (c + 1))
      = 2 * Real.cosh k * Real.sinh (k * c) := by
  rw [show k * (c - 1) = k * c - k by ring,
      show k * (c + 1) = k * c + k by ring, Real.sinh_sub, Real.sinh_add]
  ring

lemma sinh_pair_n (n : ℕ) (k : ℝ) :
    Real.sinh (k * ((n : ℝ) + 1)) + Real.sinh (k * ((n : ℝ) - 1))
      = 2 * Real.cosh k * Real.sinh (k * (n : ℝ)) := by
  have h := sinh_shift_add k (n : ℝ)
  linarith [h]

lemma sinh_matching_iff (n : ℕ) (k s : ℝ) :
    (s * Real.sqrt 2 * Real.sinh (k * (n : ℝ)) + Real.sinh (k * ((n : ℝ) - 1))
        = 2 * Real.cosh k * Real.sinh (k * (n : ℝ)))
      ↔ Real.sinh (k * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sinh (k * (n : ℝ)) := by
  have hpair := sinh_pair_n n k
  constructor
  · intro h; linarith [hpair, h]
  · intro h; linarith [hpair, h]

theorem sinh_path_eigen {n : ℕ} (hn : 2 ≤ n) {k s : ℝ} (hs : s ^ 2 = 1)
    (hmatch : Real.sinh (k * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sinh (k * (n : ℝ))) :
    IsPathEigen n (sinhFun n k s) (2 * Real.cosh k) := by
  intro c hc1 hc2
  by_cases hcase1 : c = 1
  · rw [hcase1]
    rw [show ((1 : ℕ) - 1) = 0 by norm_num, show ((1 : ℕ) + 1) = 2 by norm_num,
        sinhFun_zero,
        edgeWeight_off (n := n) (c := 0) (by omega),
        edgeWeight_off (n := n) (c := 1) (by omega)]
    rw [sinhFun_left (c := 2) (by norm_num) (by omega),
        sinhFun_left (c := 1) (by norm_num) (by omega)]
    simp only [zero_add, one_mul]
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2]
    simp only [Nat.cast_one, mul_one]
    rw [show k * 2 = 2 * k by ring, show (2 : ℝ) * k = k + k by ring, Real.sinh_add]
    ring
  · have hc2' : 2 ≤ c := by omega
    by_cases hleft : c ≤ n - 1
    · rw [sinhFun_left (c := c - 1) (by omega) (by omega)]
      rw [sinhFun_left (c := c + 1) (by omega) (by omega)]
      rw [sinhFun_left (c := c) hc1 (by omega)]
      rw [edgeWeight_off (n := n) (c := c - 1) (by omega),
          edgeWeight_off (n := n) (c := c) (by omega)]
      simp only [one_mul]
      have e1 : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ c)]; norm_num
      have e2 : ((c + 1 : ℕ) : ℝ) = (c : ℝ) + 1 := by push_cast; ring
      rw [e1, e2]
      exact sinh_shift_add k (c : ℝ)
    · have hcn : n ≤ c := by omega
      by_cases hcaseN : c = n
      · rw [hcaseN]
        rw [sinhFun_left (c := n - 1) (by omega) (by omega),
            sinhFun_right (c := n + 1) (by omega) (by omega),
            sinhFun_left (c := n) (by omega) (by omega),
            edgeWeight_off (n := n) (c := n - 1) (by omega), edgeWeight_at n]
        simp only [one_mul]
        have e1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
          push_cast; ring
        rw [e1, e2]
        have hpair := sinh_pair_n n k
        have h65 := (sinh_matching_iff n k s).mpr hmatch
        linarith [hpair, h65]
      · have hn1 : n + 1 ≤ c := by omega
        by_cases hcaseN1 : c = n + 1
        · rw [hcaseN1]
          have hsub : (n + 1) - 1 = n := by omega
          rw [hsub]
          rw [sinhFun_left (c := n) (by omega) (by omega)]
          rw [sinhFun_right (c := n + 1 + 1) (by omega) (by omega)]
          rw [sinhFun_right (c := n + 1) (by omega) (by omega)]
          rw [edgeWeight_at n, edgeWeight_off (n := n) (c := n + 1) (by omega)]
          simp only [one_mul]
          have e1 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 + 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
            push_cast; ring
          have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
            push_cast; ring
          rw [e1, e2]
          have h65 := (sinh_matching_iff n k s).mpr hmatch
          have hs1 : s = 1 ∨ s = -1 := by
            have hfac : (s - 1) * (s + 1) = 0 := by nlinarith [hs]
            rcases mul_eq_zero.mp hfac with h | h
            · left; linarith
            · right; linarith
          rcases hs1 with rfl | rfl <;> nlinarith [h65]
        · have hn2 : n + 2 ≤ c := by omega
          rw [sinhFun_right (c := c - 1) (by omega) (by omega)]
          rw [sinhFun_right (c := c + 1) (by omega) (by omega)]
          rw [sinhFun_right (c := c) (by omega) (by omega)]
          rw [edgeWeight_off (n := n) (c := c - 1) (by omega),
              edgeWeight_off (n := n) (c := c) (by omega)]
          simp only [one_mul]
          have e1 : (((2 * n + 1 : ℕ) : ℝ) - ((c - 1 : ℕ) : ℝ))
              = (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)) + 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ c)]; ring
          have e2 : (((2 * n + 1 : ℕ) : ℝ) - ((c + 1 : ℕ) : ℝ))
              = (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ)) - 1 := by
            push_cast; ring
          rw [e1, e2]
          rw [show s * Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) + 1))
                + s * Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) - 1))
              = s * (Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) - 1))
                + Real.sinh (k * (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ) + 1))) by ring]
          rw [sinh_shift_add k (((2 * n + 1 : ℕ) : ℝ) - (c : ℝ))]
          ring

theorem sinh_ansatz_eigenvalue {n : ℕ} (hn : 2 ≤ n) {k s : ℝ} (hs : s ^ 2 = 1)
    (hsinh : Real.sinh (k * (n : ℝ)) ≠ 0)
    (hmatch : Real.sinh (k * ((n : ℝ) + 1)) = Real.sqrt 2 * s * Real.sinh (k * (n : ℝ))) :
    IsEigenvalue n (2 * Real.cosh k) := by
  refine ⟨sinhFun n k s, sinhFun_zero n k s, ?_, ?_, sinh_path_eigen hn hs hmatch⟩
  · have h := sinhFun_right (n := n) (k := k) (s := s) (c := 2 * n + 1) (by omega) (by omega)
    rw [h]
    rw [show (((2 * n + 1 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ)) = 0 by ring,
      mul_zero, Real.sinh_zero, mul_zero]
  · intro hzero
    have h1 := congrFun hzero n
    rw [sinhFun_left (c := n) (by omega) (by omega)] at h1
    exact hsinh h1

lemma abs_two_cos_sub_eq (p q : ℝ) (havg : 0 ≤ Real.sin ((p + q) / 2)) :
    |2 * Real.cos p - 2 * Real.cos q|
      = 4 * Real.sin ((p + q) / 2) * |Real.sin ((p - q) / 2)| := by
  have hkey : 2 * Real.cos p - 2 * Real.cos q
      = -(4 * Real.sin ((p + q) / 2) * Real.sin ((p - q) / 2)) := by
    have h := Real.cos_sub_cos p q
    linarith [h]
  calc |2 * Real.cos p - 2 * Real.cos q|
      = |-(4 * Real.sin ((p + q) / 2) * Real.sin ((p - q) / 2))| := by rw [hkey]
    _ = 4 * Real.sin ((p + q) / 2) * |Real.sin ((p - q) / 2)| := by
        rw [abs_neg, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg havg]

theorem eigenvalue_gap_of_root_gap {n : ℕ} (hn : 2 ≤ n) {p q : ℝ}
    (havg : 0 ≤ Real.sin ((p + q) / 2))
    (hampl : 2 / (n : ℝ) ≤ Real.sin ((p + q) / 2))
    (hclose : |p - q| ≤ Real.pi)
    (hroot : Real.pi / ((1 + Real.sqrt 2) * (n : ℝ) ^ 2) ≤ |p - q|) :
    8 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 3) ≤ |2 * Real.cos p - 2 * Real.cos q| := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hden' : (0 : ℝ) < (1 + Real.sqrt 2) * (n : ℝ) ^ 2 := by positivity
  rw [abs_two_cos_sub_eq p q havg]
  have hhalf : |(p - q) / 2| = |p - q| / 2 := by rw [abs_div]; norm_num
  have hx : |(p - q) / 2| ≤ Real.pi / 2 := by
    rw [hhalf]; linarith
  have hsin_ge : (2 / Real.pi) * |(p - q) / 2| ≤ |Real.sin ((p - q) / 2)| :=
    Real.mul_abs_le_abs_sin hx
  have hsin_ge' : |p - q| / Real.pi ≤ |Real.sin ((p - q) / 2)| := by
    have heq : |p - q| / Real.pi = (2 / Real.pi) * |(p - q) / 2| := by
      rw [hhalf]; field_simp
    rw [heq]; exact hsin_ge
  have hstep1 : 4 * (2 / (n : ℝ)) * (|p - q| / Real.pi)
      ≤ 4 * Real.sin ((p + q) / 2) * |Real.sin ((p - q) / 2)| := by
    have hprod : (2 / (n : ℝ)) * (|p - q| / Real.pi)
        ≤ Real.sin ((p + q) / 2) * |Real.sin ((p - q) / 2)| :=
      mul_le_mul hampl hsin_ge' (by positivity) havg
    have h4 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
    linarith [h4]
  have hstep2 : 8 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 3)
      ≤ 4 * (2 / (n : ℝ)) * (|p - q| / Real.pi) := by
    have hdiv : 1 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 2) ≤ |p - q| / Real.pi := by
      have h1 : Real.pi / ((1 + Real.sqrt 2) * (n : ℝ) ^ 2) / Real.pi
          = 1 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 2) := by
        field_simp
      have h := div_le_div_of_nonneg_right hroot hπpos.le
      rwa [h1] at h
    have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 4 * (2 / (n : ℝ)))
    have heq : 4 * (2 / (n : ℝ)) * (1 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 2))
        = 8 / ((1 + Real.sqrt 2) * (n : ℝ) ^ 3) := by
      field_simp; ring
    linarith [hmul, heq]
  linarith [hstep1, hstep2]

theorem eight_lt_two_pi_sq : (8 : ℝ) < 2 * Real.pi ^ 2 / (1 + Real.sqrt 2) := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hsqrt : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.42)]
    norm_num
  have hden : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hpi2 : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith [hpi]
  rw [lt_div_iff₀ hden]
  nlinarith [hpi2, hsqrt]

end Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.MinGap
