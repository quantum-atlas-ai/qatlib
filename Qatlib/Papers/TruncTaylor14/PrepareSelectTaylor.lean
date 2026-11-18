/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.PrepareSelectAmplitude

@[expose] public section

/-!
# Concrete Taylor weights and exact rotation angles

For the order register in [BerryEtAl2015Taylor],
[arXiv:1412.4687v1](https://arxiv.org/abs/1412.4687v1), Eq. (23), the coefficient of order `k`
is `t^k / k!`. This module constructs its normalized square-root amplitudes and
negative arccos rotation angles, and proves that the actual unary cascade prepares
them. The parameter domain is `t > 0`; the zero-time circuit can be omitted.
The scalar tail estimate uses the public factorial-series theorem, for `t ≤ 1`.
Exact real angles are constructed here; finite-bit synthesis and loading the
term-index state remain separate obligations.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open Qatlib.Papers.TruncTaylor14.PrepareSelectAmplitude
open Qatlib.Papers.TruncTaylor14.PrepareSelectCount
open Qatlib.Papers.TruncTaylor14.ResourceCount

namespace Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor

noncomputable section

/-- The scalar Taylor coefficient of order `k`, nonnegative when `0 ≤ t`. -/
def taylorWeight (t : ℝ) (k : ℕ) : ℝ := t ^ k / (k.factorial : ℝ)

/-- The finite tail from `n` through the truncation order `K`. -/
def taylorTail (t : ℝ) (K n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), if n ≤ k then taylorWeight t k else 0

/-- The normalization of the truncated Taylor order distribution. -/
def taylorMass (t : ℝ) (K : ℕ) : ℝ := taylorTail t K 0

/-- The desired normalized order-register amplitude. -/
def taylorAmplitude (t : ℝ) (K k : ℕ) : ℝ :=
  Real.sqrt (taylorWeight t k / taylorMass t K)

/-- The norm of the unallocated tail at a rotation step. -/
def taylorTailNorm (t : ℝ) (K n : ℕ) : ℝ :=
  Real.sqrt (taylorTail t K n / taylorMass t K)

/-- The explicit real rotation, with the sign convention of the physical cascade. -/
def taylorAngle (t : ℝ) (K n : ℕ) : ℝ :=
  -Real.arccos (taylorAmplitude t K n / taylorTailNorm t K n)

/-- Positive time makes every factorial coefficient strictly positive. -/
theorem taylorWeight_pos {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < taylorWeight t k := by
  unfold taylorWeight
  positivity

/-- Every finite tail is nonnegative for nonnegative time. -/
theorem taylorTail_nonneg {t : ℝ} (ht : 0 ≤ t) (K n : ℕ) :
    0 ≤ taylorTail t K n := by
  unfold taylorTail
  apply Finset.sum_nonneg
  intro k _
  simp only [taylorWeight]
  split_ifs <;> positivity

/-- A nonempty finite tail contains its first positive coefficient. -/
theorem taylorTail_pos {t : ℝ} (ht : 0 < t) {K n : ℕ} (hn : n ≤ K) :
    0 < taylorTail t K n := by
  have hle : taylorWeight t n ≤ taylorTail t K n := by
    have h := Finset.single_le_sum
      (s := Finset.range (K + 1))
      (f := fun k => if n ≤ k then taylorWeight t k else 0)
      (fun k _ => by simp only [taylorWeight]; split_ifs <;> positivity)
      (Finset.mem_range.mpr (by omega : n < K + 1))
    simpa [taylorTail] using! h
  exact (taylorWeight_pos ht n).trans_le hle

/-- Splitting off one coefficient leaves the next finite tail. -/
theorem taylorTail_split (t : ℝ) {K n : ℕ} (hn : n ≤ K) :
    taylorTail t K n = taylorWeight t n + taylorTail t K (n + 1) := by
  unfold taylorTail
  have heq :
      (∑ k ∈ Finset.range (K + 1), if n ≤ k then taylorWeight t k else 0) =
        ∑ k ∈ Finset.range (K + 1),
          ((if k = n then taylorWeight t n else 0) +
            (if n + 1 ≤ k then taylorWeight t k else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkn : k = n
    · subst k
      simp
    · by_cases hlt : k < n
      · simp [Nat.not_le.mpr hlt, show ¬ n + 1 ≤ k by omega, hkn]
      · simp [show n ≤ k by omega, show n + 1 ≤ k by omega, hkn]
  rw [heq, Finset.sum_add_distrib]
  simp [Finset.mem_range.mpr (by omega : n < K + 1)]

/-- At the final order the finite tail is exactly the final coefficient. -/
theorem taylorTail_last (t : ℝ) (K : ℕ) :
    taylorTail t K K = taylorWeight t K := by
  unfold taylorTail
  rw [Finset.sum_eq_single K]
  · simp
  · intro k hk hne
    have hk' := Finset.mem_range.mp hk
    simp [show ¬ K ≤ k by omega]
  · simp

/-- The normalized tail starts at unit norm. -/
theorem taylorTailNorm_zero {t : ℝ} (ht : 0 < t) (K : ℕ) :
    taylorTailNorm t K 0 = 1 := by
  have hm : taylorMass t K ≠ 0 := ne_of_gt (taylorTail_pos ht (Nat.zero_le K))
  change Real.sqrt (taylorMass t K / taylorMass t K) = 1
  rw [div_self hm, Real.sqrt_one]

/-- The final tail norm is the desired final amplitude. -/
theorem taylorTailNorm_last (t : ℝ) (K : ℕ) :
    taylorTailNorm t K K = taylorAmplitude t K K := by
  simp only [taylorTailNorm, taylorTail_last, taylorAmplitude]

/-- The squared normalized tail splits into the emitted amplitude and remaining tail. -/
theorem taylor_norm_split {t : ℝ} (ht : 0 < t) {K n : ℕ} (hn : n ≤ K) :
    taylorTailNorm t K n ^ 2 =
      taylorAmplitude t K n ^ 2 + taylorTailNorm t K (n + 1) ^ 2 := by
  have hm : 0 < taylorMass t K := taylorTail_pos ht (Nat.zero_le K)
  rw [taylorTailNorm, taylorAmplitude, taylorTailNorm,
    Real.sq_sqrt (div_nonneg (taylorTail_nonneg ht.le K n) hm.le),
    Real.sq_sqrt (div_nonneg (taylorWeight_pos ht n).le hm.le),
    Real.sq_sqrt (div_nonneg (taylorTail_nonneg ht.le K (n + 1)) hm.le),
    taylorTail_split t hn, add_div]

/-- Negative arccos realizes a nonnegative two-component split of a positive norm. -/
theorem negative_arccos_split {a r s : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hs : 0 ≤ s) (h : r ^ 2 = a ^ 2 + s ^ 2) :
    Real.cos (-Real.arccos (a / r)) * r = a ∧
      -Real.sin (-Real.arccos (a / r)) * r = s := by
  have har : a ≤ r := (sq_le_sq₀ ha hr.le).mp (by nlinarith [sq_nonneg s])
  have hc0 : 0 ≤ a / r := div_nonneg ha hr.le
  have hc1 : a / r ≤ 1 := (div_le_one hr).mpr har
  have hc2 : (a / r) ^ 2 ≤ 1 := pow_le_one₀ hc0 hc1
  constructor
  · rw [Real.cos_neg, Real.cos_arccos (by linarith) hc1]
    exact div_mul_cancel₀ a hr.ne'
  · rw [Real.sin_neg, neg_neg, Real.sin_arccos]
    have hx : 0 ≤ Real.sqrt (1 - (a / r) ^ 2) := Real.sqrt_nonneg _
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - (a / r) ^ 2 by linarith)
    have hdiv : (a / r) * r = a := div_mul_cancel₀ a hr.ne'
    have hmul : (a / r) ^ 2 * r ^ 2 = a ^ 2 := by rw [← mul_pow, hdiv]
    have hprod : (Real.sqrt (1 - (a / r) ^ 2) * r) ^ 2 = s ^ 2 := by
      calc
        _ = (1 - (a / r) ^ 2) * r ^ 2 := by rw [mul_pow, hsq]
        _ = s ^ 2 := by nlinarith
    have hnonneg := mul_nonneg hx hr.le
    exact (sq_eq_sq₀ hnonneg hs).mp hprod

/-- The concrete Taylor angle obeys both physical splitting equations. -/
theorem taylorAngle_split {t : ℝ} (ht : 0 < t) {K n : ℕ} (hn : n ≤ K) :
    Real.cos (taylorAngle t K n) * taylorTailNorm t K n = taylorAmplitude t K n ∧
      -Real.sin (taylorAngle t K n) * taylorTailNorm t K n =
        taylorTailNorm t K (n + 1) := by
  have hm : 0 < taylorMass t K := taylorTail_pos ht (Nat.zero_le K)
  apply negative_arccos_split (Real.sqrt_nonneg _)
    (Real.sqrt_pos.2 (div_pos (taylorTail_pos ht hn) hm)) (Real.sqrt_nonneg _)
    (taylor_norm_split ht hn)

/-- The explicit Taylor-angle cascade emits the factorial square-root amplitudes. -/
theorem taylor_cascade_amplitudes {t : ℝ} (ht : 0 < t) (K : ℕ) :
    ∀ n, n ≤ K →
      cascadeTop (taylorAngle t K) n = taylorTailNorm t K n ∧
        ∀ k, k < n → cascadeAmplitude (taylorAngle t K) n k = taylorAmplitude t K k := by
  intro n
  induction n with
  | zero =>
      intro _
      constructor
      · simp [cascadeTop, cascadeAmplitude, taylorTailNorm_zero ht]
      · intro k hk; omega
  | succ n ih =>
      intro hn
      obtain ⟨htop, hprev⟩ := ih (by omega)
      obtain ⟨hcos, hsin⟩ := taylorAngle_split ht (by omega : n ≤ K)
      constructor
      · rw [cascadeTop_succ, htop]
        nlinarith
      · intro k hk
        by_cases hkn : k < n
        · rw [cascadeAmplitude_lt _ hkn]
          exact hprev k hkn
        · have hk' : k = n := by omega
          subst k
          rw [cascadeAmplitude_penultimate, htop]
          nlinarith

/-- The actual unary PREPARE word has the normalized factorial amplitude at every order. -/
theorem taylor_prepared_entry {t : ℝ} (ht : 0 < t) (K : ℕ) (k : Fin (K + 1)) :
    cascadePrepared K (fun i => taylorAngle t K i.val) (unaryReg K k) =
      (taylorAmplitude t K k.val : ℂ) := by
  rw [cascadePrepared_eq_unaryState_all, unaryState_entry]
  obtain ⟨htop, hprev⟩ := taylor_cascade_amplitudes ht K K (Nat.le_refl K)
  by_cases hk : k.val < K
  · rw [hprev k.val hk]
  · have hk' : k.val = K := by omega
    rw [hk']
    exact congrArg Complex.ofReal (htop.trans (taylorTailNorm_last t K))

/-- Born measurement of the actual order-register state gives the normalized
factorial weights, with the same explicit exact angles. -/
theorem taylor_prepared_born {t : ℝ} (ht : 0 < t) (K : ℕ) (k : Fin (K + 1)) :
    ‖cascadePrepared K (fun i => taylorAngle t K i.val) (unaryReg K k)‖ ^ 2 =
      taylorWeight t k.val / taylorMass t K := by
  rw [taylor_prepared_entry ht, taylorAmplitude, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (div_nonneg (taylorWeight_pos ht k.val).le
    (taylorTail_pos ht (Nat.zero_le K)).le)

/-- On a segment of strength at most one, the omitted factorial tail is summable
and bounded by twice its first omitted coefficient. -/
theorem taylor_remainder_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (K : ℕ) :
    Summable (fun j : ℕ => taylorWeight t (K + 1 + j)) ∧
      (∑' j : ℕ, taylorWeight t (K + 1 + j)) ≤ 2 * taylorWeight t (K + 1) := by
  simpa only [taylorWeight, mul_div_assoc] using
    Qatlib.Concepts.CoherentSim.FactorialTaylor.factorialTaylor_tail t K ht ht1

end

end Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor
