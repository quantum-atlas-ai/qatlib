/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux2

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11 of `QLinearODE17`: the transfer polynomial is `√1.04`-bounded

Source: arXiv:1701.03684v2, Appendix A, printed Lemma 11 (`lem:taylor2`).
For `k ≥ 5`, `0 ≤ b ≤ k`, `|z| ≤ 1` and `Re z ≤ 0`, the block transfer
polynomial `T_{b,k}(z) = b! ∑_{j=b}^{k} z^{j-b}/j!` satisfies
`|T_{b,k}(z)| ≤ √1.04`.

The printed proof splits on the position of `b` relative to `k` and uses the
sharp half-plane Taylor remainder of Lemma 10 in each piece:

* `b = 0`: `T_{0,k} = T_k`, so Lemma 10 gives `1 + 1/(k+1)! ≤ 1 + 1/720`.
* `b = k`: `T_{k,k} = 1`.
* `b = k - 1`: `T_{k-1,k}(z) = 1 + z/k`, and `Re z ≤ 0` cancels the linear
  term, so `|T_{k-1,k}(z)|² ≤ 1 + 1/k² ≤ 1.04`. This is the tight case, with
  equality at `k = 5`, `z = i`.
* `b ≤ k - 2`: the transfer bound `1 + b!/(k+1)!` of `taylorTransPoly_le`
  upgrades to `1 + 1/120`, because two factorial factors give
  `b!/(k+1)! ≤ 1/((k-1)k(k+1)) ≤ 1/120`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Qatlib.Papers.QLinearODE17.TaylorAnalysis

/-- `T_{k,k}(z) = 1`: the last block transfer polynomial keeps only the term
`k!/k! z^0`. -/
theorem taylorTransPoly_self (k : ℕ) (z : ℂ) : taylorTransPoly k k z = 1 := by
  have hset : Finset.Icc k k = {k} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_singleton]
    omega
  have hk : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [taylorTransPoly, hset, Finset.sum_singleton, Nat.sub_self, pow_zero, mul_one]
  exact div_self hk

/-- `T_{k-1,k}(z) = 1 + z/k`: the second to last transfer polynomial keeps only
two terms. -/
theorem taylorTransPoly_pred {k : ℕ} (hk : 1 ≤ k) (z : ℂ) :
    taylorTransPoly k (k - 1) z = 1 + z / (k : ℂ) := by
  have hset : Finset.Icc (k - 1) k = insert (k - 1) {k} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hk1 : (k - 1) + 1 = k := by omega
  have hfac : ((Nat.factorial k : ℕ) : ℂ) = (k : ℂ) * ((Nat.factorial (k - 1) : ℕ) : ℂ) := by
    have hsucc := Nat.factorial_succ (k - 1)
    rw [hk1] at hsucc
    rw [hsucc]
    push_cast
    ring
  have hfk : ((Nat.factorial (k - 1) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))
  have hpow0 : z ^ (k - 1 - (k - 1)) = 1 := by rw [Nat.sub_self, pow_zero]
  have hpow1 : z ^ (k - (k - 1)) = z := by
    rw [show k - (k - 1) = 1 from by omega, pow_one]
  rw [taylorTransPoly, hset, Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      omega), Finset.sum_singleton, hpow0, hpow1, mul_one, div_self hfk, hfac]
  have hk0 : (k : ℂ) ≠ 0 := by
    have hknz : k ≠ 0 := by omega
    exact Nat.cast_ne_zero.mpr hknz
  field_simp

/-- Squared stability of `1 + w` on the closed left half-plane:
`|1 + w|² = 1 + 2 Re w + |w|² ≤ 1 + |w|²`. -/
theorem norm_one_add_sq_le {w : ℂ} (hw : w.re ≤ 0) :
    ‖1 + w‖ * ‖1 + w‖ ≤ 1 + ‖w‖ * ‖w‖ := by
  have h1 : ‖1 + w‖ * ‖1 + w‖ = (1 + w.re) * (1 + w.re) + w.im * w.im := by
    rw [← pow_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
  have h2 : ‖w‖ * ‖w‖ = w.re * w.re + w.im * w.im := by
    rw [← pow_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [h1, h2]
  nlinarith

/-- The real part of `z / k` for a positive natural `k` stays nonpositive. -/
theorem div_natCast_re_le {k : ℕ} (hk : 0 < k) {z : ℂ} (hre : z.re ≤ 0) :
    (z / ((k : ℕ) : ℂ)).re ≤ 0 := by
  rw [show ((k : ℕ) : ℂ) = (((k : ℝ)) : ℂ) from by simp, Complex.div_ofReal_re]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact div_nonpos_of_nonpos_of_nonneg hre hkpos.le

/-- A nonnegative real bounded by `c` has its square bounded by `c²`. -/
theorem mul_self_le_mul_self_of_le {X c : ℝ} (hX : 0 ≤ X) (h : X ≤ c) :
    X * X ≤ c * c :=
  mul_le_mul h h hX (le_trans hX h)

/-- Printed Lemma 11: for `k ≥ 5`, `0 ≤ b ≤ k`, `|z| ≤ 1` and `Re z ≤ 0`, the
block transfer polynomial `T_{b,k}(z) = b! ∑_{j=b}^{k} z^{j-b}/j!` satisfies
`|T_{b,k}(z)| ≤ √1.04`. -/
theorem taylorTransPoly_norm_le_sqrt_1_04 {k b : ℕ} (hk : 5 ≤ k) (hbk : b ≤ k)
    (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorTransPoly k b z‖ ≤ Real.sqrt 1.04 := by
  have h104 : (0 : ℝ) ≤ 1.04 := by norm_num
  have hk1 : 1 ≤ k := by omega
  by_cases hb0 : b = 0
  · subst hb0
    rw [taylorTransPoly_zero]
    have hbound := taylorPoly_le k z h1 hre
    have h720 : (720 : ℝ) ≤ ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
      have h6 : 6 ≤ k + 1 := by omega
      have hle := Nat.factorial_le h6
      have h720' : Nat.factorial 6 = 720 := by decide
      rw [h720'] at hle
      exact_mod_cast hle
    have hF : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) := by positivity
    have hinv : 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) ≤ 1 / 720 := by
      rw [div_le_div_iff₀ hF (by norm_num)]
      linarith
    have hlim : ‖taylorPoly k z‖ ≤ 1 + 1 / 720 := le_trans hbound (by linarith)
    have hT : ‖taylorPoly k z‖ ^ 2 ≤ 1.04 := by
      rw [pow_two]
      have hsq := mul_self_le_mul_self_of_le (norm_nonneg (taylorPoly k z)) hlim
      have hc : (1 + 1 / 720 : ℝ) * (1 + 1 / 720) ≤ 1.04 := by norm_num
      linarith
    exact (Real.le_sqrt (norm_nonneg _) h104).mpr hT
  by_cases hbk' : b = k
  · subst hbk'
    rw [taylorTransPoly_self, norm_one]
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) h104).mpr (by norm_num)
  by_cases hbk1 : b = k - 1
  · subst hbk1
    rw [taylorTransPoly_pred hk1]
    have hw : (z / ((k : ℕ) : ℂ)).re ≤ 0 := div_natCast_re_le (by omega) hre
    have hstep := norm_one_add_sq_le hw
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hwn : ‖z / ((k : ℕ) : ℂ)‖ ≤ 1 / (k : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right h1 hkR.le
    have hk5 : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hw2 : ‖z / ((k : ℕ) : ℂ)‖ * ‖z / ((k : ℕ) : ℂ)‖ ≤ (1 / 5 : ℝ) * (1 / 5) := by
      have hlim : ‖z / ((k : ℕ) : ℂ)‖ ≤ 1 / 5 := by
        apply le_trans hwn
        rw [div_le_div_iff₀ hkR (by norm_num)]
        linarith
      exact mul_self_le_mul_self_of_le (norm_nonneg _) hlim
    have hT : ‖1 + z / ((k : ℕ) : ℂ)‖ ^ 2 ≤ 1.04 := by
      rw [pow_two]
      have hc : 1 + (1 / 5 : ℝ) * (1 / 5) ≤ 1.04 := by norm_num
      linarith
    exact (Real.le_sqrt (norm_nonneg _) h104).mpr hT
  · have hb1 : 1 ≤ b := by omega
    have hb2 : b ≤ k - 2 := by omega
    have hbound := taylorTransPoly_le hb1 hbk z h1 hre
    have hstep : Nat.factorial (k + 1) = (k - 1) * k * (k + 1) * Nat.factorial (k - 2) := by
      have h1' : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
      have h2' : Nat.factorial k = k * Nat.factorial (k - 1) := by
        have hsucc := Nat.factorial_succ (k - 1)
        rw [show k - 1 + 1 = k from by omega] at hsucc
        exact hsucc
      have h3' : Nat.factorial (k - 1) = (k - 1) * Nat.factorial (k - 2) := by
        have hsucc := Nat.factorial_succ (k - 2)
        rw [show k - 2 + 1 = k - 1 from by omega] at hsucc
        exact hsucc
      rw [h1', h2', h3']
      ring
    have h120 : 120 ≤ (k - 1) * k * (k + 1) := by
      have h4 : 4 ≤ k - 1 := by omega
      have h5 : 5 ≤ k := hk
      have h6 : 6 ≤ k + 1 := by omega
      calc 120 = 4 * 5 * 6 := by norm_num
        _ ≤ (k - 1) * k * (k + 1) := Nat.mul_le_mul (Nat.mul_le_mul h4 h5) h6
    have hkey : 120 * Nat.factorial b ≤ Nat.factorial (k + 1) := by
      rw [hstep]
      calc 120 * Nat.factorial b ≤ ((k - 1) * k * (k + 1)) * Nat.factorial (k - 2) :=
            Nat.mul_le_mul h120 (Nat.factorial_le hb2)
        _ = (k - 1) * k * (k + 1) * Nat.factorial (k - 2) := by ring
    have hkeyR : (120 : ℝ) * ((Nat.factorial b : ℕ) : ℝ) ≤
        ((Nat.factorial (k + 1) : ℕ) : ℝ) := by exact_mod_cast hkey
    have hF : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) := by positivity
    have hratio : ((Nat.factorial b : ℕ) : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) ≤
        1 / 120 := by
      rw [div_le_iff₀ hF]
      linarith
    have hlim : ‖taylorTransPoly k b z‖ ≤ 1 + 1 / 120 := le_trans hbound (by linarith)
    have hT : ‖taylorTransPoly k b z‖ ^ 2 ≤ 1.04 := by
      rw [pow_two]
      have hsq := mul_self_le_mul_self_of_le (norm_nonneg (taylorTransPoly k b z)) hlim
      have hc : (1 + 1 / 120 : ℝ) * (1 + 1 / 120) ≤ 1.04 := by norm_num
      linarith
    exact (Real.le_sqrt (norm_nonneg _) h104).mpr hT

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
