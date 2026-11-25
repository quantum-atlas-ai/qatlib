/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# BesselTruncation — Lemmas 8 and 11 of arXiv:1501.01715v3

Paper: Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal
dependence on all parameters*, arXiv:1501.01715v3 (2015-12-07).

* Lemma 8, p.10, eq.(43): with the coefficients `a_m` of eq.(42), for `|z| ≤ k`,
  `‖V_k − V_∞‖ = O((‖H‖/Xd)(z/2)^{k+1}/k!)`.  Its proof (Appendix, eq.(84)–(88))
  rests on the pointwise Bessel bound `|J_m(z)| ≤ (|z|/2)^{|m|}/|m|!` (eq.(84)) and the
  geometric tail estimate (85).  The repository already has `abs_lcBesselJ_le`
  (`|lcBesselJ k τ| ≤ (τ/2)^k/k!`) for the power-series Bessel function `lcBesselJ`.
* Lemma 11, p.12, eq.(51): `S(z) := ∑_{m∈ℤ} |J_m(z)|` is `O(√|z|)`.

The operator-level statements `V_k`/`V_∞` of Lemma 8 need the Szegedy quantum-walk
operator `U` and its eigenvalues `μ±` of eq.(7), which the repository does not provide;
the analytic core that the paper actually estimates (eq.(85)) is stated below.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamSimOptimal15.MainResults

open Qatlib.Concepts.QsvtCore.PhaseExistence

/-- Factorial absorption: for `k, m : ℕ`, `k^m * (k+1)! ≤ (k+m+1)!`.  The product
`∏_{i=1}^{m} (k+1+i)` is at least `(k+1)^m ≥ k^m`. -/
private theorem pow_mul_factorial_le (k m : ℕ) :
    (k : ℝ) ^ m * ((k + 1).factorial : ℝ) ≤ ((k + m + 1).factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hfac : ((k + (m + 1) + 1).factorial : ℝ)
          = ((k + (m + 1) + 1 : ℕ) : ℝ) * ((k + m + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring_nf
      calc (k : ℝ) ^ (m + 1) * ((k + 1).factorial : ℝ)
          = (k : ℝ) * ((k : ℝ) ^ m * ((k + 1).factorial : ℝ)) := by ring
        _ ≤ (k : ℝ) * ((k + m + 1).factorial : ℝ) := mul_le_mul_of_nonneg_left ih hk
        _ ≤ ((k + (m + 1) + 1 : ℕ) : ℝ) * ((k + m + 1).factorial : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            push_cast
            linarith
        _ = ((k + (m + 1) + 1).factorial : ℝ) := hfac.symm

/-- **Lemma 8, analytic core, arXiv:1501.01715v3 p.10, eq.(84)–(85)**: for `0 ≤ z ≤ k`
the tail of the Bessel series beyond order `k` is bounded by
`2·(|z|/2)^{k+1}/(k+1)!`, which is the estimate the paper combines with Stirling's
formula to obtain eq.(43).

(`|J_m(−z)| = |J_m(z)|` extends the statement to negative `z`; this is not needed for
the `|z| ≤ k` use in Theorem 3, where `z = −1/2`.)

Proof.  `abs_lcBesselJ_le` bounds the `m`-th tail term by
`(z/2)^{m+k+1}/(m+k+1)!`.  Factoring out `(z/2)^{k+1}/(k+1)!` leaves the ratio
`(z/2)^m·(k+1)!/(k+m+1)!`, which is at most `2^{-m}` because `z ≤ k` and
`(k+m+1)!/(k+1)! = ∏_{i=1}^{m}(k+1+i) ≥ (k+1)^m`.  Summing the geometric series of
ratio `1/2` closes the estimate. -/
theorem lemma8_bessel_tail (k : ℕ) (z : ℝ) (h0 : 0 ≤ z) (hk : z ≤ (k : ℝ)) :
    (∑' m : ℕ, |lcBesselJ (m + k + 1) z|) ≤
      2 * ((z / 2) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  have hfacpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ (z / 2) ^ (k + 1) := by positivity
  -- factorial absorption at the paper's hypothesis `z ≤ k`
  have hzpow : ∀ m : ℕ, z ^ m * ((k + 1).factorial : ℝ) ≤
      ((k + m + 1).factorial : ℝ) := by
    intro m
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hk m)
      (le_of_lt hfacpos)).trans ?_
    exact pow_mul_factorial_le k m
  have hkey : ∀ m : ℕ, (z / 2) ^ m * ((k + 1).factorial : ℝ) ≤
      (1 / 2 : ℝ) ^ m * ((k + m + 1).factorial : ℝ) := by
    intro m
    have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hz := hzpow m
    have hL : (z / 2) ^ m = z ^ m / 2 ^ m := by rw [div_pow]
    have hR : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
    have eL : (z ^ m / 2 ^ m) * ((k + 1).factorial : ℝ)
        = (z ^ m * ((k + 1).factorial : ℝ)) / 2 ^ m := by
      rw [div_mul_eq_mul_div]
    have eR : (1 / 2 ^ m) * ((k + m + 1).factorial : ℝ)
        = ((k + m + 1).factorial : ℝ) / 2 ^ m := by
      rw [one_div_mul_eq_div]
    rw [hL, hR, eL, eR]
    exact (div_le_div_iff_of_pos_right h2).mpr hz
  -- termwise comparison with `(z/2)^{k+1}/(k+1)! · 2^{-m}`
  have hterm : ∀ m : ℕ, |lcBesselJ (m + k + 1) z| ≤
      ((z / 2) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (1 / 2) ^ m := by
    intro m
    have h1 := abs_lcBesselJ_le (k + m + 1) z h0
    have hidx : m + k + 1 = k + m + 1 := by omega
    rw [hidx]
    refine h1.trans ?_
    have e3 : (z / 2) ^ (k + m + 1) = (z / 2) ^ (k + 1) * (z / 2) ^ m := by
      rw [← pow_add]
      congr 1
      omega
    have e4 : ((z / 2) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (1 / 2) ^ m
        = (z / 2) ^ (k + 1) * ((1 / 2) ^ m / ((k + 1).factorial : ℝ)) := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
    have hF : (0 : ℝ) < ((k + m + 1).factorial : ℝ) := by positivity
    rw [e3, e4, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hpow
    exact (div_le_div_iff₀ hF hfacpos).mpr (hkey m)
  -- summability of the majorant and of the tail
  have hgeom : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmajor : Summable (fun m : ℕ =>
      ((z / 2) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (1 / 2) ^ m) :=
    hgeom.mul_left _
  have htail : Summable (fun m : ℕ => |lcBesselJ (m + k + 1) z|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm hmajor
  refine (htail.tsum_le_tsum hterm hmajor).trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1),
    show (1 - 1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  ring

/-- **Statement only.** The absolute Bessel sum
`S(z) = ∑_{m∈ℤ} |J_m(z)|` grows at most as `√z` for `z ≥ 1`
([BerryChildsKothari2015], Lemma 11, Eq. (51)). The source proof uses square-sum
normalization and the Bessel recurrence to control the central band and tail. -/
def besselSumSqrtGrowthStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
    (∑' m : ℤ, |lcBesselJ m.natAbs z|) ≤ C * Real.sqrt z

end Qatlib.Papers.HamSimOptimal15.MainResults
