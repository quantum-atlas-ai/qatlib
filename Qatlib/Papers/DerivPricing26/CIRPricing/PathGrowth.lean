/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CIRPricing.PathGrowth

Source: Herman, Sun, Liu, Pistoia, Che, Otter, Chakrabarti, Harrow,
*Quantum Speedups for Derivative Pricing Beyond Black-Scholes*,
fixed version arXiv:2602.03725v1, Appendix C.2, Lemma C.1
(v1 text, line 4777 of the extracted source):

> Let `X_t` follow a CIR process with `γ + γ² < 1`. Then any point `x_t` on a
> realized path satisfies `x_t ≤ x_0 + c (1 + γ)^t Σ_{k=0}^t (y_k + z_k²)`,
> where `γ := sqrt (c β) < 1`.

The paper proves it by normalising `v_t := x_t / c`, so that the CIR step reads
`sqrt (v_t) = y_t + (z_t + γ sqrt (v_{t-1}))²`. Only the displayed *numerical*
recursion is used after that: Jensen's inequality gives the one-step estimate
`v_t ≤ y_t + (1 + γ) z_t² + (γ + γ²) v_{t-1}`, and an induction on `t` with
geometric weights produces the bound.

This module formalises exactly those two steps over `ℝ`, with no CIR measure
theory: the AM-GM step that yields the recursion (`cir_one_step`), the
geometric-weight induction (`cir_geometric_bound`), and the paper's displayed
final bound (`cir_path_bound`).

Boundary: only the recursion `sqrt v_t = y_t + (z_t + γ sqrt v_{t-1})²` and the
numerical consequence are covered. The identification of `x_t` with a realised
CIR path, the meaning of `y_k`, `z_k` and `c β` as CIR coefficients, the
Feller/non-central-χ² transition decomposition, and any probabilistic statement
about the path are *not* formalised here. The hypotheses `0 ≤ y k` and
`0 ≤ x0` are the sign facts that hold for the CIR increments and the initial
variance.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DerivPricing26.CIRPricing.PathGrowth

open Finset
open scoped BigOperators

/-- Lemma C.1, Jensen step in the paper's proof: with `γ ≥ 0` and `v ≥ 0`,
`(z + γ sqrt v)² ≤ (1 + γ) z² + (γ + γ²) v`. This is the displayed
`v_t ≤ y_t + (1 + γ) z_t² + (γ + γ²) v_{t-1}` after moving `y_t` to the left. -/
theorem cir_one_step {γ z v : ℝ} (hγ : 0 ≤ γ) (hv : 0 ≤ v) :
    (z + γ * Real.sqrt v) ^ 2 ≤ (1 + γ) * z ^ 2 + (γ + γ ^ 2) * v := by
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  nlinarith [sq_nonneg (z - Real.sqrt v), sq_nonneg (z + Real.sqrt v), hγ, Real.sqrt_nonneg v]

/-- Lemma C.1, geometric-weight induction: if the normalised path obeys
`v_t ≤ y_t + (1 + γ) z_t² + (γ + γ²) v_{t-1}` with `0 ≤ γ`, then
`v_t ≤ (γ + γ²)^t v_0 + Σ_{k=1}^t (γ + γ²)^{t-k} (y_k + (1 + γ) z_k²)`.
This is the intermediate display in the paper's proof; the paper additionally
assumes `γ + γ² < 1`, which this finite-`t` identity does not need. -/
theorem cir_geometric_bound {γ : ℝ} (hγ : 0 ≤ γ) {v y z : ℕ → ℝ}
    (hrec : ∀ n : ℕ, v (n + 1) ≤ y (n + 1) + (1 + γ) * z (n + 1) ^ 2 + (γ + γ ^ 2) * v n) :
    ∀ n : ℕ, v n ≤ (γ + γ ^ 2) ^ n * v 0 +
      ∑ k ∈ Icc 1 n, (γ + γ ^ 2) ^ (n - k) * (y k + (1 + γ) * z k ^ 2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hρ : 0 ≤ γ + γ ^ 2 := by nlinarith
    set S := ∑ k ∈ Icc 1 n, (γ + γ ^ 2) ^ (n - k) * (y k + (1 + γ) * z k ^ 2) with hSdef
    have hstep : v (n + 1) ≤ y (n + 1) + (1 + γ) * z (n + 1) ^ 2 +
        (γ + γ ^ 2) * ((γ + γ ^ 2) ^ n * v 0 + S) := by
      rw [mul_add]
      have h := mul_le_mul_of_nonneg_left ih hρ
      have h' := hrec n
      linarith
    refine le_trans hstep ?_
    have hsum : (γ + γ ^ 2) * S
        = ∑ k ∈ Icc 1 n, (γ + γ ^ 2) ^ (n + 1 - k) * (y k + (1 + γ) * z k ^ 2) := by
      rw [hSdef, mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
      have hk' : n + 1 - k = (n - k) + 1 := by omega
      rw [hk', pow_succ]
      ring
    have hpow : (γ + γ ^ 2) ^ (n + 1) = (γ + γ ^ 2) * (γ + γ ^ 2) ^ n := by
      rw [pow_succ, mul_comm]
    have hzero : n + 1 - (n + 1) = 0 := by omega
    rw [sum_Icc_succ_top (a := 1) (b := n) (by omega)
      (fun k => (γ + γ ^ 2) ^ (n + 1 - k) * (y k + (1 + γ) * z k ^ 2)), ← hsum,
      hzero, pow_zero, one_mul]
    have hA : y (n + 1) + (1 + γ) * z (n + 1) ^ 2 +
          (γ + γ ^ 2) * ((γ + γ ^ 2) ^ n * v 0 + S)
        = (γ + γ ^ 2) ^ (n + 1) * v 0 +
          ((γ + γ ^ 2) * S + (y (n + 1) + (1 + γ) * z (n + 1) ^ 2)) := by
      rw [hpow]
      ring
    rw [hA]

/-- Lemma C.1, the paper's displayed conclusion: for `γ + γ² ≤ 1`, `c > 0`,
`x_t = c v_t` with `v_0 = x_0 / c`, nonnegative increments `y_k` and any
realised numeric path `z`, for every monitoring step `t ≥ 1`
`x_t ≤ x_0 + c (1 + γ)^t Σ_{k=0}^t (y_k + z_k²)`. -/
theorem cir_path_bound {γ c x0 : ℝ} (hγ : 0 ≤ γ) (hγγ : γ + γ ^ 2 ≤ 1) (hc : 0 < c)
    {v y z : ℕ → ℝ} (hv0 : v 0 = x0 / c) (hx0 : 0 ≤ x0) (hy : ∀ k : ℕ, 0 ≤ y k)
    (hrec : ∀ n : ℕ, v (n + 1) ≤ y (n + 1) + (1 + γ) * z (n + 1) ^ 2 + (γ + γ ^ 2) * v n)
    {n : ℕ} (hn : 1 ≤ n) :
    c * v n ≤ x0 + c * (1 + γ) ^ n * ∑ k ∈ range (n + 1), (y k + z k ^ 2) := by
  have hρ0 : 0 ≤ γ + γ ^ 2 := by nlinarith
  have hρ1 : γ + γ ^ 2 ≤ 1 := hγγ
  have hv0' : 0 ≤ v 0 := by rw [hv0]; positivity
  have hcv : c * v 0 = x0 := by rw [hv0]; field_simp
  have hcollapse : v n ≤ v 0 + ∑ k ∈ Icc 1 n, (y k + (1 + γ) * z k ^ 2) := by
    refine (cir_geometric_bound hγ hrec n).trans ?_
    have hleft : (γ + γ ^ 2) ^ n * v 0 ≤ v 0 := by
      have h := pow_le_one₀ (n := n) hρ0 hρ1
      nlinarith
    have hright : (∑ k ∈ Icc 1 n, (γ + γ ^ 2) ^ (n - k) * (y k + (1 + γ) * z k ^ 2))
        ≤ ∑ k ∈ Icc 1 n, (y k + (1 + γ) * z k ^ 2) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hw : (γ + γ ^ 2) ^ (n - k) ≤ 1 := pow_le_one₀ hρ0 hρ1
      have hterm : 0 ≤ y k + (1 + γ) * z k ^ 2 := by
        have hyk : 0 ≤ y k := hy k
        have hzk : 0 ≤ (1 + γ) * z k ^ 2 := by nlinarith [sq_nonneg (z k)]
        linarith
      calc (γ + γ ^ 2) ^ (n - k) * (y k + (1 + γ) * z k ^ 2)
          ≤ 1 * (y k + (1 + γ) * z k ^ 2) := mul_le_mul_of_nonneg_right hw hterm
        _ = y k + (1 + γ) * z k ^ 2 := by ring
    nlinarith
  have hgamma : ∑ k ∈ Icc 1 n, (y k + (1 + γ) * z k ^ 2)
      ≤ (1 + γ) * ∑ k ∈ Icc 1 n, (y k + z k ^ 2) := by
    rw [mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hyk : 0 ≤ y k := hy k
    have hz : 0 ≤ z k ^ 2 := sq_nonneg (z k)
    nlinarith
  have hsubset : ∑ k ∈ Icc 1 n, (y k + z k ^ 2) ≤ ∑ k ∈ range (n + 1), (y k + z k ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      simp only [Finset.mem_range]
      have h := (Finset.mem_Icc.mp hk).2
      omega
    · intro k _ _
      nlinarith [sq_nonneg (z k), hy k]
  have hpow : (1 + γ) ≤ (1 + γ) ^ n := by
    have h1 : 1 ≤ 1 + γ := by linarith
    simpa using pow_le_pow_right₀ h1 hn
  have hS : 0 ≤ ∑ k ∈ range (n + 1), (y k + z k ^ 2) := by
    refine Finset.sum_nonneg fun k _ => ?_
    nlinarith [sq_nonneg (z k), hy k]
  have hfinal : (1 + γ) * ∑ k ∈ Icc 1 n, (y k + z k ^ 2)
      ≤ (1 + γ) ^ n * ∑ k ∈ range (n + 1), (y k + z k ^ 2) := by
    have h1 : (1 + γ) * ∑ k ∈ Icc 1 n, (y k + z k ^ 2)
        ≤ (1 + γ) * ∑ k ∈ range (n + 1), (y k + z k ^ 2) := by
      have h0 : 0 ≤ 1 + γ := by linarith
      exact mul_le_mul_of_nonneg_left hsubset h0
    nlinarith [h1, hS, hpow]
  nlinarith [hcollapse, hgamma, hfinal, hcv, hc]

end Qatlib.Papers.DerivPricing26.CIRPricing.PathGrowth
