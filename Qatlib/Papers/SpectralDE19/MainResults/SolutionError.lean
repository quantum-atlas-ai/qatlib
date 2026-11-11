/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Solution error of the quantum spectral ODE method

Fixed source: arXiv:1901.00961, *Quantum spectral methods for differential
equations*, Lemma 3 (§4, p. 9, eq. (4.1)), proof pp. 9–10, eqs. (4.2)–(4.16).

The paper divides `[0,T]` into `m` subintervals `[Γ_h, Γ_{h+1}]`, rescales each
to `[-1,1]` and solves the Chebyshev collocation system on every subinterval.
Writing `Δ_h := ‖x̂(Γ_h) − x(Γ_h)‖` for the error at the left endpoint of the
`h`-th subinterval, Lemma 2 (the Chebyshev interpolation error bound, eq. (2.12))
gives, for a suitable `n`,

* `Δ_1 ≤ K (e/(2n))^n` (eq. (4.7)), and
* the recurrence `Δ_{h+1} ≤ (1 + K/‖γ‖ (e/(2n))^n) Δ_h + K (e/(2n))^n`
  (eq. (4.13)), where `K := max_t ‖x̂^{(n+1)}(t)‖`.

Choosing `n` so that `K/‖γ‖ (e/(2n))^n ≤ 1/(m+1)` (eq. (4.4)/(4.14)) turns the
recurrence into `Δ_{h+1} ≤ (1+1/m) Δ_h + B` with `B := K (e/(2n))^n`, and
iterating (eqs. (4.15)–(4.16)) gives the paper's bound (4.1)

  `‖x̂(T) − x(T)‖ ≤ m · max_t ‖x̂^{(n+1)}(t)‖ · e^{n+1}/(2n)^n`.

This file formalises exactly that iteration.  The two displayed *analytic*
inputs — the choice of `n` from (4.2)–(4.4) and the per-subinterval estimate of
Lemma 2 — are not re-derived here; they enter as the hypotheses `hbase` and
`hstep` in the shape in which the paper uses them.  Everything from (4.13) to
(4.16), including the constant `e`, is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralDE19.MainResults

open scoped BigOperators

/-- The elementary estimate `(1 + 1/m)^m ≤ e` used at eq. (4.15) of the paper
(`(1+1/m)^{m-1} ≤ (1+1/m)^m ≤ e`). -/
theorem one_add_one_div_pow_le_exp (m : ℕ) (hm : 1 ≤ m) :
    (1 + (1 : ℝ) / (m : ℝ)) ^ m ≤ Real.exp 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hstep : (1 : ℝ) + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (m : ℝ))
  have hnonneg : (0 : ℝ) ≤ 1 + 1 / (m : ℝ) := by positivity
  have hpow : (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / (m : ℝ))) ^ m :=
    pow_le_pow_left₀ hnonneg hstep m
  have hexp : (Real.exp (1 / (m : ℝ))) ^ m = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    have h : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    rw [h]
  calc (1 + 1 / (m : ℝ)) ^ m
      ≤ (Real.exp (1 / (m : ℝ))) ^ m := hpow
    _ = Real.exp 1 := hexp

/-- **SpectralDE19, Lemma 3 (iteration (4.14)–(4.16)).**  Error accumulation
over the `m` subintervals: if the initial error is at most `bound` and each
subinterval transports it with the paper's factor `1 + 1/m` and adds at most
`bound`, then the final error is at most `m · bound · e`.

`bound` is the paper's `B = max_t ‖x̂^{(n+1)}(t)‖ (e/(2n))^n`. -/
theorem lemma3_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (m n : ℕ) (hm : 1 ≤ m)
    (xhat x : ℕ → E) (bound : ℝ) (hbound : 0 ≤ bound)
    (hstep : ∀ h : ℕ, 1 ≤ h → h < m →
      ‖xhat (h + 1) - x (h + 1)‖ ≤
        (1 + (1 : ℝ) / (m : ℝ)) * ‖xhat h - x h‖ + bound)
    (hbase : ‖xhat 1 - x 1‖ ≤ bound) :
    ‖xhat m - x m‖ ≤ (m : ℝ) * bound * Real.exp 1 := by
  classical
  set c : ℝ := 1 + (1 : ℝ) / (m : ℝ) with hc_def
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by positivity
    rw [hc_def]; linarith
  have hc0 : 0 ≤ c := le_trans zero_le_one hc1
  -- Iterated bound: `Δ_h ≤ c^h · h · bound`.
  have hmain : ∀ h : ℕ, 1 ≤ h → h ≤ m →
      ‖xhat h - x h‖ ≤ c ^ h * ((h : ℝ) * bound) := by
    intro h hh1
    refine Nat.le_induction
      (P := fun h _ => h ≤ m → ‖xhat h - x h‖ ≤ c ^ h * ((h : ℝ) * bound)) ?base ?step h hh1
    · -- `h = 1`
      intro _
      have h1 : ‖xhat 1 - x 1‖ ≤ c ^ 1 * ((1 : ℕ) : ℝ) * bound := by
        have hcB : bound ≤ c * bound := by nlinarith [hbound, hc1]
        calc ‖xhat 1 - x 1‖ ≤ bound := hbase
          _ ≤ c * bound := hcB
          _ = c ^ 1 * ((1 : ℕ) : ℝ) * bound := by norm_num
      simpa using h1
    · -- step `h → h + 1`
      intro k hk ih hkm1
      have hkm : k < m := by omega
      have ihk := ih (by omega)
      have hstepk : ‖xhat (k + 1) - x (k + 1)‖ ≤ c * ‖xhat k - x k‖ + bound := by
        have := hstep k hk hkm
        simpa [hc_def] using this
      have hB : bound ≤ c ^ (k + 1) * bound := by
        have hge : (1 : ℝ) ≤ c ^ (k + 1) := one_le_pow₀ hc1
        nlinarith [hbound]
      have hmul : c * (c ^ k * ((k : ℝ) * bound)) = c ^ (k + 1) * ((k : ℝ) * bound) := by
        rw [pow_succ']
        ring
      calc ‖xhat (k + 1) - x (k + 1)‖
          ≤ c * ‖xhat k - x k‖ + bound := hstepk
        _ ≤ c * (c ^ k * ((k : ℝ) * bound)) + bound := by
              gcongr
        _ = c ^ (k + 1) * ((k : ℝ) * bound) + bound := by rw [hmul]
        _ ≤ c ^ (k + 1) * ((k : ℝ) * bound) + c ^ (k + 1) * bound := by gcongr
        _ = c ^ (k + 1) * (((k + 1 : ℕ) : ℝ) * bound) := by push_cast; ring
  have hm_le : ‖xhat m - x m‖ ≤ c ^ m * ((m : ℝ) * bound) := hmain m hm le_rfl
  have hc_exp : c ^ m ≤ Real.exp 1 := by
    simpa [hc_def] using one_add_one_div_pow_le_exp m hm
  have hprod : (0 : ℝ) ≤ (m : ℝ) * bound := by positivity
  calc ‖xhat m - x m‖ ≤ c ^ m * ((m : ℝ) * bound) := hm_le
    _ ≤ Real.exp 1 * ((m : ℝ) * bound) := by gcongr
    _ = (m : ℝ) * bound * Real.exp 1 := by ring

/-- **SpectralDE19, Lemma 3, eq. (4.1) with the paper's explicit constant.**
With `B = K · (e/(2n))^n` the abstract conclusion reads
`‖x̂(T) − x(T)‖ ≤ m · K · e^{n+1}/(2n)^n`. -/
theorem lemma3_error_bound_explicit
    {E : Type*} [NormedAddCommGroup E]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (xhat x : ℕ → E) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ h : ℕ, 1 ≤ h → h < m →
      ‖xhat (h + 1) - x (h + 1)‖ ≤
        (1 + (1 : ℝ) / (m : ℝ)) * ‖xhat h - x h‖
          + K * (Real.exp 1 / (2 * (n : ℝ))) ^ n)
    (hbase : ‖xhat 1 - x 1‖ ≤ K * (Real.exp 1 / (2 * (n : ℝ))) ^ n) :
    ‖xhat m - x m‖ ≤ (m : ℝ) * K * (Real.exp 1) ^ (n + 1) / (2 * (n : ℝ)) ^ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hbase' : 0 ≤ (Real.exp 1 / (2 * (n : ℝ))) ^ n := by positivity
  have hbound : 0 ≤ K * (Real.exp 1 / (2 * (n : ℝ))) ^ n := by positivity
  have hmain := lemma3_error_bound m n hm xhat x
    (K * (Real.exp 1 / (2 * (n : ℝ))) ^ n) hbound hstep hbase
  -- `(m) · (K·(e/2n)^n) · e = m · K · e^{n+1}/(2n)^n`
  calc ‖xhat m - x m‖
      ≤ (m : ℝ) * (K * (Real.exp 1 / (2 * (n : ℝ))) ^ n) * Real.exp 1 := hmain
    _ = (m : ℝ) * K * (Real.exp 1) ^ (n + 1) / (2 * (n : ℝ)) ^ n := by
          rw [div_pow, pow_succ]
          field_simp

end Qatlib.Papers.SpectralDE19.MainResults
