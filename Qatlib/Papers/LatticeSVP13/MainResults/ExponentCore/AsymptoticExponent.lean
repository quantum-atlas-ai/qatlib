/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic exponent vocabulary for LatticeSVP13

Laarhoven--Mosca--van de Pol, *Solving the Shortest Vector Problem in Lattices
Faster Using Quantum Search*, fixed arXiv:1301.6176v1 (25 Jan 2013).

The paper reports every complexity as a leading exponential term
`2 ^ (c * n + o(n))` and then records the leading coefficient `c`.  This file
gives the exact meaning of "the logarithm (base two) of a cost is `c * n + o(n)`"
and the closure properties used in Appendices A and B: adding exponents,
rescaling by a nonnegative factor, taking a maximum (needed for the space
`O(|S| + |C|)` bound), and taking base-two logarithms of products with square
roots (`O(|S| · √|C|)`).  It also records a Taylor-series tool for proving the
concrete numerical logarithms that appear in Theorems 1 and 2.

`HasLog2Exponent f c` is *not* a weakening and adds no hypotheses: it is a
definition of the paper's own `2 ^ (c * n + o(n))` representation for the
logarithm of a cost, on the index `n` ranging over `ℕ`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

open Asymptotics Filter

/-- The pointwise maximum of two `o(n)` functions (on `ℕ`) is again `o(n)`.

Proof: for `ε > 0`, eventually `|g n| ≤ (ε/2) n` and `|k n| ≤ (ε/2) n`, so
`|max (g n) (k n)| ≤ |g n| + |k n| ≤ ε n`. -/
theorem isLittleO_nat_max {g k : ℕ → ℝ}
    (hg : g =o[atTop] (fun n : ℕ => (n : ℝ)))
    (hk : k =o[atTop] (fun n : ℕ => (n : ℝ))) :
    (fun n => max (g n) (k n)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  rw [isLittleO_iff] at hg hk ⊢
  intro c hc
  have hc2 : 0 < c / 2 := by linarith
  filter_upwards [hg (c := c / 2) hc2, hk (c := c / 2) hc2] with n hgn hkn
  have hgn' : |g n| ≤ (c / 2) * (n : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hgn
  have hkn' : |k n| ≤ (c / 2) * (n : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hkn
  have hmax : |max (g n) (k n)| ≤ |g n| + |k n| := by
    rcases le_total (g n) (k n) with hle | hle
    · rw [max_eq_right hle]; exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [max_eq_left hle]; exact le_add_of_nonneg_right (abs_nonneg _)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn]
  nlinarith [hmax, hgn', hkn', abs_nonneg (g n), abs_nonneg (k n)]

/-- A constant function on `ℕ` is `o(n)` as `n → ∞`. -/
theorem isLittleO_nat_const (a : ℝ) :
    (fun _ : ℕ => a) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (|a| / c)
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => by exact_mod_cast hn⟩] with n hn
  have hNn : |a| / c ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have habs : |a| ≤ (n : ℝ) * c := by
    rwa [div_le_iff₀ hc] at hNn
  have habs' : |a| ≤ c * (n : ℝ) := by rw [mul_comm]; exact habs
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn]

/-- A single `o(n)` function plus a constant is still `o(n)`. -/
theorem isLittleO_nat_add_const {g : ℕ → ℝ}
    (hg : g =o[atTop] (fun n : ℕ => (n : ℝ))) (a : ℝ) :
    (fun n => g n + a) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  simpa only [add_comm] using hg.add (isLittleO_nat_const a)

/-- `HasLog2Exponent f c` reads: `f n ≤ c * n + o(n)` as `n → ∞`.

This is the logarithmic (base `2`) form of the paper's cost estimate
`2 ^ (c * n + o(n))`: if `f n = log₂ (cost n)` then this says exactly that
`cost n ≤ 2 ^ (c * n + o(n))`. -/
def HasLog2Exponent (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, g =o[atTop] (fun n : ℕ => (n : ℝ)) ∧ ∀ n : ℕ, f n ≤ c * (n : ℝ) + g n

namespace HasLog2Exponent

/-- Adding two estimates adds the leading coefficients and the `o(n)` remainders. -/
theorem add {f h : ℕ → ℝ} {c d : ℝ}
    (hf : HasLog2Exponent f c) (hh : HasLog2Exponent h d) :
    HasLog2Exponent (fun n => f n + h n) (c + d) := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨k, hk, hhk⟩ := hh
  refine ⟨fun n => g n + k n, ?_, fun n => ?_⟩
  · simpa only using hg.add hk
  · have h1 := hfg n
    have h2 := hhk n
    nlinarith [h1, h2]

/-- Rescaling an estimate by a nonnegative factor rescales the coefficient. -/
theorem const_mul {f : ℕ → ℝ} {c a : ℝ} (ha : 0 ≤ a)
    (hf : HasLog2Exponent f c) :
    HasLog2Exponent (fun n => a * f n) (a * c) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun n => a * g n, hg.const_mul_left a, fun n => ?_⟩
  have h1 := hfg n
  nlinarith [h1, ha, mul_nonneg ha (Nat.cast_nonneg (α := ℝ) n)]

/-- Pointwise equality preserves the estimate. -/
theorem congr {f g : ℕ → ℝ} {c : ℝ} (h : HasLog2Exponent f c)
    (hfg : ∀ n, f n = g n) : HasLog2Exponent g c := by
  obtain ⟨g', hg', hb⟩ := h
  exact ⟨g', hg', fun n => by rw [← hfg n]; exact hb n⟩

/-- A pointwise maximum of two estimates with the same coefficient keeps that
coefficient (the `max` of two `o(n)` remainders is again `o(n)`). -/
theorem max_exp {f h : ℕ → ℝ} {c : ℝ}
    (hf : HasLog2Exponent f c) (hh : HasLog2Exponent h c) :
    HasLog2Exponent (fun n => max (f n) (h n)) c := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨k, hk, hhk⟩ := hh
  refine ⟨fun n => max (g n) (k n), isLittleO_nat_max hg hk, fun n => ?_⟩
  have h1 := hfg n
  have h2 := hhk n
  exact max_le (by linarith [le_max_left (g n) (k n)])
    (by linarith [le_max_right (g n) (k n)])

/-- A pointwise maximum of two estimates keeps the larger of the two leading
coefficients.  This is the `max` step in Lemma 6, where the three quantum phases
have three different leading coefficients and the total is their maximum. -/
theorem sup {f h : ℕ → ℝ} {c d : ℝ}
    (hf : HasLog2Exponent f c) (hh : HasLog2Exponent h d) :
    HasLog2Exponent (fun n => max (f n) (h n)) (max c d) := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨k, hk, hhk⟩ := hh
  refine ⟨fun n => max (g n) (k n), isLittleO_nat_max hg hk, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact max_le
    (by nlinarith [hfg n, le_max_left (g n) (k n), le_max_left c d, le_max_right c d, hn])
    (by nlinarith [hhk n, le_max_right (g n) (k n), le_max_left c d, le_max_right c d, hn])

/-- Adding a constant to the logarithm keeps the leading coefficient (a constant
is `o(n)`). -/
theorem add_const {f : ℕ → ℝ} {c : ℝ} (hf : HasLog2Exponent f c) (a : ℝ) :
    HasLog2Exponent (fun n => f n + a) c := by
  obtain ⟨g, hg, hb⟩ := hf
  exact ⟨fun n => g n + a, isLittleO_nat_add_const hg a, fun n => by
    have h := hb n; linarith⟩

/-- Increasing the leading coefficient weakens the estimate. -/
theorem mono_coeff {f : ℕ → ℝ} {c c' : ℝ} (hf : HasLog2Exponent f c) (hcc : c ≤ c') :
    HasLog2Exponent f c' := by
  obtain ⟨g, hg, hb⟩ := hf
  exact ⟨g, hg, fun n => by
    have h := hb n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [h, hn, hcc]⟩

/-- If `f ≤ g` pointwise and `g` has an estimate, then `f` does too. -/
theorem of_le {f g : ℕ → ℝ} {c : ℝ} (h : HasLog2Exponent g c)
    (hfg : ∀ n, f n ≤ g n) : HasLog2Exponent f c := by
  obtain ⟨g', hg', hb⟩ := h
  exact ⟨g', hg', fun n => (hfg n).trans (hb n)⟩

end HasLog2Exponent

/-- Base-two logarithm upper bound via a truncated Taylor series for `exp`.

If `x > 0`, `z ≥ 0`, `z ≤ y * log 2`, and `x ≤ Σ_{i<n} z^i / i!`, then
`log₂ x ≤ y`.  This is the numerical engine for the concrete constants of
Theorems 1 and 2: the finite sum is a rational lower bound for `exp z`, hence
for `2 ^ y = exp (y log 2)`, hence `x ≤ 2 ^ y`, i.e. `log₂ x ≤ y`. -/
theorem logb_two_le_of_taylor {x y z : ℝ} {n : ℕ} (hx : 0 < x) (hz : 0 ≤ z)
    (hzy : z ≤ y * Real.log 2)
    (hxz : x ≤ ∑ i ∈ Finset.range n, z ^ i / (i.factorial : ℝ)) :
    Real.logb 2 x ≤ y := by
  have hxexp : x ≤ Real.exp (y * Real.log 2) := by
    refine hxz.trans (le_trans (Real.sum_le_exp_of_nonneg hz n) ?_)
    exact Real.exp_le_exp.mpr hzy
  have hlog : Real.log x ≤ y * Real.log 2 := (Real.log_le_iff_le_exp hx).mpr hxexp
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact hlog

/-- `log₂ (a + b) ≤ 1 + max (log₂ a) (log₂ b)` for `a, b > 0`.

Used to bound the *sum* of two sequential phase costs by the maximum of the two
phase exponents (`a + b ≤ 2 · max a b`, and base-two logarithms are monotone).
This is exactly the passage from the per-phase bullets of Appendix B to the
total time of Lemma 6. -/
theorem logb_two_sum_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.logb 2 (a + b) ≤ 1 + max (Real.logb 2 a) (Real.logb 2 b) := by
  have hab : 0 < a + b := by linarith
  have hM : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have hsum : a + b ≤ 2 * max a b := by
    have h1 := le_max_left a b
    have h2 := le_max_right a b
    nlinarith
  have hmono : Real.logb 2 (a + b) ≤ Real.logb 2 (2 * max a b) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) hab hsum
  have hsplit : Real.logb 2 (2 * max a b) = Real.logb 2 2 + Real.logb 2 (max a b) :=
    Real.logb_mul (b := 2) (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hM)
  have hmaxlog : Real.logb 2 (max a b) ≤ max (Real.logb 2 a) (Real.logb 2 b) := by
    rcases le_total a b with hle | hle
    · rw [max_eq_right hle]; exact le_max_right _ _
    · rw [max_eq_left hle]; exact le_max_left _ _
  rw [hsplit, Real.logb_self_eq_one (b := 2) (by norm_num : (1 : ℝ) < 2)] at hmono
  linarith

end Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore
