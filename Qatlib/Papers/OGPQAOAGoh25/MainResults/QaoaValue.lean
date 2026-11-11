/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! QAOA value degree-asymptotics for
"The Overlap Gap Property limits limit swapping in the QAOA"
(arXiv:2404.06087v6, 2025, Mark Goh).

Theorem 4.2 (Eq. (19)) expresses the expected QAOA value on Max-q-XORSAT
over D-regular q-uniform hypergraphs as
`1/2 + ν∞^{[q]}(D, γ, β)·√q/(2D) + O(1/√D)`, with `D` the hypergraph
degree. This file proves the degree-asymptotic core of that formula in a
restricted abstract form: the infinite-size coefficient `ν∞` enters as an
abstract `ν` with `|ν| ≤ 1`, and the `O(1/√D)` term as an abstract
remainder `r` with an explicit bound `c/√D`.

- `qaoa_value_degree_bound` gives the explicit non-asymptotic upper
  bound `1/2 + √q/(2D) + c/√D` for every degree `D ≥ 1`.
- `qaoa_value_tendsto_one_half` shows the value converges to `1/2` as
  `D → ∞`, the degree-robustness step behind "for every ε > 0 there is
  `d₀` with value `< ηOGP + ε`" in Theorem 4.2.

The derivation of the formula itself (QAOA moment recursion, Gaussian
moments, Guerra-type inputs) is not formalized; see the PR work log.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

open Filter Topology

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults.QaoaValue

/-- **Theorem 4.2 (Eq. (19)), explicit degree bound**: with the
infinite-size coefficient `ν` bounded by `1` and the remainder bounded
by `c/√D`, the QAOA value expression is at most
`1/2 + √q/(2D) + c/√D` for every degree `D ≥ 1`. -/
theorem qaoa_value_degree_bound (q : ℕ) {D : ℕ} (hD : 0 < D) (ν r c : ℝ)
    (hν : |ν| ≤ 1) (hr : |r| ≤ c / Real.sqrt D) :
    1 / 2 + ν * Real.sqrt q / (2 * D) + r
      ≤ 1 / 2 + Real.sqrt q / (2 * D) + c / Real.sqrt D := by
  have hsq : (0:ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hd : (0:ℝ) ≤ 2 * D := by positivity
  have hterm : ν * Real.sqrt q / (2 * D) ≤ Real.sqrt q / (2 * D) := by
    have h1 : |ν * Real.sqrt q| ≤ Real.sqrt q := by
      rw [abs_mul, abs_of_nonneg hsq]
      calc |ν| * Real.sqrt q ≤ 1 * Real.sqrt q :=
          mul_le_mul_of_nonneg_right hν hsq
      _ = Real.sqrt q := one_mul _
    have h2 : |ν * Real.sqrt q / (2 * D)| ≤ Real.sqrt q / (2 * D) := by
      rw [abs_div, abs_of_nonneg hd]
      exact div_le_div_of_nonneg_right h1 hd
    exact (le_abs_self _).trans h2
  have hrterm : r ≤ c / Real.sqrt D := (le_abs_self _).trans hr
  linarith

/-- **Theorem 4.2 (Eq. (19)), degree limit**: with `|v D| ≤ 1` and
`|r D| ≤ c/√D` for all degrees `D ≥ 1`, the QAOA value expression
converges to `1/2` as `D → ∞`. This is the degree-robustness core of the
"∀ε > 0 ∃d₀, value < ηOGP + ε" step of Theorem 4.2 (any
`ηOGP > 1/2` leaves room for the remainder to be absorbed). -/
theorem qaoa_value_tendsto_one_half (q : ℕ) (c : ℝ) (v r : ℕ → ℝ)
    (hv : ∀ D, |v D| ≤ 1) (hr : ∀ D, 0 < D → |r D| ≤ c / Real.sqrt D) :
    Filter.Tendsto (fun D : ℕ => 1 / 2 + v D * Real.sqrt q / (2 * D) + r D)
      Filter.atTop (𝓝 (1 / 2)) := by
  have hsq : (0:ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hc : 0 ≤ c := by
    have h1 := hr 1 (by norm_num)
    norm_num at h1
    exact (abs_nonneg (r 1)).trans h1
  have hterm : ∀ D : ℕ,
      |v D * Real.sqrt q / (2 * D)| ≤ Real.sqrt q / (2 * D) := by
    intro D
    have hd : (0:ℝ) ≤ 2 * D := by positivity
    have h1 : |v D * Real.sqrt q| ≤ Real.sqrt q := by
      rw [abs_mul, abs_of_nonneg hsq]
      calc |v D| * Real.sqrt q ≤ 1 * Real.sqrt q :=
          mul_le_mul_of_nonneg_right (hv D) hsq
      _ = Real.sqrt q := one_mul _
    rw [abs_div, abs_of_nonneg hd]
    exact div_le_div_of_nonneg_right h1 hd
  have hbd : ∀ D : ℕ, (1:ℕ) ≤ D →
      |1 / 2 + v D * Real.sqrt q / (2 * D) + r D - 1 / 2|
        ≤ Real.sqrt q / (2 * D) + c / Real.sqrt D := by
    intro D hD1
    have hrterm : |r D| ≤ c / Real.sqrt D := hr D (by omega)
    have hsplit : |1 / 2 + v D * Real.sqrt q / (2 * D) + r D - 1 / 2|
        = |v D * Real.sqrt q / (2 * D) + r D| := by
      congr 1
      ring
    rw [hsplit, abs_le]
    constructor <;> linarith [le_abs_self (v D * Real.sqrt q / (2 * D)),
      le_abs_self (r D), neg_abs_le (v D * Real.sqrt q / (2 * D)), neg_abs_le (r D),
      hterm D, hrterm]
  have tcast : Filter.Tendsto (fun D : ℕ => (D : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hinv1 : Filter.Tendsto (fun D : ℕ => ((D : ℝ))⁻¹) Filter.atTop (𝓝 (0:ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tcast
  have t1div : Filter.Tendsto (fun D : ℕ => 1 / (D : ℝ)) Filter.atTop (𝓝 (0:ℝ)) := by
    have heq : (fun D : ℕ => ((D : ℝ))⁻¹) = (fun D : ℕ => 1 / (D : ℝ)) :=
      funext fun D => (one_div _).symm
    rw [heq] at hinv1
    exact hinv1
  have tsqrt : Filter.Tendsto (fun D : ℕ => Real.sqrt (D : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tcast
  have hinvsqrt : Filter.Tendsto (fun D : ℕ => (Real.sqrt (D : ℝ))⁻¹) Filter.atTop (𝓝 (0:ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tsqrt
  have t1sqrt : Filter.Tendsto (fun D : ℕ => 1 / Real.sqrt (D : ℝ)) Filter.atTop (𝓝 (0:ℝ)) := by
    have heq : (fun D : ℕ => (Real.sqrt (D : ℝ))⁻¹)
        = (fun D : ℕ => 1 / Real.sqrt (D : ℝ)) :=
      funext fun D => (one_div _).symm
    rw [heq] at hinvsqrt
    exact hinvsqrt
  have tleft : Filter.Tendsto (fun D : ℕ => Real.sqrt q / (2 * D)) Filter.atTop (𝓝 (0:ℝ)) := by
    have h : Filter.Tendsto
        (fun D : ℕ => Real.sqrt q / 2 * ((D : ℝ))⁻¹) Filter.atTop
        (𝓝 (Real.sqrt q / 2 * 0)) :=
      (tendsto_const_nhds).mul hinv1
    rw [mul_zero] at h
    have heq : (fun D : ℕ => Real.sqrt q / 2 * ((D : ℝ))⁻¹)
        = (fun D : ℕ => Real.sqrt q / (2 * D)) :=
      funext fun D => by field_simp
    rw [heq] at h
    exact h
  have tright : Filter.Tendsto (fun D : ℕ => c / Real.sqrt (D : ℝ)) Filter.atTop (𝓝 (0:ℝ)) := by
    have h : Filter.Tendsto
        (fun D : ℕ => c * (Real.sqrt (D : ℝ))⁻¹) Filter.atTop (𝓝 (c * 0)) :=
      (tendsto_const_nhds).mul hinvsqrt
    rw [mul_zero] at h
    have heq : (fun D : ℕ => c * (Real.sqrt (D : ℝ))⁻¹)
        = (fun D : ℕ => c / Real.sqrt (D : ℝ)) :=
      funext fun D => by field_simp
    rw [heq] at h
    exact h
  have tsum : Filter.Tendsto
      (fun D : ℕ => Real.sqrt q / (2 * D) + c / Real.sqrt (D : ℝ))
      Filter.atTop (𝓝 (0:ℝ)) := by
    simpa using Tendsto.add tleft tright
  rw [tendsto_iff_dist_tendsto_zero]
  suffices h : Filter.Tendsto
      (fun D : ℕ => |1 / 2 + v D * Real.sqrt q / (2 * D) + r D - 1 / 2|)
      Filter.atTop (𝓝 (0:ℝ)) by
    exact h.congr (fun D => (Real.dist_eq _ _).symm)
  refine squeeze_zero' (Eventually.of_forall fun D => abs_nonneg _) ?_ tsum
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with D hD1
  exact hbd D hD1

end Qatlib.Papers.OGPQAOAGoh25.MainResults.QaoaValue
