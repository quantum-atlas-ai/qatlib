/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Quantum.CommunicationProtocols

set_option backward.isDefEq.respectTransparency false

/-!
# Lower bounds from Theorem 20 — Propositions 21, 22 and 23 (pp. 14--15)

Fixed source: arXiv:2402.15686v3, §5.3 (pp. 14--15).

The pattern of all three propositions is the same: a quantum algorithm of the form (7) or (9)
preparing `|f(A)b⟩` yields, via Theorem 20, a communication protocol for Set-Disjointness
whose cost is `O(T log(mn))` when the algorithm makes `T` oracle calls.  The Set-Disjointness
hardness (named hypothesis) then gives

`hard / log(mn) ≤ O(T)`,

i.e. the `Ω(hard / log(mn))` lower bound, where `hard` is the hardness of the constructed
instance and, in each construction, `hard ≥ κ`, `hard ≥ e^t`, `hard ≥ κ^d`, `hard ≥ 1/γ`
respectively.

* **Proposition 21 (matrix inversion, p. 14):** `A_ii = 1/√n` for `a_i = 1`, `A_ii = 1`
  otherwise, so `κ = √n`; preparing `|A⁺b⟩` needs `Ω(κ/log(mn))` oracle calls / copies of `|b⟩`.
* **Proposition 22 (matrix exponential, p. 15):** `A` diagonal with `A_ii = a_i`, `t = ½ ln n`,
  `e^t = √n`; preparing `|e^{At} b⟩` needs `Ω(e^t/log(mn))`.
* **Proposition 23 (matrix powers, p. 15):** `A_ii = 1` or `ε`, `ε^{2d} n = 1`, `κ = 1/ε`,
  `κ^d = √n`; alternatively `ε = 0`, `γ = ‖A^d b‖/‖b‖ = 1/√n`.  Preparing `|A^d b⟩` needs
  `Ω((κ^d + 1/γ)/log(mn))`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Quantum

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Simulation

/-! ## §1. The generic "hardness divided by log(mn)" step -/

/-- **Generic Theorem-20 step.**  If a task needs `hard` communication and the induced
protocol has cost `C · B · log(mn)` (`B` the number of oracle calls, up to the additive
player count), then `hard / log(mn) ≤ C · B`.  This is the single step turning
Theorem 20 into Propositions 21--23. -/
theorem kappa_over_log_lower_bound (κ hard C B L' : ℝ)
    (hL : 0 < L') (hC : 0 ≤ C)
    (hhard : hard ≤ C * B * L') (hκ : κ ≤ hard) :
    κ / L' ≤ C * B := by
  have h1 : κ * L'⁻¹ ≤ (C * B * L') * L'⁻¹ :=
    mul_le_mul_of_nonneg_right (le_trans hκ hhard) (inv_nonneg.mpr hL.le)
  have h2 : (C * B * L') * L'⁻¹ = C * B := by
    have hassoc : (C * B * L') * L'⁻¹ = (C * B) * (L' * L'⁻¹) := by ring
    rw [hassoc, mul_inv_cancel₀ (ne_of_gt hL), mul_one]
  rw [div_eq_mul_inv]
  exact le_trans h1 (le_of_eq h2)

/-! ## §2. Elementary inequalities for the constructed instances -/

/-- `√n ≤ n` for `n ≥ 1`. -/
theorem sqrt_le_self_cast {n : ℕ} (hn : 1 ≤ n) : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := by
        rw [Real.sqrt_le_sqrt_iff (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
    _ = (n : ℝ) := Real.sqrt_sq h0

/-- The Set-Disjointness hardness `(k : ℝ) * n` dominates `√n` for `k, n ≥ 1`; this is the
`κ = √n` step of Propositions 21--23. -/
theorem sqrt_le_card_mul {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≤ (k : ℝ) * (n : ℝ) := by
  have h1 : Real.sqrt (n : ℝ) ≤ (n : ℝ) := sqrt_le_self_cast hn
  have h2 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  calc Real.sqrt (n : ℝ) ≤ (n : ℝ) := h1
    _ = 1 * (n : ℝ) := (one_mul _).symm
    _ ≤ (k : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right h2 h3

/-- With `t = ½ ln n` the matrix-exponential parameter is `e^t = √n` (Proposition 22, p. 15). -/
theorem exp_half_log_eq_sqrt {n : ℕ} (hn : 0 < n) :
    Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = Real.sqrt (n : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  congr 1
  ring

/-! ## §3. Proposition 21 — matrix inversion (`κ = √n`) -/

/-- **Proposition 21 (p. 14).**  Any quantum algorithm of the form (7) or (9) preparing
`|A⁺b⟩` for the Set-Disjointness instance needs `Ω(κ / log(mn))` oracle calls (and likewise
copies of `|b⟩`), where `κ = √n` is the condition number of the constructed diagonal matrix.
Here `hard = kn` is the Set-Disjointness communication hardness and the algorithm induces a
protocol of cost `≤ C·(T+k)·log(qkn)` (Theorem 20). -/
theorem matrix_inversion_query_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c)
    (hc : 0 ≤ c) (k n T q m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hq : 0 < q)
    (hkn : 3200 * k ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ)
      ≤ C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    Real.sqrt (n : ℝ) / (logBits (q * (k * n)) : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) := by
  have hL : (0 : ℝ) < (logBits (q * (k * n)) : ℝ) := by
    have h := one_le_logBits_mul (a := q) (b := k * n) hq (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have : (1 : ℝ) ≤ (logBits (q * (k * n)) : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hkn p hs
  have h2 : (k : ℝ) * (n : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
    calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := h1
      _ ≤ c * (C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcost hc
      _ = (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring
  exact kappa_over_log_lower_bound (Real.sqrt (n : ℝ)) ((k : ℝ) * (n : ℝ)) (c * C)
    ((T : ℝ) + (k : ℝ)) (logBits (q * (k * n)) : ℝ) hL (mul_nonneg hc hC) h2
    (sqrt_le_card_mul hk hn)

/-! ## §4. Proposition 22 — matrix exponential (`e^t = √n` at `t = ½ ln n`) -/

/-- **Proposition 22 (p. 15).**  Any quantum algorithm of the form (7) or (9) preparing
`|e^{At}b⟩` needs `Ω(e^t / log(mn))` oracle calls (and likewise copies of `|b⟩`); for the
Set-Disjointness construction `A` is diagonal with `A_ii = a_i` and `t = ½ ln n`, so
`e^t = √n` (`exp_half_log_eq_sqrt`). -/
theorem matrix_exponential_query_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c)
    (hc : 0 ≤ c) (k n T q m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hq : 0 < q)
    (hkn : 3200 * k ≤ n) (t : ℝ) (ht : Real.exp t = Real.sqrt (n : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ)
      ≤ C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    Real.exp t / (logBits (q * (k * n)) : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) := by
  have hL : (0 : ℝ) < (logBits (q * (k * n)) : ℝ) := by
    have h := one_le_logBits_mul (a := q) (b := k * n) hq (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have : (1 : ℝ) ≤ (logBits (q * (k * n)) : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hkn p hs
  have h2 : (k : ℝ) * (n : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
    calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := h1
      _ ≤ c * (C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcost hc
      _ = (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring
  have hκ : Real.exp t ≤ (k : ℝ) * (n : ℝ) := by
    rw [ht]
    exact sqrt_le_card_mul hk hn
  exact kappa_over_log_lower_bound (Real.exp t) ((k : ℝ) * (n : ℝ)) (c * C)
    ((T : ℝ) + (k : ℝ)) (logBits (q * (k * n)) : ℝ) hL (mul_nonneg hc hC) h2 hκ

/-! ## §5. Proposition 23 — matrix powers (`κ^d` and `1/γ`) -/

/-- **Proposition 23, `κ^d` part (p. 15).**  With `A_ii = 1` or `ε`, `ε^{2d} n = 1`, we have
`κ^d = √n` for `κ = 1/ε`; preparing `|A^d b⟩` then needs `Ω(κ^d / log(mn))` oracle calls. -/
theorem matrix_powers_kappa_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c)
    (hc : 0 ≤ c) (k n T q m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hq : 0 < q)
    (hkn : 3200 * k ≤ n) (κ : ℝ) (d : ℕ) (hκ : κ ^ d ≤ Real.sqrt (n : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ)
      ≤ C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    κ ^ d / (logBits (q * (k * n)) : ℝ) ≤ (c * C) * ((T : ℝ) + (k : ℝ)) := by
  have hL : (0 : ℝ) < (logBits (q * (k * n)) : ℝ) := by
    have h := one_le_logBits_mul (a := q) (b := k * n) hq (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have : (1 : ℝ) ≤ (logBits (q * (k * n)) : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hkn p hs
  have h2 : (k : ℝ) * (n : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
    calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := h1
      _ ≤ c * (C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcost hc
      _ = (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring
  exact kappa_over_log_lower_bound (κ ^ d) ((k : ℝ) * (n : ℝ)) (c * C)
    ((T : ℝ) + (k : ℝ)) (logBits (q * (k * n)) : ℝ) hL (mul_nonneg hc hC) h2
    (le_trans hκ (sqrt_le_card_mul hk hn))

/-- **Proposition 23, `1/γ` part (p. 15).**  In the `ε = 0` regime `κ = 1` and
`γ = ‖A^d b‖/‖b‖ = 1/√n`, i.e. `1/γ = √n`; preparing `|A^d b⟩` needs `Ω(1/(γ log(mn)))`
oracle calls. -/
theorem matrix_powers_gamma_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c)
    (hc : 0 ≤ c) (k n T q m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hq : 0 < q)
    (hkn : 3200 * k ≤ n) (γ : ℝ) (hγ : γ = 1 / Real.sqrt (n : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ)
      ≤ C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    (1 / γ) / (logBits (q * (k * n)) : ℝ) ≤ (c * C) * ((T : ℝ) + (k : ℝ)) := by
  have hL : (0 : ℝ) < (logBits (q * (k * n)) : ℝ) := by
    have h := one_le_logBits_mul (a := q) (b := k * n) hq (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have : (1 : ℝ) ≤ (logBits (q * (k * n)) : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hkn p hs
  have h2 : (k : ℝ) * (n : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
    calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := h1
      _ ≤ c * (C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcost hc
      _ = (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring
  have hκ : 1 / γ ≤ (k : ℝ) * (n : ℝ) := by
    rw [hγ, one_div_one_div]
    exact sqrt_le_card_mul hk hn
  exact kappa_over_log_lower_bound (1 / γ) ((k : ℝ) * (n : ℝ)) (c * C)
    ((T : ℝ) + (k : ℝ)) (logBits (q * (k * n)) : ℝ) hL (mul_nonneg hc hC) h2 hκ

/-- **Proposition 23, combined form (p. 15).**  `Ω((κ^d + 1/γ)/log(mn))` lower bound for
preparing `|A^d b⟩`, obtained by summing the two regimes up to a factor `2` in the constant. -/
theorem matrix_powers_query_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c)
    (hc : 0 ≤ c) (k n T q m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hq : 0 < q)
    (hkn : 3200 * k ≤ n) (κ γ : ℝ) (d : ℕ)
    (hcomb : κ ^ d + 1 / γ ≤ 2 * (Real.sqrt (n : ℝ)))
    (C : ℝ) (hC : 0 ≤ C)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ)
      ≤ C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    (κ ^ d + 1 / γ) / (logBits (q * (k * n)) : ℝ)
      ≤ (2 * (c * C)) * ((T : ℝ) + (k : ℝ)) := by
  have hL : (0 : ℝ) < (logBits (q * (k * n)) : ℝ) := by
    have h := one_le_logBits_mul (a := q) (b := k * n) hq (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have : (1 : ℝ) ≤ (logBits (q * (k * n)) : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hkn p hs
  have h2 : (k : ℝ) * (n : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
    calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := h1
      _ ≤ c * (C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcost hc
      _ = (c * C) * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring
  have hκ : κ ^ d + 1 / γ ≤ 2 * ((k : ℝ) * (n : ℝ)) := by
    calc κ ^ d + 1 / γ ≤ 2 * Real.sqrt (n : ℝ) := hcomb
      _ ≤ 2 * ((k : ℝ) * (n : ℝ)) := by
          have := sqrt_le_card_mul hk hn
          linarith
  have hmain : ((k : ℝ) * (n : ℝ)) / (logBits (q * (k * n)) : ℝ)
      ≤ (c * C) * ((T : ℝ) + (k : ℝ)) :=
    kappa_over_log_lower_bound ((k : ℝ) * (n : ℝ)) ((k : ℝ) * (n : ℝ)) (c * C)
      ((T : ℝ) + (k : ℝ)) (logBits (q * (k * n)) : ℝ) hL (mul_nonneg hc hC) h2 le_rfl
  have hdiv : (κ ^ d + 1 / γ) / (logBits (q * (k * n)) : ℝ)
      ≤ (2 * ((k : ℝ) * (n : ℝ))) / (logBits (q * (k * n)) : ℝ) :=
    div_le_div_of_nonneg_right hκ hL.le
  calc (κ ^ d + 1 / γ) / (logBits (q * (k * n)) : ℝ)
      ≤ (2 * ((k : ℝ) * (n : ℝ))) / (logBits (q * (k * n)) : ℝ) := hdiv
    _ = 2 * (((k : ℝ) * (n : ℝ)) / (logBits (q * (k * n)) : ℝ)) := by ring
    _ ≤ 2 * ((c * C) * ((T : ℝ) + (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = (2 * (c * C)) * ((T : ℝ) + (k : ℝ)) := by ring

end Qatlib.Papers.QInspired25.MainResults.Quantum
