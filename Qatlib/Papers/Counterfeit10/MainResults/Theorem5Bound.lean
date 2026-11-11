/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Weight scheme for Theorem 5 (Counterfeit10, Appendix C, "small pans")

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Appendix C.

Theorem 5 bounds the query complexity of finding `k` false coins when every weighing places at
most `l` coins on each pan: `Ω(√(kN / (l · min(k,l))))`.  Its proof instantiates Zhang's strong
weighted adversary theorem (Lemma 3) with a scheme whose every vertex has total weight

`μ(x) = k (N - k)`

and for which the product of the query weights obeys

`ν(x,q) · ν(y,q) = O(k N l · min(k,l))`.

The adversary theorem then gives the bound
`√(μ² / (νν)) = k(N-k) / √(K · k N l · min(k,l))` for an absolute constant `K`, and the paper
simplifies this to `Ω(√(kN / (l min(k,l))))` using `k ≤ N/2`.

This file formalises the **analytic step**: from `μ = k(N-k)`, `νν ≤ K·k·N·l·m` and `2k ≤ N`, the
squared adversary bound dominates `(1/(4K))·(kN/(l m))`, i.e.

`(1/(4K)) · (k N / (l m)) ≤ (k(N-k))² / (K · k N l m)`.

Because both displayed quantities are non-negative this is exactly the square of the claimed
`(1/(2√K))·√(kN/(lm)) ≤ k(N-k)/√(K k N l m)`, and taking square roots recovers Theorem 5's
`Ω` bound.  The combinatorial part (the weight assignment and the computation of `νν`) is not
mechanised.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- Theorem 5, adversary/weight counting step in squared form.  With vertex weight `μ = k(N-k)`,
query-weight product bounded by `K·k·N·l·m`, and `k ≤ N/2`, the squared adversary bound
`μ²/(K k N l m)` dominates `(1/(4K))·(kN/(lm))`. -/
theorem theorem5_sq_bound {k N l m K : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hl : 0 < l) (hm : 0 < m) (hK : 0 < K)
    (hkn : 2 * k ≤ N) :
    (1 / (4 * K)) * (k * N / (l * m)) ≤
      (k * (N - k)) ^ 2 / (K * (k * N * l * m)) := by
  have hlm : (0 : ℝ) < l * m := mul_pos hl hm
  have hkN : (0 : ℝ) < k * N := mul_pos hk hN
  have hkNlm : (0 : ℝ) < k * N * l * m := mul_pos (mul_pos hkN hl) hm
  have hK4 : (0 : ℝ) < 4 * K := by linarith
  have hD : (0 : ℝ) < K * (k * N * l * m) := mul_pos hK hkNlm
  -- rewrite the left factor as a division
  have hlhs : (1 / (4 * K)) * (k * N / (l * m)) = (k * N / (l * m)) / (4 * K) := by
    rw [div_eq_mul_inv]; ring
  rw [hlhs, div_le_div_iff₀ hK4 hD]
  -- simplify `(kN/(lm)) * (K * kNlm)` to `K * (kN)^2`
  have hsimp : (k * N / (l * m)) * (K * (k * N * l * m)) = K * (k * N) ^ 2 := by
    field_simp [ne_of_gt hlm]
  rw [hsimp]
  -- reduce to `(kN)^2 ≤ 4 (k(N-k))^2`
  have hkey : (k * N) ^ 2 ≤ 4 * (k * (N - k)) ^ 2 := by
    have h1 : k * N ≤ 2 * (k * (N - k)) := by nlinarith [hk, hkn]
    have h2 := pow_le_pow_left₀ (le_of_lt hkN) h1 2
    nlinarith [h2]
  have hfin : K * (k * N) ^ 2 ≤ (k * (N - k)) ^ 2 * (4 * K) := by
    have := mul_le_mul_of_nonneg_left hkey (le_of_lt hK)
    nlinarith [this]
  exact hfin

/-- A trivially equivalent restatement in the paper's `O(k N l · min(k,l))` shape, exhibiting the
constant: if the query-weight product is at most `K · k · N · l · m`, the squared bound holds. -/
theorem theorem5_sq_bound' {k N l m K nu : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hl : 0 < l) (hm : 0 < m) (hK : 0 < K)
    (hkn : 2 * k ≤ N) (hnu : nu ≤ K * (k * N * l * m)) :
    (1 / (4 * K)) * (k * N / (l * m)) * nu ≤
      (k * (N - k)) ^ 2 := by
  have hbase := theorem5_sq_bound hk hN hl hm hK hkn
  have hlm : (0 : ℝ) < l * m := mul_pos hl hm
  have hkN : (0 : ℝ) < k * N := mul_pos hk hN
  have hkNlm : (0 : ℝ) < k * N * l * m := mul_pos (mul_pos hkN hl) hm
  have hD : (0 : ℝ) < K * (k * N * l * m) := mul_pos hK hkNlm
  have hK4 : (0 : ℝ) < 4 * K := by linarith
  have hLnonneg : (0 : ℝ) ≤ (1 / (4 * K)) * (k * N / (l * m)) :=
    mul_nonneg (div_nonneg zero_le_one (le_of_lt hK4))
      (div_nonneg (le_of_lt hkN) (le_of_lt hlm))
  calc (1 / (4 * K)) * (k * N / (l * m)) * nu
      ≤ (1 / (4 * K)) * (k * N / (l * m)) * (K * (k * N * l * m)) :=
          mul_le_mul_of_nonneg_left hnu hLnonneg
    _ ≤ ((k * (N - k)) ^ 2 / (K * (k * N * l * m))) * (K * (k * N * l * m)) :=
          mul_le_mul_of_nonneg_right hbase (le_of_lt hD)
    _ = (k * (N - k)) ^ 2 := by field_simp [ne_of_gt hD]

end Qatlib.Papers.Counterfeit10.MainResults
