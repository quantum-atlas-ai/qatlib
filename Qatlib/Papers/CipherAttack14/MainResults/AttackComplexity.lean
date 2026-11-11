/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# CipherAttack14 — the complexity bookkeeping of Theorems 1, 2, 4 and Corollary 1

Fixed source: M. Kaplan, *Quantum attacks against iterated block ciphers*,
arXiv:1410.1434v2 (2015).

* Theorem 1 (p. 4) states that for `M ≥ N` the quantum query and time complexity
  of element distinctness and claw finding is `Θ(N^{2/3})`, and that the most
  time-efficient algorithm uses memory `O(N^{2/3})`.
* Theorem 2 (p. 5) gives `KE2` an algorithm of time `O(N^{2/3})` and memory
  `O(N^{2/3})`; Corollary 1 (p. 5) concludes that the time-space product of the
  most time-efficient attack is `O(N^{4/3})`, and the remark after it observes
  that this is *worse* than the `O(N)` product of Grover search.
* Theorem 4 (p. 10) gives `KE4` an algorithm of time `O(M^{1/2} N^{2/3})` and
  memory `O(N^{2/3})`, hence time-space product `O(M^{1/2} N^{4/3})`; with `M`
  and `N` of comparable size these are `O(N^{7/6})`, `O(N^{2/3})` and
  `O(N^{11/6})`.
* The proof of Theorem 4 applies the walk cost `S + (1/√ε)((1/√δ)U + C)` of
  Theorem 5 with setup and update cost `O(1)`, checking probability `ε = 1/M` and
  eigenvalue gap `δ = 1 - 1/(M-1)` on the complete graph.
* The gain of a quantized attack is `log C / log Q` (p. 8); Table 1 (p. 8) and
  Table 2 (p. 10) record the gains `3/2` for meet-in-the-middle time, `12/7` for
  dissection time, and `18/11` for the dissection time-space product.

This module formalizes that arithmetic, including the walk's amplification and
gap substitution.  It deliberately contains no query-algorithm model, no walk
implementation and no adversary argument, so it does not by itself establish any
of the asymptotic upper or lower bounds as bounds on algorithms.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CipherAttack14.MainResults

open Real

/-- Corollary 1 (p. 5): the time `N^{2/3}` of Theorem 2 multiplied by its memory
`N^{2/3}` gives time-space product `N^{4/3}`. -/
theorem corollary1_timeSpaceProduct {N : ℝ} (hN : 0 < N) :
    N ^ (2/3 : ℝ) * N ^ (2/3 : ℝ) = N ^ (4/3 : ℝ) := by
  rw [← Real.rpow_add hN]
  congr 1
  norm_num

/-- The remark after Corollary 1 (p. 5): the time-space product `N^{4/3}` of the
meet-in-the-middle attack is worse than the product `N` of plain Grover search,
which uses only logarithmic space. -/
theorem grover_product_smaller {N : ℝ} (hN : 1 < N) :
    N ^ (1 : ℝ) < N ^ (4/3 : ℝ) := by
  exact Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)

/-- Theorem 4 (p. 10): the attack's time `M^{1/2} N^{2/3}` multiplied by its memory
`N^{2/3}` bounds the time-space product by `M^{1/2} N^{4/3}`. -/
theorem theorem4_timeSpaceProduct {M N : ℝ} (hN : 0 < N) :
    M ^ (1/2 : ℝ) * N ^ (2/3 : ℝ) * N ^ (2/3 : ℝ) = M ^ (1/2 : ℝ) * N ^ (4/3 : ℝ) := by
  rw [mul_assoc, ← Real.rpow_add hN]
  congr 2
  norm_num

/-- Theorem 4 (p. 10) with `M` and `N` of comparable size: the query and time
bound `M^{1/2} N^{2/3}` becomes `N^{7/6}`. -/
theorem theorem4_timeComparable {N : ℝ} (hN : 0 < N) :
    N ^ (1/2 : ℝ) * N ^ (2/3 : ℝ) = N ^ (7/6 : ℝ) := by
  rw [← Real.rpow_add hN]
  congr 1
  norm_num

/-- Theorem 4 (p. 10) with `M` and `N` of comparable size: the time-space product
`M^{1/2} N^{4/3}` becomes `N^{11/6}`. -/
theorem theorem4_productComparable {N : ℝ} (hN : 0 < N) :
    N ^ (1/2 : ℝ) * N ^ (4/3 : ℝ) = N ^ (11/6 : ℝ) := by
  rw [← Real.rpow_add hN]
  congr 1
  norm_num

/-- The amplification factor of Theorem 5 for the walk of Theorem 4 (p. 10): with
checking probability `ε = 1/M`, the factor `1/√ε` is `√M`, the Grover factor over
the `M` candidate middle values.  (The identity is algebraic and holds for every
real `M`; the paper needs `M > 0`, which is what makes `√M` the Grover factor.) -/
theorem walk_amplification (M : ℝ) :
    1 / Real.sqrt (1 / M) = Real.sqrt M := by
  rw [one_div, one_div, Real.sqrt_inv, inv_inv]

/-- The eigenvalue gap of the complete graph on `M` vertices (p. 10) is
`δ = 1 - 1/(M-1)`, which is positive as soon as there are at least two
vertices. -/
theorem completeGraph_gap_pos {M : ℝ} (hM : 2 < M) : 0 < 1 - 1 / (M - 1) := by
  have hM1 : 0 < M - 1 := by linarith
  have h1 : 1 / (M - 1) < 1 := by
    rw [div_lt_one hM1]
    linarith
  linarith

/-- The eigenvalue gap of the complete graph is bounded below by `1/2` from three
vertices on, so the walk's `1/√δ` factor is at most `2`: a constant, absorbed by
the `O(·)` in Theorem 4. -/
theorem completeGraph_gap_amplification_le_two {M : ℝ} (hM : 3 ≤ M) :
    1 / Real.sqrt (1 - 1 / (M - 1)) ≤ 2 := by
  have hM1 : 0 < M - 1 := by linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 1 / (M - 1) := by
    have h : 1 / (M - 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hquarter : (1 : ℝ) / 4 ≤ 1 - 1 / (M - 1) := le_trans (by norm_num) hhalf
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (1 - 1 / (M - 1)) := by
    have h := Real.sqrt_le_sqrt hquarter
    rwa [show Real.sqrt ((1 : ℝ) / 4) = 1 / 2 by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  calc
    1 / Real.sqrt (1 - 1 / (M - 1)) ≤ 1 / ((1 : ℝ) / 2) :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    _ = 2 := by norm_num

/-- Table 1 (p. 8) and Table 2 (p. 10): the gain in time of the quantum
meet-in-the-middle attack, `log N / log N^{2/3}`, is `3/2`. -/
theorem gain_mitm_time {N : ℝ} (hN : 1 < N) :
    Real.log (N ^ (1 : ℝ)) / Real.log (N ^ (2/3 : ℝ)) = 3 / 2 := by
  have h0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [Real.log_rpow h0, Real.log_rpow h0, one_mul]
  field_simp

/-- Table 2 (p. 10): the gain in time of the quantized dissection attack,
`log N^2 / log N^{7/6}`, is `12/7`. -/
theorem gain_dissection_time {N : ℝ} (hN : 1 < N) :
    Real.log (N ^ (2 : ℝ)) / Real.log (N ^ (7/6 : ℝ)) = 12 / 7 := by
  have h0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [Real.log_rpow h0, Real.log_rpow h0]
  field_simp
  norm_num

/-- Table 2 (p. 10): the gain in the time-space product of the quantized
dissection attack, `log N^3 / log N^{11/6}`, is `18/11`. -/
theorem gain_dissection_product {N : ℝ} (hN : 1 < N) :
    Real.log (N ^ (3 : ℝ)) / Real.log (N ^ (11/6 : ℝ)) = 18 / 11 := by
  have h0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [Real.log_rpow h0, Real.log_rpow h0]
  field_simp
  norm_num

end Qatlib.Papers.CipherAttack14.MainResults
