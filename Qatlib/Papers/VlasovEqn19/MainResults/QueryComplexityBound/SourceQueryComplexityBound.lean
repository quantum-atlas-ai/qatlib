/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QueryComplexityBound — Eq. (36) of the Vlasov algorithm

Paper: Engel--Smith--Parker, "Quantum Algorithm for the Vlasov Equation",
fixed arXiv:1907.09418.  Claim `c003` (MainResults, p. 6).

The Hamiltonian-simulation error bound of Low--Chuang [17] used by the paper is
`b(n) := 32 (t'/2)^n / n!` (Eq. (34)).  In the large-`t'` regime the paper
chooses the smallest `n` with `n ≥ e t'/2 + ln(1/ε) + 1.5` (Eq. (35)); the
circuit then uses `Q = 2L = 4(n-1)` queries (`L = 2(n-1)`), and this yields

  `Q ≤ 2 e t' + 4 ln(1/ε) + 6`.                                    (Eq. (36))

This file formalises the arithmetic content of Eq. (35) ⇒ Eq. (36): if the
implementation takes the minimal integer `n = ⌈e t'/2 + ln(1/ε) + 1.5⌉`, then
the query count `4(n-1)` obeys the stated bound.

Boundary: the input `n` is exactly the paper's rounded threshold; the lemma
does not re-derive Eq. (35) from the factorial error bound `b(n)` (the paper
uses an asymptotic approximation there).  `ε ∈ (0,1]` is the error tolerance.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VlasovEqn19.MainResults.QueryComplexityBound

/-- The rounded threshold of Eq. (35): `e t'/2 + ln(1/ε) + 1.5`, with
`e = Real.exp 1`. -/
def threshold (t' ε : ℝ) : ℝ :=
  Real.exp 1 * t' / 2 + Real.log (1 / ε) + 1.5

/-- Number of Hamiltonian-simulation queries of the algorithm: `Q = 2L` with
`L = 2(n-1)`, i.e. `Q = 4(n-1)` (p. 6). -/
def queryCount (n : ℕ) : ℕ :=
  4 * (n - 1)

/-- Claim `c003`, Eq. (36): with the paper's choice
`n = ⌈e t'/2 + ln(1/ε) + 1.5⌉` and `0 < ε ≤ 1`, `t' ≥ 0`, the query cost is
bounded by `2 e t' + 4 ln(1/ε) + 6`. -/
theorem query_complexity_bound (t' ε : ℝ) (ht' : 0 ≤ t')
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (queryCount (Nat.ceil (threshold t' ε)) : ℝ) ≤
      2 * Real.exp 1 * t' + 4 * Real.log (1 / ε) + 6 := by
  set n : ℕ := Nat.ceil (threshold t' ε) with hn
  have hexp_nonneg : 0 ≤ Real.exp 1 * t' / 2 :=
    div_nonneg (mul_nonneg (Real.exp_pos 1).le ht') (by norm_num)
  have hlog_nonneg : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div hε0).mpr hε1)
  have hT_pos : 0 < threshold t' ε := by
    unfold threshold
    linarith
  have hn_pos : 0 < n := Nat.ceil_pos.mpr hT_pos
  have h1n : 1 ≤ n := by omega
  have hlt : (n : ℝ) < threshold t' ε + 1 := Nat.ceil_lt_add_one hT_pos.le
  have hn_sub : (n : ℝ) - 1 < threshold t' ε := by linarith
  have hcast : ((queryCount n : ℕ) : ℝ) = 4 * ((n : ℝ) - 1) := by
    unfold queryCount
    rw [Nat.cast_mul, Nat.cast_sub h1n]
    norm_num
  have hT_exp : 4 * threshold t' ε =
      2 * Real.exp 1 * t' + 4 * Real.log (1 / ε) + 6 := by
    unfold threshold
    ring
  rw [hcast]
  have hstrict : 4 * ((n : ℝ) - 1) <
      2 * Real.exp 1 * t' + 4 * Real.log (1 / ε) + 6 := by
    calc
      4 * ((n : ℝ) - 1) < 4 * threshold t' ε := by linarith
      _ = 2 * Real.exp 1 * t' + 4 * Real.log (1 / ε) + 6 := hT_exp
  linarith [hstrict]

end Qatlib.Papers.VlasovEqn19.MainResults.QueryComplexityBound
