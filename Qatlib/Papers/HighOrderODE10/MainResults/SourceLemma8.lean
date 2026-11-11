/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Lemma 8: state-preparation cost

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Lemma 8 and its proof,
p. 9–10, Eq. (56).

The paper prepares `|~b⟩ ∝ ∑_{j,ℓ} b_j^{[ℓ]} |j,ℓ⟩` in three registers
(time-range qubit, remaining time register, and the `N_x`-dimensional data
register).  The proof decomposes the cost as:

* an `s`-sparse state in dimension `s` costs `O(√s)` (Grover, Ref. [25];
  the oracle form of Eq. (30) from Ref. [8] makes the `s`-sparse preparation
  cost `O(√s)` as well), applied to both the `b` and the `x_in` branches, whose
  controlled preparation is charged `O(√s)` each;
* the uniform superposition of `N_t/2` times costs `O(log N_t)` (choose `N_t`
  a power of two);
* normalisations of `x_in` and `b` are known (cost `O(s)`, paid once).

Adding the three ledger entries gives `O(√s + log N_t)`.  The theorem below
performs exactly this addition: `h_b`, `h_xin`, `h_time` are the three cited
cost bounds and the witness is `C_b + C_x + C_t`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

/-- **Lemma 8** (Berry, arXiv:1010.2745v2, p. 9–10, Eq. (56)).
If the `b`-register, the `x_in`-register and the time-superposition register of
the Eq. (56) state preparation respectively cost at most `C_b √s`, `C_x √s`
and `C_t log N_t` oracle calls (the cited Ref. [25] / Ref. [8] bounds), then
the whole preparation costs `O(√s + log N_t)` calls.

`L` is the three-register call ledger, `s` the sparsity, `N_t` the number of
time steps (taken as a power of two in the paper). -/
theorem lemma8_statePreparationCost
    (L : SourcePrepLedger) (s Nt Cb Cx Ct : ℝ)
    (hs : 0 ≤ s) (hNt : 1 ≤ Nt)
    (hCb : 0 < Cb) (hCx : 0 ≤ Cx) (hCt : 0 < Ct)
    (hb : (L.bCalls : ℝ) ≤ Cb * Real.sqrt s)
    (hxin : (L.xinCalls : ℝ) ≤ Cx * Real.sqrt s)
    (htime : (L.timeCalls : ℝ) ≤ Ct * Real.log Nt) :
    ∃ C : ℝ, 0 < C ∧ (L.total : ℝ) ≤ C * sourcePrepCostExpr s Nt := by
  refine ⟨Cb + Cx + Ct, by linarith, ?_⟩
  have hsqrt : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hlog : 0 ≤ Real.log Nt := Real.log_nonneg hNt
  have htot : (L.total : ℝ) = (L.bCalls : ℝ) + (L.xinCalls : ℝ) + (L.timeCalls : ℝ) := by
    unfold SourcePrepLedger.total
    push_cast
    ring
  rw [htot]
  unfold sourcePrepCostExpr
  have h1 : (L.xinCalls : ℝ) ≤ Cx * Real.sqrt s := hxin
  have h2 : (L.timeCalls : ℝ) ≤ Ct * Real.log Nt := htime
  have hsum : Cb * Real.sqrt s + Cx * Real.sqrt s + Ct * Real.log Nt ≤
      (Cb + Cx + Ct) * (Real.sqrt s + Real.log Nt) := by
    have hnonneg1 : 0 ≤ Real.sqrt s := hsqrt
    have hnonneg2 : 0 ≤ Real.log Nt := hlog
    have hCx' : 0 ≤ Cx := hCx
    nlinarith [mul_nonneg hCx' hnonneg2, mul_nonneg (le_of_lt hCb) hnonneg2,
      mul_nonneg (le_of_lt hCt) hnonneg1]
  linarith

end Qatlib.Papers.HighOrderODE10.MainResults
