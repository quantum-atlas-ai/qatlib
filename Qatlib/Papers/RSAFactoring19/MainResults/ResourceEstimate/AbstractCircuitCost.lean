/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Abstract circuit model cost estimate (Eqs. (1)--(3), Table 1)

Source: Gidney--Ekerå, *How to factor 2048 bit RSA integers in 8 hours using
20 million noisy qubits*, arXiv:1905.09749v3 (13 Apr 2021), abstract, Table 1,
§2.8 Eqs. (1)--(3) (p. 9), §2.11 Eq. (5).

Fixed version: v3 (PDF header `arXiv:1905.09749v3 [quant-ph] 13 Apr 2021`),
accepted Quantum 2021-03-29.

Claim c002 (abstract + Table 1 row `(ours) 2019`): *in the abstract circuit
model (which ignores overheads from distillation, routing, and error
correction) the construction uses `3n + 0.002 n lg n` logical qubits,
`0.3n³ + 0.0005 n³ lg n` Toffolis, and `500n² + n² lg n` measurement depth to
factor `n`-bit RSA integers.*

This file formalises the paper's own leading-order cost model:

* `lookupAdditionCount` — Eq. (1) after its `→` simplification, at the
  recommended parameters `c_exp = c_mul = 5`, `c_sep = 1024`
  (`(2n n_e / 25) · (1025/1024)`, dropping the stated lower-order
  `O(n_e lg n)` term);
* `toffoliPerLookupAddition` — Eq. (2), `2n + n c_pad / c_sep + 2^{c_exp+c_mul}`;
* `measurementDepthPerLookupAddition` — Eq. (3),
  `2c_sep + 2c_pad + 2^{c_exp+c_mul}`;
* `cpad` — the paper's `2 lg n + lg n_e + 10`;
* `exponentQubits` — the paper's choice `n_e = 3n/2` used to instantiate the
  abstract formulas;
* `logicalQubits` — the three `n`-qubit registers plus the runway/padding
  overhead `(n/c_sep)·2 lg n`.

We prove that for `n ≥ 2048` (the paper's target size) these exact
leading-order expressions satisfy the abstract's asymptotic upper bounds, and
that at `n = 2048`, `n_e = 3072` the Toffoli count is at most the Table 1
entry of 2.7 billion.  The bounds are honest upper bounds in the paper's own
leading-order accounting: the `O(n_e lg n)` term of Eq. (1) and the
`O(1)` terms of Eqs. (2)--(3) (uncompute, ancillae) are exactly the terms the
paper explicitly drops.  A fully rigorous accounting would need the
`O(n_e lg n)` term as a lower-order additive cost; bounding it away would
require the concrete layout constants that the paper defers to the ancillary
`estimate costs.py`, so we follow the paper's stated simplification.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RSAFactoring19.MainResults.ResourceEstimate

/-! ### Definitions from Eqs. (1)--(3) -/

/-- Base-2 logarithm, written `lg` in the paper. -/
def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- The recommended exponent window size `c_exp = 5` (§2.8). -/
def cexp : ℕ := 5

/-- The recommended multiplication window size `c_mul = 5` (§2.8). -/
def cmul : ℕ := 5

/-- The recommended runway separation `c_sep = 1024` (§2.8). -/
def csep : ℕ := 1024

/-- The padding / runway length `c_pad = 2 lg n + lg n_e + 10` (§2.8). -/
def cpad (n ne : ℝ) : ℝ := 2 * lg n + lg ne + 10

/-- Eq. (1) after its `→` simplification, at `c_exp = c_mul = 5`:
`LookupAdditionCount(n, n_e) = (2n n_e/25)·(1025/1024)`. -/
def lookupAdditionCount (n ne : ℝ) : ℝ := (2 * n * ne / 25) * (1025 / 1024)

/-- Eq. (2): Toffoli count of a lookup addition, `2n + n c_pad/c_sep + 2^{c_exp+c_mul}`
(ignoring the negligible uncomputation cost, as the paper does). -/
def toffoliPerLookupAddition (n ne : ℝ) : ℝ :=
  2 * n + n * cpad n ne / 1024 + 1024

/-- Eq. (3): measurement depth of a lookup addition,
`2c_sep + 2c_pad + 2^{c_exp+c_mul}`. -/
def measurementDepthPerLookupAddition (n ne : ℝ) : ℝ :=
  2048 + 2 * cpad n ne + 1024

/-- Eq. (2) as a total: lookup-addition count times per-addition Toffoli count. -/
def toffoliCount (n ne : ℝ) : ℝ :=
  lookupAdditionCount n ne * toffoliPerLookupAddition n ne

/-- Eq. (3) as a total: lookup-addition count times per-addition measurement depth. -/
def measurementDepth (n ne : ℝ) : ℝ :=
  lookupAdditionCount n ne * measurementDepthPerLookupAddition n ne

/-- The paper's instantiation `n_e = 3n/2` for the abstract cost formulas. -/
def exponentQubits (n : ℝ) : ℝ := 3 * n / 2

/-- Logical qubit budget of the abstract circuit model: three `n`-qubit registers
(`3n`) plus the `O(lg n)` coset/runway overhead, which the paper reports as
`0.002 n lg n` (one runway set of length `2 lg n` at spacing `c_sep = 1024`
gives `(2/1024) n lg n = 0.001953 n lg n`, so `0.002` is a valid bound). -/
def logicalQubits (n : ℝ) : ℝ := 3 * n + (n / 1024) * (2 * lg n)

/-! ### Basic lemmas -/

/-- `lg n ≥ 11` for `n ≥ 2048` (since `2048 = 2^11`). -/
theorem lg_ge_eleven {n : ℝ} (hn : 2048 ≤ n) : 11 ≤ lg n := by
  have h1 : Real.logb 2 (2048 : ℝ) = 11 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [show (11 : ℝ) = Real.logb 2 (2048 : ℝ) from h1.symm, lg]
  exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hn

/-- With `n_e = 3n/2`, the padding length is at most `3 lg n + 11`
(since `lg(3n/2) ≤ lg(2n) = 1 + lg n` for `n > 0`). -/
theorem cpad_le {n : ℝ} (hn : 0 < n) :
    cpad n (exponentQubits n) ≤ 3 * lg n + 11 := by
  unfold cpad exponentQubits lg
  have h1 : Real.logb 2 (3 * n / 2) ≤ Real.logb 2 (2 * n) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (by linarith)
  have h2 : Real.logb 2 (2 * n) = 1 + Real.logb 2 n := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt hn), Real.logb_self_eq_one (by norm_num)]
  linarith

/-- With `n_e = 3n/2`, Eq. (1) collapses to `(3075/25600) n²`. -/
theorem lookupAdditionCount_eq (n : ℝ) :
    lookupAdditionCount n (exponentQubits n) = (3075 / 25600 : ℝ) * n ^ 2 := by
  unfold lookupAdditionCount exponentQubits
  ring

/-- `LookupAdditionCount ≈ 0.1 n_e n` (Eq. (1)), instantiated at `n_e = 3n/2`. -/
theorem lookupAdditionCount_le (n : ℝ) :
    lookupAdditionCount n (exponentQubits n) ≤ 0.1 * exponentQubits n * n := by
  rw [lookupAdditionCount_eq]
  unfold exponentQubits
  nlinarith [sq_nonneg n]

/-! ### The abstract's three asymptotic bounds -/

/-- **c002, Toffoli count.**  For `n ≥ 2048`, the Eq. (2) Toffoli count is at
most `0.3n³ + 0.0005n³ lg n`. -/
theorem toffoliCount_le (n : ℝ) (hn : 2048 ≤ n) :
    toffoliCount n (exponentQubits n) ≤ 0.3 * n ^ 3 + 0.0005 * n ^ 3 * lg n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 11 ≤ lg n := lg_ge_eleven hn
  have hcpad := cpad_le hn0
  have hK := lookupAdditionCount_eq n
  have htoff : toffoliPerLookupAddition n (exponentQubits n) ≤
      2 * n + n * (3 * lg n + 11) / 1024 + 1024 := by
    unfold toffoliPerLookupAddition
    have h : n * cpad n (exponentQubits n) / 1024 ≤ n * (3 * lg n + 11) / 1024 := by
      gcongr
    linarith
  have hKL : 0 ≤ (3075 / 25600 : ℝ) * n ^ 2 := by positivity
  calc toffoliCount n (exponentQubits n)
      = lookupAdditionCount n (exponentQubits n) *
          toffoliPerLookupAddition n (exponentQubits n) := rfl
    _ ≤ ((3075 / 25600 : ℝ) * n ^ 2) * (2 * n + n * (3 * lg n + 11) / 1024 + 1024) := by
        rw [hK]
        exact mul_le_mul_of_nonneg_left htoff hKL
    _ ≤ 0.3 * n ^ 3 + 0.0005 * n ^ 3 * lg n := by
        nlinarith [hn, hL, mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ lg n),
          sq_nonneg n, mul_nonneg (sq_nonneg n) (by linarith : (0:ℝ) ≤ lg n)]

/-- **c002, measurement depth.**  For `n ≥ 2048`, the Eq. (3) measurement depth
is at most `500n² + n² lg n`. -/
theorem measurementDepth_le (n : ℝ) (hn : 2048 ≤ n) :
    measurementDepth n (exponentQubits n) ≤ 500 * n ^ 2 + n ^ 2 * lg n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 11 ≤ lg n := lg_ge_eleven hn
  have hcpad := cpad_le hn0
  have hK := lookupAdditionCount_eq n
  have hdepth : measurementDepthPerLookupAddition n (exponentQubits n) ≤
      6 * lg n + 3094 := by
    unfold measurementDepthPerLookupAddition
    linarith
  have hKL : 0 ≤ (3075 / 25600 : ℝ) * n ^ 2 := by positivity
  calc measurementDepth n (exponentQubits n)
      = lookupAdditionCount n (exponentQubits n) *
          measurementDepthPerLookupAddition n (exponentQubits n) := rfl
    _ ≤ ((3075 / 25600 : ℝ) * n ^ 2) * (6 * lg n + 3094) := by
        rw [hK]
        exact mul_le_mul_of_nonneg_left hdepth hKL
    _ ≤ 500 * n ^ 2 + n ^ 2 * lg n := by
        nlinarith [hn, hL, mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ lg n),
          sq_nonneg n]

/-- **c002, logical qubits.**  For `n ≥ 1`, the register-plus-padding budget is
at most the abstract's `3n + 0.002 n lg n`. -/
theorem logicalQubits_le (n : ℝ) (hn : 1 ≤ n) :
    logicalQubits n ≤ 3 * n + 0.002 * n * lg n := by
  have hL0 : 0 ≤ lg n := by
    have hmono : lg 1 ≤ lg n := by
      unfold lg
      exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hn
    simpa [lg, Real.logb_one] using hmono
  have hcoef : (2 / 1024 : ℝ) ≤ 0.002 := by norm_num
  have hnn : 0 ≤ n * lg n := mul_nonneg (by linarith) hL0
  calc logicalQubits n
      = 3 * n + (2 / 1024) * (n * lg n) := by
        unfold logicalQubits
        ring
    _ ≤ 3 * n + 0.002 * (n * lg n) := by gcongr
    _ = 3 * n + 0.002 * n * lg n := by ring

/-- **c002 (abstract circuit model cost).**  For every `n ≥ 2048`, the
construction's Eq. (1)--(3) leading-order cost model satisfies all three
asymptotic bounds stated in the abstract and Table 1. -/
theorem abstractCircuitCost_bounds (n : ℝ) (hn : 2048 ≤ n) :
    toffoliCount n (exponentQubits n) ≤ 0.3 * n ^ 3 + 0.0005 * n ^ 3 * lg n ∧
      measurementDepth n (exponentQubits n) ≤ 500 * n ^ 2 + n ^ 2 * lg n ∧
      logicalQubits n ≤ 3 * n + 0.002 * n * lg n :=
  ⟨toffoliCount_le n hn, measurementDepth_le n hn,
    logicalQubits_le n (by linarith)⟩

/-! ### Consistency with Table 1 at `n = 2048` -/

/-- `lg 3072 ≤ 12` (since `3072 ≤ 4096 = 2^12`), so `c_pad(2048, 3072) ≤ 44`. -/
theorem cpad_2048_le : cpad 2048 3072 ≤ 44 := by
  unfold cpad lg
  have h1 : Real.logb 2 (2048 : ℝ) = 11 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h2 : Real.logb 2 (3072 : ℝ) ≤ 12 := by
    have hmono : Real.logb 2 (3072 : ℝ) ≤ Real.logb 2 (4096 : ℝ) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) (by norm_num)
    have h3 : Real.logb 2 (4096 : ℝ) = 12 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    linarith
  linarith

/-- **Table 1 check.**  At `n = 2048`, `n_e = 3072`, the Eq. (1)--(2) Toffoli
count is at most the Table 1 entry `2.7 · 10⁹` for `(ours) 2019`. -/
theorem toffoliCount_2048_le :
    toffoliCount 2048 3072 ≤ 2700000000 := by
  have hcpad := cpad_2048_le
  have hK : lookupAdditionCount 2048 3072 = 503808 := by
    unfold lookupAdditionCount
    norm_num
  have htoff : toffoliPerLookupAddition 2048 3072 ≤ 5208 := by
    unfold toffoliPerLookupAddition
    have h : 2048 * cpad 2048 3072 / 1024 ≤ 2048 * 44 / 1024 := by gcongr
    linarith
  calc toffoliCount 2048 3072
      = lookupAdditionCount 2048 3072 * toffoliPerLookupAddition 2048 3072 := rfl
    _ = 503808 * toffoliPerLookupAddition 2048 3072 := by rw [hK]
    _ ≤ 503808 * 5208 := by
        exact mul_le_mul_of_nonneg_left htoff (by norm_num)
    _ ≤ 2700000000 := by norm_num

end Qatlib.Papers.RSAFactoring19.MainResults.ResourceEstimate
