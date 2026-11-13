/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# Radix sieve progress and resource ledgers

This module exposes arithmetic and resource-ledger statements for the radix sieve associated
with Algorithm 3 of [Kuperberg2005]. The declarations describe final radix labels, greedy
progress, coverage by the digit schedule, and the existence of ledgers satisfying explicit query
and bit-operation bounds.

## Main statements

* `algorithm3_greedy_progress`: divisibility of a suitable label difference forces greedy
  progress.
* `algorithm3_schedule_covers`: digit and width schedules have the prescribed length.
* `algorithm3_radix_ledger_endpoint`: existence of a ledger with a subexponential query bound
  and a bit-operation bound.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm3

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

/-- For `r ≥ 2` and `n ≥ 1`, a label below `r^n` divisible by `r^(n - 1)` is `b * r^(n - 1)` for
some digit `b < r`. -/
theorem algorithm3_final_label (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n)
    (h : r ^ (n - 1) ∣ k) :
    ∃ b : ℕ, b < r ∧ k = b * r ^ (n - 1) :=
  radixFinalLabel r n k hr hn hk h

/-- Two distinct ordered labels in the minimum-alpha sublist whose difference is divisible by
`r^(radixMinAlpha r L + 1)` force the greedy value to be at least `radixMinAlpha r L + 1`,
under the stated base and label bounds. -/
theorem algorithm3_greedy_progress (r N : ℕ) (hr : 2 ≤ r) (L : List ℕ) (k ℓ : ℕ)
    (hk : k ∈ radixMinAlphaSublist r L) (hl : ℓ ∈ radixMinAlphaSublist r L)
    (hne : k ≠ ℓ) (hlt : ℓ < k) (hkN : k < N) (hlN : ℓ < N)
    (h : r ^ (radixMinAlpha r L + 1) ∣ k - ℓ) :
    radixGreedyValue r N L ≥ radixMinAlpha r L + 1 :=
  radixGreedy_progress r N hr L k ℓ hk hl hne hlt hkN hlN h

/-- The greedy radix value bounds the value of every pair in the radix pairing list of the
minimum-alpha sublist. -/
theorem algorithm3_greedy_value_ge (r N : ℕ) (L : List ℕ) (k ℓ : ℕ)
    (h : (k, ℓ) ∈ radixPairs (radixMinAlphaSublist r L)) :
    radixPairValue r N k ℓ ≤ radixGreedyValue r N L :=
  radixGreedyValue_ge r N L k ℓ h

/-- The radix digit and width lists both have length `radixDigitCount r N`, and the first width
with default zero equals that count. -/
theorem algorithm3_schedule_covers (r N : ℕ) [NeZero N] (s : ZMod N) :
    (radixDigits r N s).length = radixDigitCount r N ∧
      (radixWidths r N).length = radixDigitCount r N ∧
      (radixWidths r N).getD 0 0 = radixDigitCount r N :=
  clause14_radix_schedule_covers r N s

/-- For base `r ≥ 2` and modulus `N ≥ 1`, the radix digit count is large enough that `N ≤ r ^
radixDigitCount r N`. -/
theorem algorithm3_digit_count_covers (r N : ℕ) (hr : 2 ≤ r) (hN : 1 ≤ N) :
    N ≤ r ^ radixDigitCount r N :=
  clause14_radix_digit_count_pow r N hr hN

/-- For each base `r ≥ 2`, there is a positive constant and a recovery ledger for every `n ≥ 1`
satisfying the stated sample, sorting, workspace, query, and bit-operation bounds for the
radix sieve of [Kuperberg2005]. -/
theorem algorithm3_radix_ledger_endpoint (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ lg : RecoveryLedger,
      lg.samples ≤ lg.queries ∧
      sortCompareSteps lg.samples ≤ lg.comparisons ∧
      sortBitOps lg.samples lg.integerBits ≤ lg.bitOps ∧
      0 < lg.workspaceBits ∧
      ((lg.queries : ℝ) ≤ C * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) ∧
      ((lg.bitOps : ℝ) ≤ C * (lg.queries : ℝ) *
        (Real.log ((lg.queries : ℝ) + 2)) ^ 4) := by
  refine ⟨radixBudgetConstant r,
    lt_of_lt_of_le zero_lt_one (radix_budgetConstant_pos r (by omega)), ?_⟩
  intro n hn
  exact ⟨radixRecursionLedger r n, radixRecursionLedger_budget r n hr hn⟩

end Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm3
