/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# Radix schedules and ledger bounds

This module exposes radix-schedule and resource-ledger results associated with the Theorem 5.1
development of [Kuperberg2005]. It gives matching digit and width schedule lengths, a power
bound covering the modulus, and existence of ledgers satisfying the stated subexponential query
and bit-operation bounds.

## Main statements

* `theorem51_radix_ledger_endpoint`: existence of ledgers with the specified resource bounds.
* `theorem51_digit_count_covers`: the radix digit count covers the modulus.
* `theorem51_schedule_covers`: schedule lengths and the initial width.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Theorem51

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

/-- For each radix at least two, there is a positive constant giving ledgers with the stated
sorting and workspace conditions, query bound `C * 3 ^ sqrt (2 * n) * (n + 1) ^ 4`, and
logarithmic-factor bit-operation bound [Kuperberg2005]. -/
theorem theorem51_radix_ledger_endpoint (r : ℕ) (hr : 2 ≤ r) :
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

/-- The radix digit list and width schedule both have length `radixDigitCount r N`
[Kuperberg2005]. -/
theorem theorem51_radix_schedule (r N : ℕ) [NeZero N] (s : ZMod N) :
    (radixDigits r N s).length = radixDigitCount r N ∧
      (radixWidths r N).length = radixDigitCount r N :=
  clause14_radix_schedule r N s

/-- For radix at least two and positive modulus, raising the radix to `radixDigitCount r N`
gives a number at least `N` [Kuperberg2005]. -/
theorem theorem51_digit_count_covers (r N : ℕ) (hr : 2 ≤ r) (hN : 1 ≤ N) :
    N ≤ r ^ radixDigitCount r N :=
  clause14_radix_digit_count_pow r N hr hN

/-- The radix digit and width lists have the prescribed digit-count length, and the first width,
with default zero, equals that digit count [Kuperberg2005]. -/
theorem theorem51_schedule_covers (r N : ℕ) [NeZero N] (s : ZMod N) :
    (radixDigits r N s).length = radixDigitCount r N ∧
      (radixWidths r N).length = radixDigitCount r N ∧
      (radixWidths r N).getD 0 0 = radixDigitCount r N :=
  clause14_radix_schedule_covers r N s

end Qatlib.Concepts.HspRecovery.OpenSieve.Theorem51
