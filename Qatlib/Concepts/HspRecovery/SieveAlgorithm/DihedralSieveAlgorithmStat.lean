/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieve

/-!
# Specification of dihedral sieve performance

`DihedralSieveAlgorithm` states the output and resource requirements for the ideal dihedral
parity sieve at `m = Nat.ceil (Real.sqrt (n - 1))`. It formalizes an explicit finite-parameter
success estimate in the setting of Algorithm 1 of [Kuperberg2005].

## Main definitions

* `DihedralSieveAlgorithm`: for `n ≥ 2` and an oracle hiding the slope, incorrect parity outputs
  have zero mass, correct parity has the specified lower bound, and the run has the stated
  resource triple.

## References

* [Kuperberg, Algorithm 1 and Theorem 3.1][Kuperberg2005]
-/

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm

/-- The proposition that for `n ≥ 2` and a hidden-reflection oracle, the ideal sieve with `m =
Nat.ceil (Real.sqrt (n - 1))` never returns an incorrect parity and satisfies the displayed
exponential success lower bound. It also requires the exact attached resource triple `(24 *
2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^ (3 * m) + 1)`. -/
def DihedralSieveAlgorithm : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReflectionHides (N := 2 ^ n) f s →
    let m := Nat.ceil (Real.sqrt (n - 1))
    let run := dihedralSieveRun n m s
    (∀ b : Bool, b ≠ decide (s.val % 2 = 1) → run.1 (some b) = 0) ∧
    ENNReal.ofReal
        ((1 - Real.exp (-(2 : ℝ) ^ ((m : ℝ) / 3 - 2))) ^ m -
          (2 : ℝ) ^ (-((2 ^ m : ℕ) : ℝ))) ≤ run.1 (some (decide (s.val % 2 = 1))) ∧
    run.2 = (24 * 2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^ (3 * m) + 1)

end Qatlib.Concepts.HspRecovery.SieveAlgorithm
