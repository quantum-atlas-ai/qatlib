/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieve
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm

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
