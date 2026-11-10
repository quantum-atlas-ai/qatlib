/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm.Theorem31

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped BigOperators

theorem theorem31_sieve_program : DihedralSieveAlgorithm :=
  dihedralSieveAlgorithm

theorem theorem31_ideal_hit (n m : ℕ) (hn : 2 ≤ n)
    (hm : m = Nat.ceil (Real.sqrt (n - 1))) :
    ENNReal.ofReal ((1 - Real.exp (-(2 : ℝ) ^ ((m : ℝ) / 3 - 2))) ^ m) ≤
      ∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
          then ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L
          else 0 :=
  dihedralSieveIdealHit n m hn hm

end Qatlib.Concepts.HspRecovery.SieveAlgorithm.Theorem31
