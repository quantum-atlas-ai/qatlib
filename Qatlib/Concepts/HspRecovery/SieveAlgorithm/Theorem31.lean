/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge

/-!
# Dihedral sieve theorem interface

This module exposes the dihedral sieve algorithm and its explicit ideal half-period hit estimate
through `theorem31_sieve_program` and `theorem31_ideal_hit`. It packages results for the
dihedral hidden subgroup sieve of [Kuperberg2005], with the hit estimate specialized to `n ≥ 2`
and `m = ceil(sqrt(n-1))`.

## Main statements

* `theorem31_sieve_program`: the dihedral sieve algorithm specification.
* `theorem31_ideal_hit`: the explicit ideal half-period hit lower bound.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm.Theorem31

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped BigOperators

/-- The formal dihedral sieve satisfies `DihedralSieveAlgorithm`, packaging the algorithmic
result associated with [Kuperberg2005]. -/
theorem theorem31_sieve_program : DihedralSieveAlgorithm :=
  dihedralSieveAlgorithm

/-- For `n ≥ 2` and `m = ceil(sqrt(n-1))`, the ideal sieve's half-period hit probability is at
least `(1-exp(-2^(m/3-2)))^m` [Kuperberg2005]. -/
theorem theorem31_ideal_hit (n m : ℕ) (hn : 2 ≤ n)
    (hm : m = Nat.ceil (Real.sqrt (n - 1))) :
    ENNReal.ofReal ((1 - Real.exp (-(2 : ℝ) ^ ((m : ℝ) / 3 - 2))) ^ m) ≤
      ∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
          then ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L
          else 0 :=
  dihedralSieveIdealHit n m hn hm

end Qatlib.Concepts.HspRecovery.SieveAlgorithm.Theorem31
