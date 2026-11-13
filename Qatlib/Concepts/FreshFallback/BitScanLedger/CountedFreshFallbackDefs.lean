/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshFallback.BitScanLedger.ClassicalOracleWitnessBounds
import Mathlib.Data.List.FinRange

/-!
# Fresh fallback with explicit read ledgers

This module defines bitwise comparison, history membership, and first-fresh-candidate scans with
explicit bit-read counters. `runFallback` combines these scans with `binaryPrefixCounted`,
returning a candidate result, a bit-read count, and a generator-visit count.

The definitions supply concrete finite-search costs for the oracle-circuit framework of
[KitaevShenVyalyi2002].

## Main statements

* `compareWord`: compares all bit positions and returns a read count.
* `firstFreshScan`: finds the first candidate absent from the history.
* `runFallback`: combines direct sampling with a counted bounded fallback search.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.FreshFallback.BitScanLedger
open Qatlib.Concepts.FreshFallback.BitScanLedger

/-- Compares two words at the listed addresses, recording two bit reads per address. -/
def compareBits {n : ℕ} (x y : Reg n) : List (Fin n) → Bool × ℕ
  | [] => (true, 0)
  | i :: rest =>
      let r := compareBits x y rest
      (decide (x i = y i) && r.1, r.2 + 2)

/-- Compares two `n`-bit words at every coordinate and returns the comparison result and read
count. -/
def compareWord {n : ℕ} (x y : Reg n) : Bool × ℕ :=
  compareBits x y (List.finRange n)

/-- Scans the history for a word equal to `x`, stopping at the first match and accumulating bit
reads. -/
def memberScan {n : ℕ} (x : Reg n) : List (Reg n) → Bool × ℕ
  | [] => (false, 0)
  | y :: hist =>
      let a := compareWord x y
      if a.1 then (true, a.2)
      else let r := memberScan x hist; (r.1, a.2 + r.2)

/-- Scans candidates for the first word absent from the history and accumulates the membership
scans' bit reads. -/
def firstFreshScan {n : ℕ} (hist : List (Reg n)) :
    List (Reg n) → Option (Reg n) × ℕ
  | [] => (none, 0)
  | x :: candidates =>
      let a := memberScan x hist
      if a.1 then let r := firstFreshScan hist candidates; (r.1, a.2 + r.2)
      else (some x, a.2)

/-- Checks whether the proposed word is fresh and otherwise scans a counted prefix of the binary
alphabet. Returns the optional result with its bit-read and generator-visit counts. -/
def runFallback (n : ℕ) (hist : List (Reg n)) (x : Reg n) :
    (Option (Reg n) × ℕ) × ℕ :=
  let a := memberScan x hist
  if a.1 then
    let candidates := binaryPrefixCounted n (hist.length + 1)
    let r := firstFreshScan hist candidates.1
    ((r.1, a.2 + r.2), candidates.2)
  else ((some x, a.2), 0)

end Qatlib.Concepts.FreshFallback.BitScanLedger
