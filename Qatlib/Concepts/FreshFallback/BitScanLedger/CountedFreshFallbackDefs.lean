/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshFallback.BitScanLedger.ClassicalOracleWitnessBounds
import Mathlib.Data.List.FinRange
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.FreshFallback.BitScanLedger
open Qatlib.Concepts.FreshFallback.BitScanLedger

def compareBits {n : ℕ} (x y : Reg n) : List (Fin n) → Bool × ℕ
  | [] => (true, 0)
  | i :: rest =>
      let r := compareBits x y rest
      (decide (x i = y i) && r.1, r.2 + 2)

def compareWord {n : ℕ} (x y : Reg n) : Bool × ℕ :=
  compareBits x y (List.finRange n)

def memberScan {n : ℕ} (x : Reg n) : List (Reg n) → Bool × ℕ
  | [] => (false, 0)
  | y :: hist =>
      let a := compareWord x y
      if a.1 then (true, a.2)
      else let r := memberScan x hist; (r.1, a.2 + r.2)

def firstFreshScan {n : ℕ} (hist : List (Reg n)) :
    List (Reg n) → Option (Reg n) × ℕ
  | [] => (none, 0)
  | x :: candidates =>
      let a := memberScan x hist
      if a.1 then let r := firstFreshScan hist candidates; (r.1, a.2 + r.2)
      else (some x, a.2)

def runFallback (n : ℕ) (hist : List (Reg n)) (x : Reg n) :
    (Option (Reg n) × ℕ) × ℕ :=
  let a := memberScan x hist
  if a.1 then
    let candidates := binaryPrefixCounted n (hist.length + 1)
    let r := firstFreshScan hist candidates.1
    ((r.1, a.2 + r.2), candidates.2)
  else ((some x, a.2), 0)

end Qatlib.Concepts.FreshFallback.BitScanLedger
