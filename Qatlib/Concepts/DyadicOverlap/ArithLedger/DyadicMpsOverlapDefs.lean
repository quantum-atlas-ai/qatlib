/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicOverlap.OverlapContract.DyadicMpsOverlap
import Mathlib.Data.Nat.Log
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.DyadicOverlap.OverlapContract
open Qatlib.Concepts.DyadicProgram.DyadicContract

set_option autoImplicit false

namespace Qatlib.Concepts.DyadicOverlap.ArithLedger

open Matrix
open scoped BigOperators
open Qatlib.Concepts.DyadicProgram.DyadicContract (GI add mul run)

def widthBoundNext (n d D w : ℕ) : ℕ :=
  n * (2 * w + 2 + 2 * Nat.clog 2 (D + 1) + Nat.clog 2 (d + 1))

def magnitudeBoundNext (n d D w : ℕ) : ℕ := 2 ^ widthBoundNext n d D w

def intBitWidth (z : ℤ) : ℕ := if z.natAbs = 0 then 0 else Nat.log 2 z.natAbs + 1

def eventBitWidth (e : Ev) : ℕ :=
  max (intBitWidth e.a) (max (intBitWidth e.b) (intBitWidth e.r))

def transferPrefix {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) (k : ℕ) : GI :=
  ((List.ofFn fun s : Fin d => mul (conjGI (A s a a')) (B s b b')).take k).foldl
    add ((0, 0) : GI)

def rowPrefix {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI)
    (j : Fin n) (jj : Fin (Da * Db)) (k : ℕ) : GI :=
  let xs := List.ofFn fun i : Fin (Da * Db) =>
    mul ((run ((transferList A B).take (j : ℕ))) i) (transferMat (A j) (B j) i jj)
  (xs.take k).foldl add ((0, 0) : GI)

def clause3StatementNext : Prop :=
  ∀ (n d Da Db w : ℕ) [NeZero Da] [NeZero Db]
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI),
    (hA : ∀ (i : Fin n) (s : Fin d) (a a' : Fin Da),
      (A i s a a').1.natAbs ≤ 2 ^ w ∧ (A i s a a').2.natAbs ≤ 2 ^ w) →
    (hB : ∀ (i : Fin n) (s : Fin d) (b b' : Fin Db),
      (B i s b b').1.natAbs ≤ 2 ^ w ∧ (B i s b b').2.natAbs ≤ 2 ^ w) →
    (overlapTrace A B).1 = overlapProgram A B
    ∧ logWF (overlapTrace A B).2
    ∧ (constructionEv A B).length ≤ constructionBound n d Da Db
    ∧ (runEv (transferList A B)).length ≤ rowBound n Da Db
    ∧ (overlapTrace A B).2.length ≤ eventBound n d Da Db
    ∧ (∀ D : ℕ, Da ≤ D → Db ≤ D →
        (constructionEv A B).length ≤ 12 * n * d * D ^ 4
        ∧ (runEv (transferList A B)).length ≤ 12 * n * D ^ 4)
    ∧ (∀ D : ℕ, Da ≤ D → Db ≤ D →
        logBounded (magnitudeBoundNext n d D w) (overlapTrace A B).2
        ∧ (∀ (i : Fin n) (a a' : Fin Da) (b b' : Fin Db),
            BoundedGI (magnitudeBoundNext n d D w) (transferEntry (A i) (B i) a a' b b'))
        ∧ (∀ (i : Fin n) (a a' : Fin Da) (b b' : Fin Db) (k : ℕ), k ≤ d →
            BoundedGI (magnitudeBoundNext n d D w)
              (transferPrefix (A i) (B i) a a' b b' k))
        ∧ (∀ j : Fin (Da * Db), BoundedGI (magnitudeBoundNext n d D w) (run (transferList A B) j))
        ∧ (∀ (j : Fin n) (jj : Fin (Da * Db)) (k : ℕ), k ≤ Da * Db →
            BoundedGI (magnitudeBoundNext n d D w) (rowPrefix A B j jj k))
        ∧ BoundedGI (magnitudeBoundNext n d D w) (overlapProgram A B)
        ∧ (∀ e ∈ (overlapTrace A B).2, eventBitWidth e ≤ widthBoundNext n d D w + 1))
    ∧ (n = 0 → overlapTrace A B = (((1, 0) : GI), []))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A B = ((0, 0) : GI))

end Qatlib.Concepts.DyadicOverlap.ArithLedger
