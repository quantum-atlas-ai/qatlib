/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicOverlap.OverlapContract.DyadicMpsOverlap
import Mathlib.Data.Nat.Log

/-!
# Width envelopes for logged MPS overlaps

`widthBoundNext` and `magnitudeBoundNext` specify uniform envelopes for Gaussian-integer
transfer contractions. `transferPrefix` and `rowPrefix` expose intermediate partial sums, and
`eventBitWidth` measures the operands and result in each arithmetic event. Matrix product state
contractions provide the tensor-network background [Schollwock2011].

`clause3StatementNext` collects agreement of the logged and unlogged overlap computations,
polynomial event counts, uniform magnitude bounds, and explicit empty-chain and
zero-physical-dimension cases.

## Main statements

* `widthBoundNext`: the dimension- and precision-dependent width parameter.
* `transferPrefix`, `rowPrefix`: intermediate contraction sums.
* `clause3StatementNext`: the complete logged-overlap specification.

## References

* [Schollwock, 2011][Schollwock2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.DyadicOverlap.OverlapContract
open Qatlib.Concepts.DyadicProgram.DyadicContract

set_option autoImplicit false

namespace Qatlib.Concepts.DyadicOverlap.ArithLedger

open Matrix
open scoped BigOperators
open Qatlib.Concepts.DyadicProgram.DyadicContract (GI add mul run)

/-- The explicit width parameter for Gaussian-integer overlap computations of length `n` with
physical dimension `d` and bond dimensions bounded by `D`. -/
def widthBoundNext (n d D w : ℕ) : ℕ :=
  n * (2 * w + 2 + 2 * Nat.clog 2 (D + 1) + Nat.clog 2 (d + 1))

/-- The power of two determined by `widthBoundNext`, used as a uniform integer magnitude bound. -/
def magnitudeBoundNext (n d D w : ℕ) : ℕ := 2 ^ widthBoundNext n d D w

/-- The binary length of an integer's absolute value, with width zero for zero. -/
def intBitWidth (z : ℤ) : ℕ := if z.natAbs = 0 then 0 else Nat.log 2 z.natAbs + 1

/-- The maximum integer bit width among the two operands and result of an arithmetic event. -/
def eventBitWidth (e : Ev) : ℕ :=
  max (intBitWidth e.a) (max (intBitWidth e.b) (intBitWidth e.r))

/-- The sum of the first `k` conjugated products used to construct a transfer-matrix entry. -/
def transferPrefix {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) (k : ℕ) : GI :=
  ((List.ofFn fun s : Fin d => mul (conjGI (A s a a')) (B s b b')).take k).foldl
    add ((0, 0) : GI)

/-- The sum of the first `k` terms in the specified row update after the preceding transfer
matrices. -/
def rowPrefix {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI)
    (j : Fin n) (jj : Fin (Da * Db)) (k : ℕ) : GI :=
  let xs := List.ofFn fun i : Fin (Da * Db) =>
    mul ((run ((transferList A B).take (j : ℕ))) i) (transferMat (A j) (B j) i jj)
  (xs.take k).foldl add ((0, 0) : GI)

/-- The combined overlap specification asserting output agreement, valid arithmetic logs,
event-count bounds, uniform magnitude and bit-width bounds, and boundary cases. -/
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
