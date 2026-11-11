/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram

/-!
# Dihedral descent procedures and resource estimates

This module defines the repeated parity trials and recursive `slopeDescent` procedure for
dihedral reflection recovery. Binary slope encodings and window keys connect this procedure to
record pairing.

Insertion sorting, comparison counters, and level budgets provide explicit definitions for the
time, workspace, and failure estimates used by the descent analysis. See [Kuperberg2005] for the
mathematical background.

## Main statements

* `firstAnswer`: repeat trials until a Boolean answer is obtained.
* `slopeDescent`: recover a slope recursively through parity restrictions.
* `descentFailureBound`: accumulate repeated-level failure estimates.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped Classical BigOperators ENNReal

/-- The Boolean digit at position `i` in the canonical representative of a modular slope. -/
def slopeBit (n : ℕ) (s : ZMod (2 ^ n)) (i : ℕ) : Bool :=
  decide (s.val / 2 ^ i % 2 = 1)

/-- The residue formed from the first `n` Boolean digits weighted by powers of two. -/
def slopeOfBits (n : ℕ) (b : ℕ → Bool) : ZMod (2 ^ n) :=
  ((∑ i : Fin n, if b i.val then (2 ^ i.val : ℕ) else 0 : ℕ) : ZMod (2 ^ n))

/-- The ceiling of `sqrt (k - 1)` used as the sieve depth at level `k`. -/
noncomputable def levelWidth (k : ℕ) : ℕ := Nat.ceil (Real.sqrt ((k : ℝ) - 1))

/-- The record budget `24 * 2 ^ (3 * levelWidth k)`. -/
def levelRecords (k : ℕ) : ℕ := 24 * 2 ^ (3 * levelWidth k)

/-- The prescribed source parity trial count at level `k`. -/
def levelTrials (k : ℕ) : ℕ := sourceParityTrials k

/-- The actual dihedral sieve law at the depth `levelWidth k`. -/
noncomputable def levelRun (k : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ k) → S) : PMF (Option Bool) :=
  dihedralSieveActual k (levelWidth k) f

/-- Repeat a law up to the specified number of trials, returning the first Boolean answer or
`none` if every trial fails. -/
noncomputable def firstAnswer : ℕ → PMF (Option Bool) → PMF (Option Bool)
  | 0, _ => pure none
  | r + 1, p =>
    p.bind fun o =>
      match o with
      | some b => pure (some b)
      | none => firstAnswer r p

/-- Repeat the level sieve law for `levelTrials k` attempts using `firstAnswer`. -/
noncomputable def levelRunTrials (k : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ k) → S) : PMF (Option Bool) :=
  firstAnswer (levelTrials k) (levelRun k f)

/-- Recursively recover a modular slope by repeated parity trials, restriction of the oracle,
and parity lifting, propagating failure as `none`. -/
noncomputable def slopeDescent :
    (k : ℕ) → (S : Type) → [Fintype S] → [DecidableEq S] → [AddCommGroup S] →
      (f : DihedralReg (2 ^ k) → S) → PMF (Option (ZMod (2 ^ k)))
  | 0, _, _, _, _, _ => pure (some 0)
  | 1, _, _, _, _, f =>
    (levelRunTrials 1 f).map fun o => o.map fun b => (if b then (1 : ZMod 2) else 0)
  | k + 2, S, _, _, _, f =>
    (levelRunTrials (k + 2) f).bind fun o =>
      match o with
      | none => pure none
      | some b =>
        (slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b)).map fun o =>
          o.map fun t => parityLift (k + 1) b t

/-- Extract the `w`-bit window beginning at position `t` from a label's canonical
representative. -/
def windowKey (n w t : ℕ) (k : ZMod (2 ^ n)) : ℕ := (k.val / 2 ^ t) % 2 ^ w

/-- Insert an entry before the first entry whose key is at least its key, or append it at the
end. -/
def insertByKey {α : Type} (key : α → ℕ) (a : α) : List α → List α
  | [] => [a]
  | b :: rest => if key a ≤ key b then a :: b :: rest else b :: insertByKey key a rest

/-- Sort a list by repeatedly inserting entries according to their natural number keys. -/
def sortRecords {α : Type} (key : α → ℕ) : List α → List α
  | [] => []
  | r :: rest => insertByKey key r (sortRecords key rest)

/-- A list has nondecreasing keys at consecutive entries. -/
def sortedByKey {α : Type} (key : α → ℕ) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => key a ≤ key b ∧ sortedByKey key (b :: rest)

/-- Count the key comparisons performed by insertion into the given list. -/
def insertCompareCount {α : Type} (key : α → ℕ) (a : α) : List α → ℕ
  | [] => 0
  | b :: rest => if key a ≤ key b then 1 else 1 + insertCompareCount key a rest

/-- Count key comparisons in the recursive insertion sort of the given list. -/
def sortCompareCount {α : Type} (key : α → ℕ) : List α → ℕ
  | [] => 0
  | r :: rest =>
    insertCompareCount key r (sortRecords key rest) + sortCompareCount key rest

/-- Scan consecutive entries, pairing equal keys and advancing past an unmatched head otherwise. -/
def sortedPairs {α : Type} (key : α → ℕ) : List α → List (α × α)
  | a :: b :: rest =>
    if key a = key b then (a, b) :: sortedPairs key rest
    else sortedPairs key (b :: rest)
  | _ => []

/-- The sorting time estimate `R * R * (k + 1) + R * (k + 1)`. -/
def sortBitTime (k R : ℕ) : ℕ := R * R * (k + 1) + R * (k + 1)

/-- The sorting workspace estimate `R * k`. -/
def sortSpace (k R : ℕ) : ℕ := R * k

/-- Sum the repeated record budgets over levels one through `n`. -/
def descentRecords (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, levelTrials k * levelRecords k

/-- Sum the sorting time estimates for the repeated record budgets over levels one through `n`. -/
def descentBitTime (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, sortBitTime k (levelTrials k * levelRecords k)

/-- The maximum sorting workspace estimate over levels one through `n`. -/
def descentSpace (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup fun k => sortSpace k (levelTrials k * levelRecords k)

/-- The exponential sieve success expression minus the designated top-bit correction term. -/
noncomputable def levelSuccessBound (k : ℕ) : ℝ :=
  (1 - Real.exp (-(2 : ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k -
    (2 : ℝ) ^ (-((2 ^ levelWidth k : ℕ) : ℝ))

/-- The base-level repeated failure expression plus the sum of repeated failure estimates for
levels two through `n`. -/
noncomputable def descentFailureBound (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(24 * levelTrials 1 : ℝ)) +
    ∑ k ∈ Finset.Icc 2 n, (1 - max 0 (levelSuccessBound k)) ^ levelTrials k

end Qatlib.Concepts.HspRecovery.RecordExtract
