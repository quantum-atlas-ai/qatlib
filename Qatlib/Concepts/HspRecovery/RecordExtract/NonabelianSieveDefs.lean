/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped Classical BigOperators ENNReal

def slopeBit (n : ℕ) (s : ZMod (2 ^ n)) (i : ℕ) : Bool :=
  decide (s.val / 2 ^ i % 2 = 1)

def slopeOfBits (n : ℕ) (b : ℕ → Bool) : ZMod (2 ^ n) :=
  ((∑ i : Fin n, if b i.val then (2 ^ i.val : ℕ) else 0 : ℕ) : ZMod (2 ^ n))

noncomputable def levelWidth (k : ℕ) : ℕ := Nat.ceil (Real.sqrt ((k : ℝ) - 1))

def levelRecords (k : ℕ) : ℕ := 24 * 2 ^ (3 * levelWidth k)

def levelTrials (k : ℕ) : ℕ := sourceParityTrials k

noncomputable def levelRun (k : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ k) → S) : PMF (Option Bool) :=
  dihedralSieveActual k (levelWidth k) f

noncomputable def firstAnswer : ℕ → PMF (Option Bool) → PMF (Option Bool)
  | 0, _ => pure none
  | r + 1, p =>
    p.bind fun o =>
      match o with
      | some b => pure (some b)
      | none => firstAnswer r p

noncomputable def levelRunTrials (k : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ k) → S) : PMF (Option Bool) :=
  firstAnswer (levelTrials k) (levelRun k f)

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

def windowKey (n w t : ℕ) (k : ZMod (2 ^ n)) : ℕ := (k.val / 2 ^ t) % 2 ^ w

def insertByKey {α : Type} (key : α → ℕ) (a : α) : List α → List α
  | [] => [a]
  | b :: rest => if key a ≤ key b then a :: b :: rest else b :: insertByKey key a rest

def sortRecords {α : Type} (key : α → ℕ) : List α → List α
  | [] => []
  | r :: rest => insertByKey key r (sortRecords key rest)

def sortedByKey {α : Type} (key : α → ℕ) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => key a ≤ key b ∧ sortedByKey key (b :: rest)

def insertCompareCount {α : Type} (key : α → ℕ) (a : α) : List α → ℕ
  | [] => 0
  | b :: rest => if key a ≤ key b then 1 else 1 + insertCompareCount key a rest

def sortCompareCount {α : Type} (key : α → ℕ) : List α → ℕ
  | [] => 0
  | r :: rest =>
    insertCompareCount key r (sortRecords key rest) + sortCompareCount key rest

def sortedPairs {α : Type} (key : α → ℕ) : List α → List (α × α)
  | a :: b :: rest =>
    if key a = key b then (a, b) :: sortedPairs key rest
    else sortedPairs key (b :: rest)
  | _ => []

def sortBitTime (k R : ℕ) : ℕ := R * R * (k + 1) + R * (k + 1)

def sortSpace (k R : ℕ) : ℕ := R * k

def descentRecords (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, levelTrials k * levelRecords k

def descentBitTime (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, sortBitTime k (levelTrials k * levelRecords k)

def descentSpace (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup fun k => sortSpace k (levelTrials k * levelRecords k)

noncomputable def levelSuccessBound (k : ℕ) : ℝ :=
  (1 - Real.exp (-(2 : ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k -
    (2 : ℝ) ^ (-((2 ^ levelWidth k : ℕ) : ℝ))

noncomputable def descentFailureBound (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(24 * levelTrials 1 : ℝ)) +
    ∑ k ∈ Finset.Icc 2 n, (1 - max 0 (levelSuccessBound k)) ^ levelTrials k

end Qatlib.Concepts.HspRecovery.RecordExtract
