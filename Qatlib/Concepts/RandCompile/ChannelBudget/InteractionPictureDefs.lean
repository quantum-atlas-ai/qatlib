/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.InteractionPicture
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def ip25CorrectedCutoff (ε : ℝ) : ℕ :=
  Nat.ceil (2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε)))

def ip25DyadicAccuracy (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

def ip25SortingComparators (k : ℕ) : ℕ := k * (Nat.log2 k + 1)

def ip25IndexTransposition {k : ℕ} (i j : Fin k) : Fin k → Fin k :=
  fun p => if p = i then j else if p = j then i else p

def ip25IndexSwap {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) : Fin k → Fin M :=
  fun p => v (ip25IndexTransposition i j p)

def ip25IndexCompare {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) : Fin k → Fin M :=
  if v i ≤ v j then v else ip25IndexSwap i j v

def ip25IndexReverse {M k : ℕ} (v : Fin k → Fin M) : Fin k → Fin M :=
  fun p => v ⟨k - 1 - p.val, by omega⟩

def ip25ReverseGates (k : ℕ) : ℕ := k

def ip26SegmentGateCount (p : EffectiveSegmentParameters) : ℕ :=
  2 * ipSegmentCopies p

def ip27SparseStepCount (p : EffectiveSparseParameters) : ℕ := 3

def ip27SparseWidth (p : EffectiveSparseParameters) : ℕ :=
  p.nd + 2 * p.ns + 2 * p.np

def ip26SegmentQueryRate (k : ℕ) : ℕ := computedDysonCutoff (k + 8)

def ip26TotalQueryRate (L k : ℕ) : ℕ := L * ip26SegmentQueryRate k

def ip26AuxBitRate (L : ℕ) : ℕ := Nat.clog 2 L

noncomputable def ip26NonBinaryRate (ε : ℝ) : ℝ :=
  2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε))

def ip27ProgramQueries (prog : EffectiveProgram) : ℕ :=
  (prog.steps.filter (fun s => match s with
    | EffectiveStep.query _ _ _ _ => true
    | _ => false)).length

def ip27DiagonalGateCount (p : EffectiveSparseParameters) : ℕ := p.nd

def ip27DiagonalQueries (p : EffectiveSparseParameters) : ℕ := 0

def ip27DiagonalProgram (p : EffectiveSparseParameters) : EffectiveProgram :=
  { width := p.nd + 2 * p.ns + 2 * p.np
    steps := (List.range p.nd).map (fun i => EffectiveStep.phase i 1 1 false)
      ++ (ipSparseProgram p).steps }

def ip27DiagonalTotalGates (p : EffectiveSparseParameters) : ℕ :=
  ip27DiagonalGateCount p + (ipSparseProgram p).steps.length

def ip25MergeRun {α : Type} (le : α → α → Bool) (off : ℕ) (fuel : ℕ)
    (res a b : List α) : List α × List (ℕ × ℕ) :=
  match fuel with
  | 0 => (res ++ a ++ b, [])
  | fuel + 1 =>
    match a, b with
    | [], b => (res ++ b, [])
    | a, [] => (res ++ a, [])
    | x :: xs, y :: ys =>
        if le x y then
          let (r, t) := ip25MergeRun le off fuel (res ++ [x]) xs (y :: ys)
          (r, (off + res.length, off + res.length + (x :: xs).length) :: t)
        else
          let (r, t) := ip25MergeRun le off fuel (res ++ [y]) (x :: xs) ys
          (r, (off + res.length, off + res.length + (x :: xs).length) :: t)

def ip25SortRunAt {α : Type} (le : α → α → Bool) (off : ℕ) (fuel : ℕ)
    (xs : List α) : List α × List (ℕ × ℕ) :=
  match fuel with
  | 0 => (xs, [])
  | fuel + 1 =>
    match xs with
    | [] => ([], [])
    | [_] => (xs, [])
    | _ =>
        let l := xs.take ((xs.length + 1) / 2)
        let r := xs.drop ((xs.length + 1) / 2)
        let (ls, t1) := ip25SortRunAt le off fuel l
        let (rs, t2) := ip25SortRunAt le (off + l.length) fuel r
        let (m, t3) := ip25MergeRun le off (l.length + r.length) [] ls rs
        (m, t1 ++ t2 ++ t3)

def ip25SortRun {α : Type} (le : α → α → Bool) (off : ℕ) (xs : List α) :
    List α × List (ℕ × ℕ) :=
  ip25SortRunAt le off xs.length xs

def ip25SortSchedule {M k : ℕ} (v : Fin k → Fin M) : List (ℕ × ℕ) :=
  (ip25SortRun (fun a b => decide (a ≤ b)) 0 (List.ofFn v)).2

structure Ip25BitonicGate where

  i : ℕ

  j : ℕ

  up : Bool
  deriving DecidableEq, Repr

def ip25BitonicMerge (s : ℕ) (up : Bool) : List Ip25BitonicGate :=
  match s with
  | 0 => []
  | s + 1 =>
      let half := 2 ^ s
      (List.range half).map (fun i => ⟨i, i + half, up⟩)
        ++ (ip25BitonicMerge s up
          ++ (ip25BitonicMerge s up).map
            (fun g => ⟨g.i + half, g.j + half, g.up⟩))

def ip25BitonicSortDir (m : ℕ) (up : Bool) : List Ip25BitonicGate :=
  match m with
  | 0 => []
  | m + 1 =>
      let half := 2 ^ m
      ip25BitonicSortDir m (!up)
        ++ ((ip25BitonicSortDir m up).map (fun g => ⟨g.i + half, g.j + half, g.up⟩)
          ++ ip25BitonicMerge (m + 1) up)

def ip25BitonicSort (m : ℕ) : List Ip25BitonicGate := ip25BitonicSortDir m true

def ip25BoolGate (g : Ip25BitonicGate) (v : ℕ → Bool) : ℕ → Bool :=
  fun j =>
    if j = g.i then
      if g.up then v j && v g.j else v j || v g.j
    else if j = g.j then
      if g.up then v j || v g.i else v j && v g.i
    else v j

def ip25BoolRun (gs : List Ip25BitonicGate) (v : ℕ → Bool) : ℕ → Bool :=
  gs.foldl (fun v g => ip25BoolGate g v) v

def ip25BoolHalfCleaner (h : ℕ) (v : ℕ → Bool) : ℕ → Bool :=
  fun j => if j < h then v j && v (j + h) else if j < 2 * h then v (j - h) || v j else v j

def ip25BoolHalfCleanerGates (h : ℕ) : List Ip25BitonicGate :=
  (List.range h).map (fun j => ⟨j, j + h, true⟩)

def ip25BoolMergeRun (s : ℕ) (up : Bool) (v : ℕ → Bool) : ℕ → Bool :=
  match s with
  | 0 => v
  | s + 1 =>
      let half := 2 ^ s
      let b := ip25BoolHalfCleaner half v
      let lo := ip25BoolMergeRun s up (fun j => b j)
      let hi := ip25BoolMergeRun s up (fun j => b (j + half))
      fun j => if j < half then lo j else if j < 2 * half then hi (j - half) else b j

def ip25BoolSortRun (m : ℕ) (up : Bool) (v : ℕ → Bool) : ℕ → Bool :=
  match m with
  | 0 => v
  | m + 1 =>
      let half := 2 ^ m
      let lo := ip25BoolSortRun m (!up) (fun j => v j)
      let hi := ip25BoolSortRun m up (fun j => v (j + half))
      ip25BoolMergeRun (m + 1) up (fun j => if j < half then lo j else hi (j - half))

def Ip25BoolMountain (v : ℕ → Bool) (n z : ℕ) : Prop :=
  ∃ A B, A ≤ B ∧ B ≤ n ∧ n - (B - A) = z ∧ ∀ j < n, v j = decide (A ≤ j ∧ j < B)

def Ip25BoolValley (v : ℕ → Bool) (n z : ℕ) : Prop :=
  ∃ A B, A ≤ B ∧ B ≤ n ∧ B - A = z ∧ ∀ j < n, v j = decide (j < A ∨ (B ≤ j))

def Ip25BoolBitonic (v : ℕ → Bool) (n z : ℕ) : Prop :=
  Ip25BoolMountain v n z ∨ Ip25BoolValley v n z

def Ip25BoolSorted (v : ℕ → Bool) (n z : ℕ) : Prop :=
  z ≤ n ∧ ∀ j < n, v j = decide (z ≤ j)

def Ip25BoolReverseSorted (v : ℕ → Bool) (n z : ℕ) : Prop :=
  z ≤ n ∧ ∀ j < n, v j = decide (j < n - z)

end Qatlib.Concepts.RandCompile.ChannelBudget
