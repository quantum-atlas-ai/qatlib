/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeWeightedSampling
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

def pendingIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if r.stop = .fuel then 1 else 0

noncomputable def pendingMass (n a b : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    pendingIndicator

noncomputable def tailMass (n a b : ℕ) : ℝ≥0∞ := pendingMass (n+1) a b

noncomputable def expectedBits (a b : ℕ) : ℝ≥0∞ := ∑' n, tailMass n a b

noncomputable def expectedSteps (a b : ℕ) : ℝ≥0∞ := ∑' n, pendingMass n a b

noncomputable def pendingProb (n a b : ℕ) : ℝ := (pendingMass n a b).toReal

noncomputable def decay (a b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - 1 / ((a + b : ℕ) : ℝ) ^ 2)

noncomputable def decayReal (a b : ℕ) : ℝ := 1 - 1 / ((a + b : ℕ) : ℝ) ^ 2

noncomputable def pendingInputMass (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    pendingIndicator

noncomputable def truncationFailure (n a b : ℕ) : ℝ≥0∞ := pendingMass n a b

noncomputable def truncationBudget (a b : ℕ) (delta : ℝ) : ℕ :=
  (a + b) * (a + b) * Nat.ceil (((a : ℝ) * (b : ℝ)) / delta)

noncomputable def expectedInputSteps (A B : ℕ) : ℝ≥0∞ :=
  ∑' n, pendingInputMass n A B

noncomputable def pendingInputProb (n A B : ℕ) : ℝ :=
  (pendingInputMass n A B).toReal

noncomputable def truncationBudgetInput (A B : ℕ) (delta : ℝ) : ℕ :=
  A + 1 + truncationBudget A B delta

noncomputable def leftEventProb (n a b : ℕ) : ℝ :=
  (Qatlib.Concepts.AdversaryBounds.AdvDuality.leftEvent n a b).toReal

noncomputable def rightEventProb (n a b : ℕ) : ℝ :=
  (Qatlib.Concepts.AdversaryBounds.AdvDuality.rightEvent n a b).toReal

inductive BucketTree where
  | leaf (w : ℕ)
  | node (left right : BucketTree)

def totalWeight : BucketTree → ℕ
  | .leaf w => w
  | .node l r => totalWeight l + totalWeight r

def PositiveTree : BucketTree → Prop
  | .leaf w => 0 < w
  | .node l r => PositiveTree l ∧ PositiveTree r

def isPath : BucketTree → List Bool → Prop
  | .leaf _, [] => True
  | .leaf _, _ => False
  | .node _ _, [] => False
  | .node l _, true :: bs => isPath l bs
  | .node _ r, false :: bs => isPath r bs

def leafWeight : BucketTree → List Bool → ℕ
  | .leaf w, _ => w
  | .node _ _, [] => 0
  | .node l _, true :: bs => leafWeight l bs
  | .node _ r, false :: bs => leafWeight r bs

def leafPaths : BucketTree → List (List Bool)
  | .leaf _ => [[]]
  | .node l r => (leafPaths l).map (fun p => true :: p) ++ (leafPaths r).map (fun p => false :: p)

def nodePairs : BucketTree → List (ℕ × ℕ)
  | .leaf _ => []
  | .node l r => (totalWeight l, totalWeight r) :: (nodePairs l ++ nodePairs r)

noncomputable def leafMass : BucketTree → List Bool → ℝ
  | .leaf _, _ => 1
  | .node _ _, [] => 0
  | .node l r, true :: bs =>
      (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass l bs
  | .node l r, false :: bs =>
      (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass r bs

noncomputable def massSum : BucketTree → ℝ
  | .leaf _ => 1
  | .node l r =>
      (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * massSum l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * massSum r

noncomputable def treeBits : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      (totalWeight l : ℝ) * (totalWeight r : ℝ) +
        (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeBits l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeBits r

noncomputable def treeSteps : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      ((totalWeight l : ℝ) * (totalWeight r : ℝ) + (totalWeight l : ℕ) + 2) +
        (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps r

noncomputable def treeBitsByNodes : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) * (totalWeight r : ℝ)) +
        treeBitsByNodes l (reach * (totalWeight l : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ)) +
        treeBitsByNodes r (reach * (totalWeight r : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ))

noncomputable def treeStepsByNodes : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) * (totalWeight r : ℝ) + (totalWeight l : ℕ) + 2) +
        treeStepsByNodes l (reach * (totalWeight l : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ)) +
        treeStepsByNodes r (reach * (totalWeight r : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ))

noncomputable def inputLeftEvent (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.leftIndicator

noncomputable def inputRightEvent (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.rightIndicator

noncomputable def inputLeftEventProb (n A B : ℕ) : ℝ := (inputLeftEvent n A B).toReal

noncomputable def inputRightEventProb (n A B : ℕ) : ℝ := (inputRightEvent n A B).toReal

structure NodeLaw where

  toLeft : ℝ

  toRight : ℝ

  pending : ℝ

noncomputable def nodeLaw (n : ℕ) (WL WR : ℕ) : NodeLaw :=
  ⟨inputRightEventProb (WL + 1 + n) WL WR,
    inputLeftEventProb (WL + 1 + n) WL WR,
    pendingInputProb (WL + 1 + n) WL WR⟩

noncomputable def treeSuccessProb (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 1
  | .node l r =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSuccessProb n l +
        (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSuccessProb n r

noncomputable def treePendingProb (n : ℕ) (t : BucketTree) : ℝ := 1 - treeSuccessProb n t

noncomputable def treeLeafMassTrunc (n : ℕ) : BucketTree → List Bool → ℝ
  | .leaf _, [] => 1
  | .leaf _, _ => 0
  | .node _ _, [] => 0
  | .node l r, true :: bs =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeLeafMassTrunc n l bs
  | .node l r, false :: bs =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeLeafMassTrunc n r bs

def treeInternalCount : BucketTree → ℕ
  | .leaf _ => 0
  | .node l r => 1 + treeInternalCount l + treeInternalCount r

noncomputable def treePendingByNodes (n : ℕ) : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending +
        treePendingByNodes n l
          (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
        treePendingByNodes n r
          (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)

noncomputable def encWeight (N : ℕ) (x : ℝ) : ℕ := Nat.floor (N * x)

noncomputable def encDefect (N : ℕ) (x : ℝ) : ℝ := N * x - (encWeight N x : ℝ)

noncomputable def nodeBudget (count : ℕ) (delta : ℝ) (WL WR : ℕ) : ℕ :=
  truncationBudget WL WR (delta / (count : ℝ)) + 1

noncomputable def treeTruncationBudgetWith (count : ℕ) (t : BucketTree) (delta : ℝ) : ℕ :=
  match t with
  | .leaf _ => 0
  | .node l r =>
      max (nodeBudget count delta (totalWeight l) (totalWeight r))
        (max (treeTruncationBudgetWith count l delta) (treeTruncationBudgetWith count r delta))

noncomputable def treeTruncationBudget (t : BucketTree) (delta : ℝ) : ℕ :=
  treeTruncationBudgetWith (treeInternalCount t) t delta

def NodePendingBound (n : ℕ) (eps : ℝ) : BucketTree → Prop
  | .leaf _ => True
  | .node l r =>
      (nodeLaw n (totalWeight l) (totalWeight r)).pending ≤ eps ∧
      NodePendingBound n eps l ∧
      NodePendingBound n eps r

def BudgetCovers (count : ℕ) (delta : ℝ) (budget : ℕ) : BucketTree → Prop
  | .leaf _ => True
  | .node l r =>
      nodeBudget count delta (totalWeight l) (totalWeight r) ≤ budget ∧
      BudgetCovers count delta budget l ∧
      BudgetCovers count delta budget r

def treePathCost (n : ℕ) : BucketTree → List Bool → ℝ
  | .leaf _, _ => 0
  | .node _ _, [] => 0
  | .node l r, true :: bs => (totalWeight l : ℝ) + 1 + n + treePathCost n l bs
  | .node l r, false :: bs => (totalWeight l : ℝ) + 1 + n + treePathCost n r bs

def treeWorstSteps (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      max ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n l)
        ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n r)

def treeDepth : BucketTree → ℕ
  | .leaf _ => 0
  | .node l r => 1 + max (treeDepth l) (treeDepth r)

noncomputable def truncatedInputSteps (n A B : ℕ) : ℝ≥0∞ :=
  (∑ k ∈ Finset.range n, pendingInputMass k A B) + (n : ℝ≥0∞) * pendingInputMass n A B

noncomputable def nodeTruncSteps (n WL WR : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (WL + 1 + n), pendingInputProb k WL WR) +
    ((WL + 1 + n : ℕ) : ℝ) * pendingInputProb (WL + 1 + n) WL WR

noncomputable def treeTruncSteps (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      nodeTruncSteps n (totalWeight l) (totalWeight r) +
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeTruncSteps n l +
      (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeTruncSteps n r

noncomputable def treeTruncWaste (n : ℕ) : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) + 1 + n) *
          (nodeLaw n (totalWeight l) (totalWeight r)).pending +
      treeTruncWaste n l (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
      treeTruncWaste n r (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)

noncomputable def encEvalSteps (N : ℕ) (x : ℝ) : ℕ := encWeight N x

noncomputable def encTotalSteps (N : ℕ) (u v : ℝ) : ℝ :=
  ((encEvalSteps N u + encEvalSteps N v : ℕ) : ℝ) +
    (expectedInputSteps (encWeight N u) (encWeight N v)).toReal

def stateLabel (state : Bool)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : Option Bool :=
  match Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | some false => some state
  | some true => some (!state)
  | Option.none => Option.none

noncomputable def stateLabelMass (a b : ℕ) (state : Bool) : ℝ :=
  (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
    (if stateLabel state r = some true then 1 else 0)).toReal

inductive StateBucketTree (S : Type) where
  | leaf (w : S → ℕ)
  | node (left right : StateBucketTree S)

def stateTotalWeight {S : Type} : StateBucketTree S → S → ℕ
  | .leaf w, s => w s
  | .node l r, s => stateTotalWeight l s + stateTotalWeight r s

def PositiveStateTree {S : Type} : StateBucketTree S → S → Prop
  | .leaf w, s => 0 < w s
  | .node l r, s => PositiveStateTree l s ∧ PositiveStateTree r s

def stateIsPath {S : Type} : StateBucketTree S → List Bool → Prop
  | .leaf _, [] => True
  | .leaf _, _ => False
  | .node l r, [] => False
  | .node l r, true :: bs => stateIsPath l bs
  | .node l r, false :: bs => stateIsPath r bs

def stateLeafWeight {S : Type} : StateBucketTree S → S → List Bool → ℕ
  | .leaf w, s, _ => w s
  | .node _ _, _, [] => 0
  | .node l _, s, true :: bs => stateLeafWeight l s bs
  | .node _ r, s, false :: bs => stateLeafWeight r s bs

noncomputable def stateLeafMass {S : Type} : StateBucketTree S → S → List Bool → ℝ
  | .leaf _, _, [] => 1
  | .leaf _, _, _ => 0
  | .node _ _, _, [] => 0
  | .node l r, s, true :: bs =>
      (stateTotalWeight l s : ℝ) /
          ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ) *
        stateLeafMass l s bs
  | .node l r, s, false :: bs =>
      (stateTotalWeight r s : ℝ) /
          ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ) *
        stateLeafMass r s bs

noncomputable def stateTreeBits {S : Type} : StateBucketTree S → S → ℝ
  | .leaf _, _ => 0
  | .node l r, s =>
      (stateTotalWeight l s : ℝ) * (stateTotalWeight r s : ℝ) +
        (stateTotalWeight l s : ℝ) /
            ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ) *
          stateTreeBits l s +
        (stateTotalWeight r s : ℝ) /
            ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ) *
          stateTreeBits r s

noncomputable def stateTreeBitsByNodes {S : Type} : StateBucketTree S → S → ℝ → ℝ
  | .leaf _, _, _ => 0
  | .node l r, s, reach =>
      reach * ((stateTotalWeight l s : ℝ) * (stateTotalWeight r s : ℝ)) +
        stateTreeBitsByNodes l s
          (reach * (stateTotalWeight l s : ℝ) /
            ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ)) +
        stateTreeBitsByNodes r s
          (reach * (stateTotalWeight r s : ℝ) /
            ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
