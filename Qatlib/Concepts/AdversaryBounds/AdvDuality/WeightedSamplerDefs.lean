/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeWeightedSampling

/-!
# Weighted sampler laws, costs, and truncation

This module defines pending masses, tail sums, and cutoff budgets for a native fair-bit weighted
sampler. `BucketTree` organizes positive integer weights into binary choices, with recursive
leaf masses, expected costs, and truncated execution quantities for use in finite sampling and
Monte Carlo constructions [Montanaro2015].

The definitions also account for integer encodings of real weights and state-dependent sampling
through `StateBucketTree`. Nodewise cost and failure sums make the dependence on branch reach
probabilities explicit.

## Main definitions

* `expectedBits` and `expectedSteps`: tail-sum quantities for loaded sampler execution.
* `BucketTree`: binary trees of integer leaf weights.
* `treeTruncationBudget`: a common node budget obtained from the internal-node count.
* `StateBucketTree`: binary trees whose leaf weights depend on a state.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- The indicator that a native tape result stopped because its fuel was exhausted. -/
def pendingIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if r.stop = .fuel then 1 else 0

/-- The fuel-exhaustion mass after `n` steps of the weighted sampler started from the loaded
configuration with weights `a` and `b`. -/
noncomputable def pendingMass (n a b : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    pendingIndicator

/-- The pending mass after `n + 1` steps of the loaded weighted sampler. -/
noncomputable def tailMass (n a b : ℕ) : ℝ≥0∞ := pendingMass (n+1) a b

/-- The extended nonnegative tail sum of `tailMass` for the loaded weighted sampler. -/
noncomputable def expectedBits (a b : ℕ) : ℝ≥0∞ := ∑' n, tailMass n a b

/-- The extended nonnegative sum of pending masses over all step cutoffs of the loaded weighted
sampler. -/
noncomputable def expectedSteps (a b : ℕ) : ℝ≥0∞ := ∑' n, pendingMass n a b

/-- The real-valued conversion of the loaded sampler's pending mass after `n` steps. -/
noncomputable def pendingProb (n a b : ℕ) : ℝ := (pendingMass n a b).toReal

/-- The extended nonnegative conversion of `1 - 1 / (a + b)^2`. -/
noncomputable def decay (a b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - 1 / ((a + b : ℕ) : ℝ) ^ 2)

/-- The real number `1 - 1 / (a + b)^2` used as the sampler's decay factor. -/
noncomputable def decayReal (a b : ℕ) : ℝ := 1 - 1 / ((a + b : ℕ) : ℝ) ^ 2

/-- The fuel-exhaustion mass after `n` steps of the weighted sampler started from its input
configuration with weights `A` and `B`. -/
noncomputable def pendingInputMass (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    pendingIndicator

/-- The pending mass at cutoff `n` for the loaded weighted sampler. -/
noncomputable def truncationFailure (n a b : ℕ) : ℝ≥0∞ := pendingMass n a b

/-- The integer cutoff `(a + b)^2 * ceil(a * b / delta)` assigned to the loaded sampler. -/
noncomputable def truncationBudget (a b : ℕ) (delta : ℝ) : ℕ :=
  (a + b) * (a + b) * Nat.ceil (((a : ℝ) * (b : ℝ)) / delta)

/-- The extended nonnegative sum of pending masses over all cutoffs for the sampler's input
configuration. -/
noncomputable def expectedInputSteps (A B : ℕ) : ℝ≥0∞ :=
  ∑' n, pendingInputMass n A B

/-- The real-valued conversion of the input sampler's pending mass after `n` steps. -/
noncomputable def pendingInputProb (n A B : ℕ) : ℝ :=
  (pendingInputMass n A B).toReal

/-- The input sampler cutoff obtained by adding the `A + 1` initialization allowance to
`truncationBudget A B delta`. -/
noncomputable def truncationBudgetInput (A B : ℕ) (delta : ℝ) : ℕ :=
  A + 1 + truncationBudget A B delta

/-- The real-valued conversion of the loaded sampler's left-event mass at cutoff `n`. -/
noncomputable def leftEventProb (n a b : ℕ) : ℝ :=
  (Qatlib.Concepts.AdversaryBounds.AdvDuality.leftEvent n a b).toReal

/-- The real-valued conversion of the loaded sampler's right-event mass at cutoff `n`. -/
noncomputable def rightEventProb (n a b : ℕ) : ℝ :=
  (Qatlib.Concepts.AdversaryBounds.AdvDuality.rightEvent n a b).toReal

/-- A binary sampling tree with natural-number weights at its leaves. -/
inductive BucketTree where
  | leaf (w : ℕ)
  | node (left right : BucketTree)

/-- The sum of all leaf weights in a `BucketTree`. -/
def totalWeight : BucketTree → ℕ
  | .leaf w => w
  | .node l r => totalWeight l + totalWeight r

/-- The predicate that every leaf weight of a `BucketTree` is strictly positive. -/
def PositiveTree : BucketTree → Prop
  | .leaf w => 0 < w
  | .node l r => PositiveTree l ∧ PositiveTree r

/-- The predicate that a Boolean list follows a root-to-leaf path, with true choosing the left
child and false choosing the right child. -/
def isPath : BucketTree → List Bool → Prop
  | .leaf _, [] => True
  | .leaf _, _ => False
  | .node _ _, [] => False
  | .node l _, true :: bs => isPath l bs
  | .node _ r, false :: bs => isPath r bs

/-- Read the leaf weight by following Boolean choices, returning zero if the choices end at an
internal node. Any remaining choices are ignored once a leaf is reached. -/
def leafWeight : BucketTree → List Bool → ℕ
  | .leaf w, _ => w
  | .node _ _, [] => 0
  | .node l _, true :: bs => leafWeight l bs
  | .node _ r, false :: bs => leafWeight r bs

/-- List all root-to-leaf Boolean paths, with true for left edges and false for right edges. -/
def leafPaths : BucketTree → List (List Bool)
  | .leaf _ => [[]]
  | .node l r => (leafPaths l).map (fun p => true :: p) ++ (leafPaths r).map (fun p => false :: p)

/-- List the left and right subtree total weights at every internal node in preorder. -/
def nodePairs : BucketTree → List (ℕ × ℕ)
  | .leaf _ => []
  | .node l r => (totalWeight l, totalWeight r) :: (nodePairs l ++ nodePairs r)

/-- The product of subtree-weight ratios along Boolean choices in a sampling tree, with value
zero if the choices end at an internal node. Any remaining choices are ignored at a leaf. -/
noncomputable def leafMass : BucketTree → List Bool → ℝ
  | .leaf _, _ => 1
  | .node _ _, [] => 0
  | .node l r, true :: bs =>
      (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass l bs
  | .node l r, false :: bs =>
      (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass r bs

/-- The recursively computed total leaf mass, combining child masses with their subtree-weight
ratios. -/
noncomputable def massSum : BucketTree → ℝ
  | .leaf _ => 1
  | .node l r =>
      (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * massSum l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * massSum r

/-- The recursive weighted sampling bit-cost expression, charging the product of child weights
at each visited internal node. -/
noncomputable def treeBits : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      (totalWeight l : ℝ) * (totalWeight r : ℝ) +
        (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeBits l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeBits r

/-- The recursive weighted sampling step-cost expression, with local charge `WL * WR + WL + 2`
and child costs weighted by subtree ratios. -/
noncomputable def treeSteps : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      ((totalWeight l : ℝ) * (totalWeight r : ℝ) + (totalWeight l : ℕ) + 2) +
        (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps l +
        (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps r

/-- Sum local bit-cost expressions over internal nodes, propagating the supplied reach weight by
subtree-weight ratios. -/
noncomputable def treeBitsByNodes : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) * (totalWeight r : ℝ)) +
        treeBitsByNodes l (reach * (totalWeight l : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ)) +
        treeBitsByNodes r (reach * (totalWeight r : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ))

/-- Sum local step-cost expressions over internal nodes, propagating the supplied reach weight
by subtree-weight ratios. -/
noncomputable def treeStepsByNodes : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) * (totalWeight r : ℝ) + (totalWeight l : ℕ) + 2) +
        treeStepsByNodes l (reach * (totalWeight l : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ)) +
        treeStepsByNodes r (reach * (totalWeight r : ℝ) /
          ((totalWeight l + totalWeight r : ℕ) : ℝ))

/-- The left-event mass of the native weighted sampler at cutoff `n` from its input
configuration. -/
noncomputable def inputLeftEvent (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.leftIndicator

/-- The right-event mass of the native weighted sampler at cutoff `n` from its input
configuration. -/
noncomputable def inputRightEvent (n A B : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))
    Qatlib.Concepts.AdversaryBounds.AdvDuality.rightIndicator

/-- The real-valued conversion of the input sampler's left-event mass. -/
noncomputable def inputLeftEventProb (n A B : ℕ) : ℝ := (inputLeftEvent n A B).toReal

/-- The real-valued conversion of the input sampler's right-event mass. -/
noncomputable def inputRightEventProb (n A B : ℕ) : ℝ := (inputRightEvent n A B).toReal

/-- A record of real-valued masses for proceeding to the left child, proceeding to the right
child, or remaining pending. -/
structure NodeLaw where

  toLeft : ℝ

  toRight : ℝ

  pending : ℝ

/-- The node masses at cutoff `WL + 1 + n`, taking the input sampler's right event as the
left-child choice and its left event as the right-child choice. -/
noncomputable def nodeLaw (n : ℕ) (WL WR : ℕ) : NodeLaw :=
  ⟨inputRightEventProb (WL + 1 + n) WL WR,
    inputLeftEventProb (WL + 1 + n) WL WR,
    pendingInputProb (WL + 1 + n) WL WR⟩

/-- The recursively computed completion mass for a sampling tree using `nodeLaw n` at each
internal node. -/
noncomputable def treeSuccessProb (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 1
  | .node l r =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSuccessProb n l +
        (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSuccessProb n r

/-- One minus the truncated tree completion mass `treeSuccessProb n t`. -/
noncomputable def treePendingProb (n : ℕ) (t : BucketTree) : ℝ := 1 - treeSuccessProb n t

/-- The product of truncated node choice masses along an exact root-to-leaf Boolean path, with
value zero for invalid paths. -/
noncomputable def treeLeafMassTrunc (n : ℕ) : BucketTree → List Bool → ℝ
  | .leaf _, [] => 1
  | .leaf _, _ => 0
  | .node _ _, [] => 0
  | .node l r, true :: bs =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeLeafMassTrunc n l bs
  | .node l r, false :: bs =>
      (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeLeafMassTrunc n r bs

/-- The number of internal nodes in a `BucketTree`. -/
def treeInternalCount : BucketTree → ℕ
  | .leaf _ => 0
  | .node l r => 1 + treeInternalCount l + treeInternalCount r

/-- Sum pending masses over internal nodes, weighted by the reach masses induced by truncated
child choices. -/
noncomputable def treePendingByNodes (n : ℕ) : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending +
        treePendingByNodes n l
          (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
        treePendingByNodes n r
          (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)

/-- Encode a real weight `x` as the natural-number floor of `N * x`. -/
noncomputable def encWeight (N : ℕ) (x : ℝ) : ℕ := Nat.floor (N * x)

/-- The real difference between `N * x` and its natural-number encoding `encWeight N x`. -/
noncomputable def encDefect (N : ℕ) (x : ℝ) : ℝ := N * x - (encWeight N x : ℝ)

/-- The loaded sampler truncation budget for error allowance `delta / count`, increased by one. -/
noncomputable def nodeBudget (count : ℕ) (delta : ℝ) (WL WR : ℕ) : ℕ :=
  truncationBudget WL WR (delta / (count : ℝ)) + 1

/-- The maximum `nodeBudget` among internal nodes of the tree for the given count and error
allowance, with value zero at leaves. -/
noncomputable def treeTruncationBudgetWith (count : ℕ) (t : BucketTree) (delta : ℝ) : ℕ :=
  match t with
  | .leaf _ => 0
  | .node l r =>
      max (nodeBudget count delta (totalWeight l) (totalWeight r))
        (max (treeTruncationBudgetWith count l delta) (treeTruncationBudgetWith count r delta))

/-- The common tree truncation budget obtained using the tree's internal-node count in
`treeTruncationBudgetWith`. -/
noncomputable def treeTruncationBudget (t : BucketTree) (delta : ℝ) : ℕ :=
  treeTruncationBudgetWith (treeInternalCount t) t delta

/-- The predicate that every internal node's pending component under `nodeLaw n` is at most
`eps`. -/
def NodePendingBound (n : ℕ) (eps : ℝ) : BucketTree → Prop
  | .leaf _ => True
  | .node l r =>
      (nodeLaw n (totalWeight l) (totalWeight r)).pending ≤ eps ∧
      NodePendingBound n eps l ∧
      NodePendingBound n eps r

/-- The predicate that the specified budget is at least `nodeBudget count delta` at every
internal node. -/
def BudgetCovers (count : ℕ) (delta : ℝ) (budget : ℕ) : BucketTree → Prop
  | .leaf _ => True
  | .node l r =>
      nodeBudget count delta (totalWeight l) (totalWeight r) ≤ budget ∧
      BudgetCovers count delta budget l ∧
      BudgetCovers count delta budget r

/-- The sum of local cutoff costs `WL + 1 + n` along the supplied Boolean choices until a leaf
or the end of the list is reached. -/
def treePathCost (n : ℕ) : BucketTree → List Bool → ℝ
  | .leaf _, _ => 0
  | .node _ _, [] => 0
  | .node l r, true :: bs => (totalWeight l : ℝ) + 1 + n + treePathCost n l bs
  | .node l r, false :: bs => (totalWeight l : ℝ) + 1 + n + treePathCost n r bs

/-- The maximum root-to-leaf sum of local cutoff costs `WL + 1 + n`. -/
def treeWorstSteps (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      max ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n l)
        ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n r)

/-- The maximum number of internal nodes on a root-to-leaf path. -/
def treeDepth : BucketTree → ℕ
  | .leaf _ => 0
  | .node l r => 1 + max (treeDepth l) (treeDepth r)

/-- The sum of input pending masses below cutoff `n`, plus `n` times the pending mass at cutoff
`n`. -/
noncomputable def truncatedInputSteps (n A B : ℕ) : ℝ≥0∞ :=
  (∑ k ∈ Finset.range n, pendingInputMass k A B) + (n : ℝ≥0∞) * pendingInputMass n A B

/-- The real sum of input pending probabilities below cutoff `WL + 1 + n`, plus that cutoff
times its pending probability. -/
noncomputable def nodeTruncSteps (n WL WR : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (WL + 1 + n), pendingInputProb k WL WR) +
    ((WL + 1 + n : ℕ) : ℝ) * pendingInputProb (WL + 1 + n) WL WR

/-- The recursive truncated step-cost expression, adding `nodeTruncSteps` and weighting child
costs by the truncated node choice masses. -/
noncomputable def treeTruncSteps (n : ℕ) : BucketTree → ℝ
  | .leaf _ => 0
  | .node l r =>
      nodeTruncSteps n (totalWeight l) (totalWeight r) +
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeTruncSteps n l +
      (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeTruncSteps n r

/-- Sum cutoff times pending mass over internal nodes, weighted by the supplied reach mass and
subsequent truncated child choices. -/
noncomputable def treeTruncWaste (n : ℕ) : BucketTree → ℝ → ℝ
  | .leaf _, _ => 0
  | .node l r, reach =>
      reach * ((totalWeight l : ℝ) + 1 + n) *
          (nodeLaw n (totalWeight l) (totalWeight r)).pending +
      treeTruncWaste n l (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
      treeTruncWaste n r (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)

/-- The integer evaluation-step charge defined to equal `encWeight N x`. -/
noncomputable def encEvalSteps (N : ℕ) (x : ℝ) : ℕ := encWeight N x

/-- The sum of the two integer encoding charges and the real-valued expected input sampler steps
for the encoded weights. -/
noncomputable def encTotalSteps (N : ℕ) (u v : ℝ) : ℝ :=
  ((encEvalSteps N u + encEvalSteps N v : ℕ) : ℝ) +
    (expectedInputSteps (encWeight N u) (encWeight N v)).toReal

/-- Interpret sampler output false as retaining `state` and output true as flipping it,
preserving absence of an output. -/
def stateLabel (state : Bool)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : Option Bool :=
  match Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | some false => some state
  | some true => some (!state)
  | Option.none => Option.none

/-- The real-valued total halted mass for which the interpreted state label is true, starting
from loaded weights `a` and `b`. -/
noncomputable def stateLabelMass (a b : ℕ) (state : Bool) : ℝ :=
  (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
    (if stateLabel state r = some true then 1 else 0)).toReal

/-- A binary sampling tree with natural-number leaf weights that depend on a state of type `S`. -/
inductive StateBucketTree (S : Type) where
  | leaf (w : S → ℕ)
  | node (left right : StateBucketTree S)

/-- The sum of a state-dependent tree's leaf weights evaluated at the specified state. -/
def stateTotalWeight {S : Type} : StateBucketTree S → S → ℕ
  | .leaf w, s => w s
  | .node l r, s => stateTotalWeight l s + stateTotalWeight r s

/-- The predicate that every leaf weight is strictly positive at the specified state. -/
def PositiveStateTree {S : Type} : StateBucketTree S → S → Prop
  | .leaf w, s => 0 < w s
  | .node l r, s => PositiveStateTree l s ∧ PositiveStateTree r s

/-- The predicate that a Boolean list is an exact root-to-leaf path in a state-dependent tree,
with true choosing left. -/
def stateIsPath {S : Type} : StateBucketTree S → List Bool → Prop
  | .leaf _, [] => True
  | .leaf _, _ => False
  | .node l r, [] => False
  | .node l r, true :: bs => stateIsPath l bs
  | .node l r, false :: bs => stateIsPath r bs

/-- Read a state-dependent leaf weight along Boolean choices, returning zero when the choices
end at an internal node and ignoring excess choices at a leaf. -/
def stateLeafWeight {S : Type} : StateBucketTree S → S → List Bool → ℕ
  | .leaf w, s, _ => w s
  | .node _ _, _, [] => 0
  | .node l _, s, true :: bs => stateLeafWeight l s bs
  | .node _ r, s, false :: bs => stateLeafWeight r s bs

/-- The product of state-dependent subtree-weight ratios along an exact Boolean root-to-leaf
path, with value zero for invalid paths. -/
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

/-- The recursive bit-cost expression for a state-dependent tree at a fixed state, with local
charge equal to the product of child total weights. -/
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

/-- Sum local bit-cost expressions over a state-dependent tree's internal nodes, propagating
reach weights by the subtree ratios at the specified state. -/
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
