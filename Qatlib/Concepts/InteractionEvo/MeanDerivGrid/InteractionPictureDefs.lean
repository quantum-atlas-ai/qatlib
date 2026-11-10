/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.ComputedGrid.ComputedDysonGridProgram
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveDysonParameters
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveCubeTransport
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveInteractionGateRateHami
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveInteractionQueries
import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeHami
import Qatlib.Concepts.InteractionEvo.SegmentProduct.Corollary4CompositeErrorHami
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveSparseHAMT
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveTriangleEncoding
import Qatlib.Concepts.LchsSimulation.InteractHybrid.InteractionPictureLchsReprLine
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Concepts.LchsSimulation.InteractHybrid
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def ipPrintedCutoff (ε : ℝ) : ℕ :=
  Nat.ceil (-1 + 2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε)) + 1)

def ipPrintedRange (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 - 1 / Real.exp 1

def ipClosedFormK (k : ℕ) : ℕ := computedDysonCutoff k

def ipClosedFormM (t Λ χ : ℝ) (k : ℕ) : ℕ := computedDysonGridSize t Λ χ k

def ipSourceGridCondition (t Λ χ : ℝ) (k : ℕ) : Prop :=
  16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k ≤ ipClosedFormM t Λ χ k ∧
    (ipClosedFormK k) ^ 2 ≤ ipClosedFormM t Λ χ k

def ipTruncationTail (k : ℕ) (x : ℝ) : Prop :=
  2 * x ^ (ipClosedFormK k + 1) / (Nat.factorial (ipClosedFormK k + 1) : ℝ) ≤
    (1 / 2 : ℝ) ^ k / 2

noncomputable def ipInjectiveCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if Function.Injective v then effectiveSortedWord H t M k v else 0

noncomputable def ipStrictCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveStrictRaw H t M k

noncomputable def ipRepeatedCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveCubeRaw H t M k

noncomputable def ipCollisionCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveCollisionRaw H t M k

def ipSortedIndexList (M k : ℕ) (v : Fin k → Fin M) : List (Fin M) :=
  (List.ofFn v).mergeSort (fun a b => decide (a ≤ b))

noncomputable def ipSortedWord {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) (v : Fin k → Fin M) : Matrix I I ℂ :=
  effectiveSortedWord H t M k v

def ipDuplicatedWires (p : EffectiveSegmentParameters) (j : ℕ) : List ℕ :=
  effectiveDuplicatedWires p j

def ipSegmentCopies (p : EffectiveSegmentParameters) : ℕ := effectiveSegmentK p

def ipSegmentWidth (p : EffectiveSegmentParameters) : ℕ :=
  p.ns + ipSegmentCopies p * (p.na + p.nd)

def ipSegmentSteps (p : EffectiveSegmentParameters) : List EffectiveStep :=
  (List.range (ipSegmentCopies p)).flatMap (fun j =>
    [ EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false
    , EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false ])

def ipSegmentProgram (p : EffectiveSegmentParameters) : EffectiveProgram :=
  { width := ipSegmentWidth p
    steps := ipSegmentSteps p }

def ipSegmentQueries (p : EffectiveSegmentParameters) : ℕ := effectiveSegmentK p

def ipSegmentCount (p : EffectiveSegmentParameters) : ℕ := effectiveLongR p

def ipPerSegmentFailure (δ : ℝ) : ℝ := 2 * δ

def ipTotalFailure (L : ℕ) (δ : ℝ) : ℝ := 1 - (1 - δ) ^ L

def ipSegmentBudget (L : ℕ) (ε : ℝ) : ℝ := ε / (L : ℝ)

def ipTotalQueries (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentCount p * ipSegmentQueries p

def ipTotalQubits (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentWidth (effectiveLongLocal p) + Nat.clog 2 (ipSegmentCount p)

def ipTotalGates (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentCount p * (ipSegmentQueries (effectiveLongLocal p) + ipSegmentCopies (effectiveLongLocal p))

def ipSparseProgram (p : EffectiveSparseParameters) : EffectiveProgram :=
  { width := p.nd + 2 * p.ns + 2 * p.np
    steps := [ EffectiveStep.query 0 (List.range (p.nd + 2 * p.ns + 2 * p.np)) [] false
      , EffectiveStep.query 1 (List.range (p.nd + 2 * p.ns)) [] false
      , EffectiveStep.phase (p.nd + 2 * p.ns) 1 1 false ] }

def ipSparseQueries (p : EffectiveSparseParameters) : ℕ := 2

def ipLchsThreeFactor (I : Type) [Fintype I] [DecidableEq I]
    (L H : Matrix I I ℂ) (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) (fun _ => H) u) 0 t *
    HamiltonianEvolution (-(k • L)) t

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
