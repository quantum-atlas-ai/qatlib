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

/-!
# Interaction picture parameter and program definitions

This module collects cutoff formulas, grid conditions, sorted Dyson sums, and explicit program
layouts for interaction picture simulation. `ipSegmentProgram` uses duplicated query wires,
while separate definitions record segment, sparse-query, failure, and resource quantities.

`ipLchsThreeFactor` packages free and interaction picture evolutions as a three-factor matrix
expression. The interaction picture simulation setting is described in [LowWiebe2018].

## Main statements

* `ipSourceGridCondition`: the explicit grid lower bounds.
* `ipSegmentProgram`: the duplicated-wire query and phase instruction program.
* `ipTotalFailure`: the algebraic failure accumulation expression.
* `ipLchsThreeFactor`: the three-factor evolution expression.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Concepts.LchsSimulation.InteractHybrid
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The natural ceiling of the logarithmic cutoff expression `-1 + 2 log(2 / ε) / log(log(2 /
ε)) + 1`. -/
noncomputable def ipPrintedCutoff (ε : ℝ) : ℕ :=
  Nat.ceil (-1 + 2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε)) + 1)

/-- The tolerance condition `0 < ε ≤ 1 / 2 - 1 / exp 1`. -/
def ipPrintedRange (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 - 1 / Real.exp 1

/-- The computed Dyson cutoff at precision parameter `k`. -/
def ipClosedFormK (k : ℕ) : ℕ := computedDysonCutoff k

/-- The computed Dyson grid size for duration `t`, norm bound `Λ`, mean derivative parameter
`χ`, and precision `k`. -/
def ipClosedFormM (t Λ χ : ℝ) (k : ℕ) : ℕ := computedDysonGridSize t Λ χ k

/-- The computed grid dominates both `16 t² (χ + Λ²) 2^k` and the squared computed cutoff. -/
def ipSourceGridCondition (t Λ χ : ℝ) (k : ℕ) : Prop :=
  16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k ≤ ipClosedFormM t Λ χ k ∧
    (ipClosedFormK k) ^ 2 ≤ ipClosedFormM t Λ χ k

/-- The computed cutoff makes the factorial-tail expression `2 x^(K+1) / (K+1)!` at most `2⁻ᵏ /
2`. -/
def ipTruncationTail (k : ℕ) (x : ℝ) : Prop :=
  2 * x ^ (ipClosedFormK k + 1) / (Nat.factorial (ipClosedFormK k + 1) : ℝ) ≤
    (1 / 2 : ℝ) ^ k / 2

/-- Sum the sorted Hamiltonian words over injective sample-index functions from `Fin k` to `Fin
M`. -/
noncomputable def ipInjectiveCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if Function.Injective v then effectiveSortedWord H t M k v else 0

/-- The unscaled sum of reverse-ordered Hamiltonian products over strictly increasing
sample-index functions. -/
noncomputable def ipStrictCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveStrictRaw H t M k

/-- The unscaled sorted Hamiltonian sum over all sample-index functions, including repeated
indices. -/
noncomputable def ipRepeatedCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveCubeRaw H t M k

/-- The unscaled sorted Hamiltonian sum restricted to noninjective sample-index functions. -/
noncomputable def ipCollisionCube {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  effectiveCollisionRaw H t M k

/-- Sort the list of sample indices supplied by `v` in nondecreasing order. -/
def ipSortedIndexList (M k : ℕ) (v : Fin k → Fin M) : List (Fin M) :=
  (List.ofFn v).mergeSort (fun a b => decide (a ≤ b))

/-- Multiply the sampled Hamiltonians in reverse sorted-index order, retaining any repeated
indices. -/
noncomputable def ipSortedWord {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) (v : Fin k → Fin M) : Matrix I I ℂ :=
  effectiveSortedWord H t M k v

/-- The system wires followed by the ancillary and time wire block for copy `j`. -/
def ipDuplicatedWires (p : EffectiveSegmentParameters) (j : ℕ) : List ℕ :=
  effectiveDuplicatedWires p j

/-- The number of duplicated query-register copies, defined to be the segment Dyson cutoff. -/
def ipSegmentCopies (p : EffectiveSegmentParameters) : ℕ := effectiveSegmentK p

/-- The system width plus one ancillary-and-time block for each segment copy. -/
def ipSegmentWidth (p : EffectiveSegmentParameters) : ℕ :=
  p.ns + ipSegmentCopies p * (p.na + p.nd)

/-- For each duplicated copy, issue a slot-zero query followed by the specified dyadic Z phase
instruction. -/
def ipSegmentSteps (p : EffectiveSegmentParameters) : List EffectiveStep :=
  (List.range (ipSegmentCopies p)).flatMap (fun j =>
    [ EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false
    , EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false ])

/-- The effective program with the duplicated-register segment width and instruction list
`ipSegmentSteps p`. -/
def ipSegmentProgram (p : EffectiveSegmentParameters) : EffectiveProgram :=
  { width := ipSegmentWidth p
    steps := ipSegmentSteps p }

/-- The assigned segment query count, equal to the segment Dyson cutoff. -/
def ipSegmentQueries (p : EffectiveSegmentParameters) : ℕ := effectiveSegmentK p

/-- The assigned long-time segment count `effectiveLongR p`. -/
def ipSegmentCount (p : EffectiveSegmentParameters) : ℕ := effectiveLongR p

/-- The per-segment failure bound expression `2 δ`. -/
def ipPerSegmentFailure (δ : ℝ) : ℝ := 2 * δ

/-- The accumulated failure expression `1 - (1 - δ)^L` for `L` segments. -/
def ipTotalFailure (L : ℕ) (δ : ℝ) : ℝ := 1 - (1 - δ) ^ L

/-- Divide the total error budget `ε` by the natural segment count `L`, viewed as a real number. -/
def ipSegmentBudget (L : ℕ) (ε : ℝ) : ℝ := ε / (L : ℝ)

/-- The product of the assigned segment count and the assigned query count for `p`. -/
def ipTotalQueries (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentCount p * ipSegmentQueries p

/-- The local segment-program width plus the base-two ceiling logarithm of the segment count. -/
def ipTotalQubits (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentWidth (effectiveLongLocal p) + Nat.clog 2 (ipSegmentCount p)

/-- The segment count times the sum of the local segment query count and local copy count. -/
def ipTotalGates (p : EffectiveSegmentParameters) : ℕ :=
  ipSegmentCount p * (ipSegmentQueries (effectiveLongLocal p) + ipSegmentCopies (effectiveLongLocal p))

/-- The effective sparse program consisting of value and location queries in slots zero and one
followed by a dyadic Z phase instruction. -/
def ipSparseProgram (p : EffectiveSparseParameters) : EffectiveProgram :=
  { width := p.nd + 2 * p.ns + 2 * p.np
    steps := [ EffectiveStep.query 0 (List.range (p.nd + 2 * p.ns + 2 * p.np)) [] false
      , EffectiveStep.query 1 (List.range (p.nd + 2 * p.ns)) [] false
      , EffectiveStep.phase (p.nd + 2 * p.ns) 1 1 false ] }

/-- The assigned sparse-program query count, equal to two. -/
def ipSparseQueries (p : EffectiveSparseParameters) : ℕ := 2

/-- The product of evolution under `k • L`, ordered evolution of its interaction generator with
`H`, and evolution under `-(k • L)`. -/
def ipLchsThreeFactor (I : Type) [Fintype I] [DecidableEq I]
    (L H : Matrix I I ℂ) (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) (fun _ => H) u) 0 t *
    HamiltonianEvolution (-(k • L)) t

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
