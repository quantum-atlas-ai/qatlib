/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.HighPrecisionLchs

/-!
# High precision LCHS coefficients and cost ledgers

This module defines source quadrature coefficients, their mass, and the corresponding finite
source sum. The sets `kernelFrontier` and `kernelDomainGap` distinguish boundary regularity from
analyticity on the open lower half-plane in the LCHS setting of [AnChildsLin2026].

`LchsNearOptimalLedger` gathers quadrature loading, amplification, and sampling counts. The
remainder expressions and matrix norm examples support the refined analytic estimates in the
companion module.

## Main statements

* `discreteSourceTerm`: sum weighted source evaluations over cells and quadrature nodes.
* `compositeCoefficientL2`: record the L2 norm of the coefficient family.
* `lchs31NearOptimalLedger`: assemble the quadrature and sampling ledger.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.Quadrature

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real axis, represented as the set of complex numbers with zero imaginary part. -/
def kernelFrontier : Set ℂ := {z : ℂ | z.im = 0}

/-- The set difference between the closed and open lower half-planes. -/
def kernelDomainGap : Set ℂ := lowerClosedHalfPlane \ lowerOpenHalfPlane

/-- The complex-valued indicator of the real axis. -/
def frontierIndicator : ℂ → ℂ := fun z => if z.im = 0 then 1 else 0

/-- The source quadrature coefficient obtained by multiplying half the cell width, the node
weight, and the kernel value at the composite node. -/
def sourceCellCoefficient {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ)
    (m : Fin M) (q : Fin Q) : ℂ :=
  (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
    κ (compositeNodeAt K node m q)

/-- The finite double sum of source vectors weighted by `sourceCellCoefficient` over cells and
nodes. -/
def discreteSourceTerm {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ)
    (σ : ℝ → QState I) : QState I :=
  ∑ m : Fin M, ∑ q : Fin Q,
    (sourceCellCoefficient K node weight κ m q) • σ (compositeNodeAt K node m q)

/-- The sum of the norms of all source cell coefficients. -/
def sourceCoefficientMass {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℝ :=
  ∑ m : Fin M, ∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖

/-- The iterated supremum of source coefficient norms over cells and nodes. -/
def sourceCoefficientSup {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℝ :=
  ⨆ m : Fin M, ⨆ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖

/-- The iterated supremum of the norms of a finite matrix's entries. -/
def entrywiseSup {J K : Type} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (A : Matrix J K ℂ) : ℝ := ⨆ i, ⨆ j, ‖A i j‖

/-- The `d`-by-`d` complex matrix with every entry equal to one. -/
def allOnesMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := fun _ _ => 1

/-- The number `M * Q` of cell-node pairs. -/
def loadingCount (M Q : ℕ) : ℕ := M * Q

/-- The loading precision allowance `ceil(log(1 / precision) / log 2) + 1`. -/
def loadingBits (precision : ℝ) : ℕ := Nat.ceil (Real.log (1 / precision) / Real.log 2) + 1

/-- The sum of the norms of the composite quadrature coefficients over all cells and nodes. -/
def compositeCoefficientMass {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : ℝ :=
  ∑ m : Fin M, ∑ q : Fin Q, ‖compositeCoefficients K node weight κ m q‖

/-- The square root of the sum of squared norms of the composite quadrature coefficients. -/
def compositeCoefficientL2 {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : ℝ :=
  Real.sqrt (∑ m : Fin M, ∑ q : Fin Q, ‖compositeCoefficients K node weight κ m q‖ ^ 2)

/-- The positive integer ceiling of the ratio of composite coefficient mass to coefficient L2
norm, with a minimum of one. -/
def amplificationRounds {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℕ :=
  max 1 (Nat.ceil (compositeCoefficientMass M K node weight κ /
    compositeCoefficientL2 M K node weight κ))

/-- The reciprocal of the Gibbs filter success probability. -/
def filterRoundCount {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X) : ℝ :=
  1 / filterSuccessProbability g

/-- The Gibbs observable sample-count expression `gibbsSampleCount g ε δ`. -/
def observableSampleCount {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (ε δ : ℝ) : ℕ :=
  gibbsSampleCount g ε δ

/-- The cell remainder expression `c * s * h^(2 * Q + 1)`. -/
def lchs30CellRemainder (Q : ℕ) (c s h : ℝ) : ℝ :=
  c * s * h ^ (2 * Q + 1)

/-- The cell remainder expression multiplied by the number `M` of cells. -/
def lchs30CompositeRemainder (Q M : ℕ) (c s h : ℝ) : ℝ :=
  (M : ℝ) * lchs30CellRemainder Q c s h

/-- Records label, quadrature, loading, amplification, and sampling counts for high precision
LCHS. -/
structure LchsNearOptimalLedger where

  kLabels : ℕ

  cells : ℕ

  nodesPerCell : ℕ

  loadedPairs : ℕ

  loadingBits : ℕ

  amplificationRounds : ℕ

  shots : ℕ

/-- Combines a composite quadrature cost ledger with loading precision, amplification rounds,
and shot count. -/
def lchs31NearOptimalLedger (β T Λ : ℝ) (K : ℕ) (ε : ℝ) (rounds shots : ℕ) :
    LchsNearOptimalLedger :=
  let c := compositeCostLedger β T Λ K ε
  { kLabels := K + 1
    cells := c.cells
    nodesPerCell := c.nodesPerCell
    loadedPairs := c.propagatorEvaluations
    loadingBits := loadingBits ε
    amplificationRounds := rounds
    shots := shots }

/-- The sum of loaded-pair, amplification-round, and shot counts in the LCHS ledger. -/
def lchs31TotalCost (l : LchsNearOptimalLedger) : ℕ :=
  l.loadedPairs + l.amplificationRounds + l.shots

end Qatlib.Concepts.RandCompile.ChannelBudget
