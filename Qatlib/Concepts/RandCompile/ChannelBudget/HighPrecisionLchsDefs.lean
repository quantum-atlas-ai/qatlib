/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.HighPrecisionLchs
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

def kernelFrontier : Set ℂ := {z : ℂ | z.im = 0}

def kernelDomainGap : Set ℂ := lowerClosedHalfPlane \ lowerOpenHalfPlane

def frontierIndicator : ℂ → ℂ := fun z => if z.im = 0 then 1 else 0

def sourceCellCoefficient {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ)
    (m : Fin M) (q : Fin Q) : ℂ :=
  (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
    κ (compositeNodeAt K node m q)

def discreteSourceTerm {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ)
    (σ : ℝ → QState I) : QState I :=
  ∑ m : Fin M, ∑ q : Fin Q,
    (sourceCellCoefficient K node weight κ m q) • σ (compositeNodeAt K node m q)

def sourceCoefficientMass {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℝ :=
  ∑ m : Fin M, ∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖

def sourceCoefficientSup {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℝ :=
  ⨆ m : Fin M, ⨆ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖

def entrywiseSup {J K : Type} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (A : Matrix J K ℂ) : ℝ := ⨆ i, ⨆ j, ‖A i j‖

def allOnesMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := fun _ _ => 1

def loadingCount (M Q : ℕ) : ℕ := M * Q

def loadingBits (precision : ℝ) : ℕ := Nat.ceil (Real.log (1 / precision) / Real.log 2) + 1

def compositeCoefficientMass {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : ℝ :=
  ∑ m : Fin M, ∑ q : Fin Q, ‖compositeCoefficients K node weight κ m q‖

def compositeCoefficientL2 {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : ℝ :=
  Real.sqrt (∑ m : Fin M, ∑ q : Fin Q, ‖compositeCoefficients K node weight κ m q‖ ^ 2)

def amplificationRounds {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) : ℕ :=
  max 1 (Nat.ceil (compositeCoefficientMass M K node weight κ /
    compositeCoefficientL2 M K node weight κ))

def filterRoundCount {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X) : ℝ :=
  1 / filterSuccessProbability g

def observableSampleCount {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (ε δ : ℝ) : ℕ :=
  gibbsSampleCount g ε δ

def lchs30CellRemainder (Q : ℕ) (c s h : ℝ) : ℝ :=
  c * s * h ^ (2 * Q + 1)

def lchs30CompositeRemainder (Q M : ℕ) (c s h : ℝ) : ℝ :=
  (M : ℝ) * lchs30CellRemainder Q c s h

structure LchsNearOptimalLedger where

  kLabels : ℕ

  cells : ℕ

  nodesPerCell : ℕ

  loadedPairs : ℕ

  loadingBits : ℕ

  amplificationRounds : ℕ

  shots : ℕ

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

def lchs31TotalCost (l : LchsNearOptimalLedger) : ℕ :=
  l.loadedPairs + l.amplificationRounds + l.shots

end Qatlib.Concepts.RandCompile.ChannelBudget
