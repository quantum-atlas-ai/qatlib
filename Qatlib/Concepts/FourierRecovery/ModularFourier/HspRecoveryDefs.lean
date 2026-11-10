/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.AbelianStabilizer
import Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrderDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.StabilizerAlg.NearUniformGen.AspRecordKernel

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.HspRecoveryDefs

open Qatlib
open scoped Classical BigOperators ENNReal

def aspBisectionCost (l : ℕ) : ℕ := l + 2

def aspBisectionPrecision (l : ℕ) : ℝ := 1 / 2 ^ (l + 2)

def aspLocalisationGateCost (j : ℕ) : ℕ := 2 ^ j

def aspLocalisationCost (l : ℕ) : ℕ :=
  (Finset.range l).sum aspLocalisationGateCost

def aspCompactWidth (m : ℕ) : ℕ := Nat.log 2 m + 1

def aspCompactIndex {X : Type} [Fintype X] : X → Fin (Fintype.card X) :=
  Fintype.equivFin X

noncomputable def aqNextProductRecordLaw {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) : FinDist (Fin l → G) where
  prob ω := μ.probOf ω
  nonneg ω := Finset.prod_nonneg fun i _ => μ.nonneg (ω i)
  sum_one := FinDist.sum_probOf μ l

def clause14_endpoint : Prop :=
  (∀ (Ω G : Type*) [Fintype Ω] [DecidableEq Ω] [Fintype G]
      (k : AspRecordKernel Ω G),
      (∑ y : G, ∑ V : Ω, k.branchLaw.prob V * (k.conditional V).prob y) = 1)
  ∧ (∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (χ : AddChar G ℂ),
      (aspOrbitBranchLaw G).prob χ = (Fintype.card G : ℝ)⁻¹)
  ∧ (∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (l : ℕ),
      ControlledPowers U (2 ^ l) = BlockDiag (fun x : Fin (2 ^ l) => U ^ (x.val : ℕ)))
  ∧ (∀ (l j : ℕ) (hj : j < l), 2 ^ j ≤ 2 ^ l - 1)
  ∧ (∀ (l : ℕ) (o : ℕ → Bool),
      (aspBisectionRun l o).queries = aspBisectionCost l ∧
        (aspBisectionRun l o).level = aspBisectionCost l ∧
        (aspBisectionRun l o).width = aspBisectionPrecision l)
  ∧ (∀ (l : ℕ) (o : ℕ → Bool) (φ : ℝ), 0 ≤ φ ∧ φ < 1 →
      AspBisectionOracleCorrect o φ (l + 2) →
        (aspBisectionRun l o).lower ≤ φ ∧ φ < (aspBisectionRun l o).lower
          + (aspBisectionRun l o).width)

def walkGoal_endpoint : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (l : ℕ),
      ControlledPowers U (2 ^ l) = BlockDiag (fun x : Fin (2 ^ l) => U ^ (x.val : ℕ)))
  ∧ (∀ (l : ℕ) (x : Fin (2 ^ l)), x.val ≤ 2 ^ l - 1)
  ∧ (∀ (l j : ℕ) (hj : j < l), 2 ^ j ≤ 2 ^ l - 1 ∧ (2 ^ j : ℕ) < 2 ^ l)
  ∧ (∀ l : ℕ, aspLocalisationCost l = 2 ^ l - 1)
  ∧ (∀ l : ℕ, aspLocalisationCost l ≤ 2 ^ l)

def clause16_endpoint : Prop :=
  (∀ (G : Type*) [Fintype G] [DecidableEq G] (μ : FinDist G) (l : ℕ),
      (∑ ω : Fin l → G, (aspProductRecordLaw μ l).prob ω) = 1)
  ∧ (∀ (G : Type*) [Fintype G] [DecidableEq G] (μ : FinDist G) (l : ℕ) (ω : Fin l → G),
      (aspProductRecordLaw μ l).prob ω = μ.probOf ω)
  ∧ (∀ (m : ℕ), m ≠ 0 → m ≤ 2 ^ aspCompactWidth m)

  ∧ (∀ (G : Type*) [Fintype G] [DecidableEq G] (μ : FinDist G) (l : ℕ),
      (∑ ω : Fin l → G, (aqNextProductRecordLaw μ l).prob ω) = 1)
  ∧ (∀ (G : Type*) [Fintype G] [DecidableEq G] (μ : FinDist G) (l : ℕ)
      (ω : Fin l → G), (aqNextProductRecordLaw μ l).prob ω = μ.probOf ω)
  ∧ (∀ (G : Type*) [Fintype G] [DecidableEq G] (μ : FinDist G) (l : ℕ)
      (E : (Fin l → G) → Prop) [DecidablePred E],
      (∑ ω ∈ Finset.univ.filter E, (aqNextProductRecordLaw μ l).prob ω)
        = FinDist.probEvent (L := l) μ E)

def clause17_endpoint : Prop :=
  (∀ (X : Type) [Fintype X] (a₁ a₂ : X),
      aspCompactIndex (X := X) a₁ = aspCompactIndex (X := X) a₂ → a₁ = a₂)
  ∧ (∀ (X : Type) [Fintype X] (z : Fin (Fintype.card X)),
      ∃ x : X, aspCompactIndex (X := X) x = z)
  ∧ (∀ (m : ℕ), m ≠ 0 → m ≤ 2 ^ aspCompactWidth m)
  ∧ (∀ (X : Type) [Fintype X], (Set.range (aspCompactIndex (X := X))).ncard = Fintype.card X)

end Qatlib.Concepts.FourierRecovery.ModularFourier.HspRecoveryDefs
