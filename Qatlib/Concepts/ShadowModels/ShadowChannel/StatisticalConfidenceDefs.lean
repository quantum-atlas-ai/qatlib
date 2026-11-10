/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleShadows
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators ComplexOrder

variable {X : Type} [Fintype X]

abbrev Block (L : ℕ) (X : Type) := Fin L → X

abbrev MainPhase (M L : ℕ) (X : Type) := Fin M → Block L X

noncomputable def centeredSq (q : FinDist X) (f : X → ℝ) (x : X) : ℝ :=
  (f x - q.expect f) ^ 2

noncomputable def pilotVariance (q : FinDist X) (f : X → ℝ) {n : ℕ}
    (ω : Fin n → X) : ℝ :=
  FinDist.avg (centeredSq q f) ω

noncomputable def pilotFourthMoment (q : FinDist X) (f : X → ℝ) : ℝ :=
  q.expect (fun x => (centeredSq q f x) ^ 2)

noncomputable def pilotLaw (q : FinDist X) (n : ℕ) : FinDist (Fin n → X) where
  prob ω := q.probOf ω
  nonneg ω := Finset.prod_nonneg fun i _ => q.nonneg _
  sum_one := q.sum_probOf n

theorem sum_mainBlockMass (q : FinDist X) (M L : ℕ) :
    (∑ x : MainPhase M L X, ∏ m, q.probOf (x m)) = 1 := by
  have hpi : Fintype.piFinset (fun _ : Fin M => (Finset.univ : Finset (Fin L → X)))
      = (Finset.univ : Finset (MainPhase M L X)) := Fintype.piFinset_univ
  calc (∑ x : MainPhase M L X, ∏ m, q.probOf (x m))
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin M => (Finset.univ : Finset (Fin L → X))),
          ∏ m, q.probOf (x m) := by rw [hpi]
    _ = ∏ m, ∑ j ∈ (Finset.univ : Finset (Fin L → X)), q.probOf j := by
          symm
          exact Finset.prod_univ_sum
            (t := fun _ : Fin M => (Finset.univ : Finset (Fin L → X)))
            (f := fun m ω => q.probOf ω)
    _ = ∏ m, (∑ j : Fin L → X, q.probOf j) := by
          exact Finset.prod_congr rfl fun m _ => rfl
    _ = 1 := by
          rw [Finset.prod_congr rfl (fun m _ => q.sum_probOf L)]
          simp

noncomputable def mainLaw (q : FinDist X) (M L : ℕ) : FinDist (MainPhase M L X) where
  prob ω := ∏ m, q.probOf (ω m)
  nonneg ω := Finset.prod_nonneg fun m _ => Finset.prod_nonneg fun i _ => q.nonneg _
  sum_one := sum_mainBlockMass q M L

noncomputable def jointPilotMainLaw (q : FinDist X) (n M L : ℕ) :
    FinDist ((Fin n → X) × MainPhase M L X) where
  prob ω := (q.probOf ω.1) * (∏ m, q.probOf (ω.2 m))
  nonneg ω := mul_nonneg (Finset.prod_nonneg fun i _ => q.nonneg _)
    (Finset.prod_nonneg fun m _ => Finset.prod_nonneg fun i _ => q.nonneg _)
  sum_one := by
    calc (∑ ω : (Fin n → X) × MainPhase M L X,
          (q.probOf ω.1) * (∏ m, q.probOf (ω.2 m)))
        = ∑ ω₁ : Fin n → X, ∑ ω₂ : MainPhase M L X,
            (q.probOf ω₁) * (∏ m, q.probOf (ω₂ m)) := by
          exact Fintype.sum_prod_type
            (fun ω : (Fin n → X) × MainPhase M L X =>
              (q.probOf ω.1) * (∏ m, q.probOf (ω.2 m)))
      _ = ∑ ω₁ : Fin n → X, q.probOf ω₁ *
          (∑ ω₂ : MainPhase M L X, ∏ m, q.probOf (ω₂ m)) := by
          exact Finset.sum_congr rfl fun ω₁ _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ ω₁ : Fin n → X, q.probOf ω₁ * 1 := by
          refine Finset.sum_congr rfl fun ω₁ _ => ?_
          rw [sum_mainBlockMass q M L]
      _ = 1 := by
          simp_rw [mul_one]
          exact q.sum_probOf n

def pilotBad (q : FinDist X) (f : X → ℝ) {n : ℕ} (tol : ℝ) (ω : Fin n → X) : Prop :=
  tol < |pilotVariance q f ω - q.variance f|

def mainBad (q : FinDist X) (f : X → ℝ) {M L : ℕ} (ε : ℝ) (ω : MainPhase M L X) : Prop :=
  ε < |q.medianOfMeans f ω - q.expect f|

noncomputable def mergedFailureMass (q : FinDist X) (f : X → ℝ) {n M L : ℕ}
    (tol ε : ℝ) : ℝ :=
  ∑ w : (Fin n → X) × MainPhase M L X,
    (jointPilotMainLaw q n M L).prob w *
      ((if pilotBad q f tol w.1 ∨ mainBad q f ε w.2 then (1 : ℝ) else 0))

structure ConfidenceBudget where

  pilotRecords : ℕ

  blockSize : ℕ

  blockCount : ℕ

  epsilon : ℝ

  pilotFailure : ℝ

  mainFailure : ℝ

def ConfidenceBudget.totalRecords (b : ConfidenceBudget) : ℕ :=
  b.pilotRecords + b.blockSize * b.blockCount

def ConfidenceBudget.totalFailure (b : ConfidenceBudget) : ℝ :=
  b.pilotFailure + b.mainFailure

end Qatlib.Concepts.ShadowModels.ShadowChannel
