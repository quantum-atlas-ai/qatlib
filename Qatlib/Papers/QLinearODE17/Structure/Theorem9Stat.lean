/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorODESystem
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Papers.QLinearODE17.StructureCore

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open scoped Matrix.Norms.L2Operator ComplexOrder

def Theorem9V3 : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (s m k p kq : ℕ) (A V D : Matrix N N ℂ)
      (h g : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N)),
    0 < m → 5 ≤ k → 0 < p → 0 < h → 1 ≤ g → 1 ≤ kq → Nat.factorial (k + 1) ≥ 2 * m →
    (∀ n : N, (Finset.univ.filter (fun c => A n c ≠ 0)).card ≤ s) →
    (∀ c : N, (Finset.univ.filter (fun n => A n c ≠ 0)).card ≤ s) →
    (∀ i j : N, i ≠ j → D i j = 0) →
    A = V * D * V⁻¹ → V * V⁻¹ = 1 → V⁻¹ * V = 1 →
    (∀ i : N, (D i i).re ≤ 0) → ‖h • A‖ ≤ 1 →
    0 < ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ →
    70 * (‖V‖ * ‖V⁻¹‖) * (m : ℝ) *
        (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) ≤
      ((Nat.factorial (k + 1) : ℕ) : ℝ) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ →
    (∀ t : ℝ, 0 ≤ t → t ≤ (m : ℝ) * h →
      ‖stateVector (taylorODESolution A b x_in t)‖ ≤
        g * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖) →
    taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b →
    ∃ κq : ℕ,
      0 < κq ∧
      (κq : ℝ) ≤ 6 * (‖V‖ * ‖V⁻¹‖) * (k : ℝ) * ((m + p : ℕ) : ℝ) *
        ((k + s + 3 : ℕ) : ℝ) ∧
      (∀ i : Fin (Fintype.card (Fin (m * (k + 1) + p + 1) × N)),
        0 < matrixSingularValues (((k + s + 3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A)) i →
          (κq : ℝ)⁻¹ ≤
            matrixSingularValues (((k + s + 3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A)) i) ∧
      ProjectedUnitaryEncoding (((k + s + 3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A))
        (1 : Matrix _ _ ℂ)
        (sparseOverlapLeft (taylorStepMatrixV2 m k p (h • A)) (k + s + 3))
        (sparseOverlapRight (taylorStepMatrixV2 m k p (h • A)) (k + s + 3)) ∧
      let nq := explicitInverseCutoff κq (kq + 2)
      let C := taylorStepMatrixV2 m k p (h • A)
      let LC := sparseOverlapLeft C (k + s + 3)
      let RC := sparseOverlapRight C (k + s + 3)
      let zhat : QState (Fin (m * (k + 1) + p + 1) × N) :=
        (((‖stateVector (taylorRHS m k p h x_in b)‖ : ℝ) : ℂ))⁻¹ • taylorRHS m k p h x_in b
      let W := evaluate (parallelOracle (1 : Matrix _ _ ℂ)) (finiteInverseWord LC RC κq kq)
      adjointQueryCount (finiteInverseWord LC RC κq kq) = 2 * nq - 1 ∧
      adjointGateCount (finiteInverseWord LC RC κq kq) = 2 * nq + 2 ∧
      ∃ φ : QState (Fin (m * (k + 1) + p + 1) × N),
        postselectionOutput W (coordinatePhaseFrame RC) (coordinatePhaseFrame LC) zhat = some φ ∧
        Normalized φ ∧
        ‖stateVector φ - NormedSpace.normalize (stateVector x)‖ ≤ (1 : ℝ) / 2 ^ (kq : ℕ) ∧
        postselectionProbability W (coordinatePhaseFrame RC) (coordinatePhaseFrame LC) zhat ≥
          (1 - (1 : ℝ) / 2 ^ (kq : ℕ) / 2) ^ 2 / (16 * (nq : ℝ)) ∧
        postselectionProbability W (coordinatePhaseFrame RC) (coordinatePhaseFrame LC) zhat *
            MeasureProb φ (taylorSuccessSet m k p) ≥
          (1 - (1 : ℝ) / 2 ^ (kq : ℕ) / 2) ^ 2 / (16 * (nq : ℝ)) *
            (max 0 (Real.sqrt (((p + 1 : ℕ) : ℝ) / ((p : ℝ) + 77 * (m : ℝ) * g ^ 2)) -
                (1 : ℝ) / 2 ^ (kq : ℕ))) ^ 2 ∧
        ((1 : ℝ) / Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) > (1 : ℝ) / 2 ^ (kq : ℕ) →
          (taylorMeasuredDensityV2 m k p φ).PosSemidef ∧
          Matrix.trace (taylorMeasuredDensityV2 m k p φ) =
            (MeasureProb φ (taylorSuccessSet m k p) : ℂ) ∧
          ∀ l : Fin (m * (k + 1) + p + 1), m * (k + 1) ≤ (l : ℕ) →
            ‖NormedSpace.normalize (stateVector (taylorBlock φ l)) -
                NormedSpace.normalize
                  (stateVector (taylorODESolution A b x_in ((m : ℝ) * h)))‖ ≤
              2 * ((1 : ℝ) / 2 ^ (kq : ℕ)) /
                  ((1 : ℝ) / Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) -
                    (1 : ℝ) / 2 ^ (kq : ℕ)) +
              1 / 12)

end Qatlib.Papers.QLinearODE17.StructureCore
