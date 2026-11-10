/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.RandCompile.ReferenceModel

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.RandCompile.ChannelBudget
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def exactQdriftMap {L D : ℕ} (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam t : ℝ) (n : ℕ) : Operator D →ₗ[ℂ] Operator D :=
  mixturePowerMap d (fun j => HamiltonianEvolution (K j) (t*lam/(n:ℝ))) n
noncomputable def fairQdriftActualMap {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) : Operator D →ₗ[ℂ] Operator D :=
  if weightTotal w = 0 then LinearMap.id else
    mixturePowerMap (fairQdriftLaw w j0 R)
      (fun j => HamiltonianEvolution (K j) (t*(weightTotal w:ℝ)/(n:ℝ))) n

theorem exact_qdrift_actual_finite_diamond_budget : ∀ (L D : ℕ) (d : FinDist (Fin L)) (K : Fin L → Operator D)
    (lam t : ℝ) (n : ℕ), 0 ≤ lam → 0 < n →
  (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
  finiteDiamondDistance (exactQdriftMap d K lam t n)
    (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤
    ENNReal.ofReal (2*lam^2*t^2/(n:ℝ)) ∧
  (∀ eps : ℝ, 0 < eps →
    let N := qdriftSteps lam t (2*eps)
    0 < N ∧ (N:ℝ) ≤ 2*lam^2*t^2/eps+1 ∧
    finiteDiamondDistance (exactQdriftMap d K lam t N)
      (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤ ENNReal.ofReal eps) := by
  intro L D d K lam t n hlam hn hK
  constructor
  · have h := finiteDiamondDistance_le_of_uniform
      (exactQdriftMap d K lam t n)
      (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t))
      (4*lam^2*t^2/(n : ℝ)) (by positivity) (by
        intro r X
        rw [exactQdriftMap, tensorLeft_mixturePowerMap, tensorLeft_conjBranch]
        exact qdrift_fresh_reference_global_error L D r d K lam t n hlam hn hK X)
    convert h using 1 <;> congr 1 <;> ring
  · intro eps heps
    (try dsimp only)
    have hb := qdrift_derived_precision_budget L D 0 d K lam t (2*eps) hlam (by positivity) hK
    refine ⟨hb.1, ?_, ?_⟩
    · convert hb.2.1 using 1 <;> ring
    · have h := finiteDiamondDistance_le_of_uniform
        (exactQdriftMap d K lam t (qdriftSteps lam t (2*eps)))
        (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t))
        (2*eps) (by positivity) (by
          intro r X
          rw [exactQdriftMap, tensorLeft_mixturePowerMap, tensorLeft_conjBranch]
          exact (qdrift_derived_precision_budget L D r d K lam t (2*eps) hlam (by positivity) hK).2.2 X)
      simpa using h

theorem fairQdriftActualMap_zero {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (hW : weightTotal w=0) :
    fairQdriftActualMap w j0 n R K t = LinearMap.id ∧
    conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) = LinearMap.id := by
  have hw : ∀ j, w j=0 := by
    intro j
    exact Finset.sum_eq_zero_iff.mp hW j (Finset.mem_univ j)
  have hH : (∑ j, (w j : ℂ) • K j) = 0 := by simp [hw]
  refine ⟨by simp [fairQdriftActualMap, hW], ?_⟩
  rw [hH]
  have hU : HamiltonianEvolution (0 : Operator D) t = 1 := by simp [HamiltonianEvolution]
  rw [hU]
  ext X
  simp [conjBranch_apply]

theorem fairQdriftActualMap_reference {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (fairQdriftActualMap w j0 n R K t) X = fairQdriftReferenceOutput w j0 n R K t r X := by
  by_cases hW : weightTotal w=0
  · simp [fairQdriftActualMap, fairQdriftReferenceOutput, hW]
  · rw [fairQdriftActualMap, if_neg hW, tensorLeft_mixturePowerMap]
    exact (fair_bit_qdrift_actual_fresh_channel_bridge L D n R r w j0 K t X
      (Nat.pos_of_ne_zero hW)).symm

theorem fair_qdrift_actual_finite_diamond_output : ∀ (L D n R : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t : ℝ), 0 < n →
  (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
  (∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    tensorLeft (fairQdriftActualMap w j0 n R K t) X =
      fairQdriftReferenceOutput w j0 n R K t r X) ∧
  finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
    (conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) ≤
      ENNReal.ofReal (2*(weightTotal w:ℝ)^2*t^2/(n:ℝ) + n*((2:ℝ)⁻¹)^R) ∧
  (weightTotal w = 0 → finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
    (conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) = 0) := by
  intro L D n R w j0 K t hn hK
  refine ⟨fun r X => fairQdriftActualMap_reference w j0 n R K t r X, ?_, ?_⟩
  · by_cases hW : weightTotal w=0
    · obtain ⟨hA,hB⟩ := fairQdriftActualMap_zero w j0 n R K t hW
      simp [hA,hB,finiteDiamondDistance]
    · have h := finiteDiamondDistance_le_of_uniform
        (fairQdriftActualMap w j0 n R K t)
        (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        (4*(weightTotal w : ℝ)^2*t^2/(n : ℝ)+2*n*((2 : ℝ)⁻¹)^R) (by positivity) (by
          intro r X
          rw [fairQdriftActualMap_reference, tensorLeft_conjBranch]
          exact fair_bit_qdrift_derived_sampling_and_analytic_error L D n R r w j0 K t X
            (Nat.pos_of_ne_zero hW) hn hK)
      convert h using 1 <;> congr 1 <;> ring
  · intro hW
    obtain ⟨hA,hB⟩ := fairQdriftActualMap_zero w j0 n R K t hW
    simp [hA,hB,finiteDiamondDistance]

theorem fair_qdrift_computed_finite_diamond_and_ledgers : ∀ (L D T s : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t : ℝ), 0 < weightTotal w → |t| ≤ T →
  (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
  let n := fairQdriftSteps (weightTotal w) T s
  let R := fairQdriftFuel n s
  finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
    (conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) ≤
    ENNReal.ofReal (((2:ℝ)⁻¹)^s/2) ∧
  (∀ omega : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)),
    IsUnitaryCircuit (fairQdriftCircuit w j0 n R K t omega) ∧
    QueryCount (fairQdriftCircuit w j0 n R K t omega) = 0 ∧
    GateCount (fairQdriftCircuit w j0 n R K t omega) = n ∧
    (∑ k, (fairQdriftPick w j0 R (omega k)).2.1) ≤ n*Nat.clog 2 (weightTotal w)*R ∧
    (∑ k, (fairQdriftPick w j0 R (omega k)).2.2) ≤ n*L*R) := by
  intro L D T s w j0 K t hW ht hK
  (try dsimp only)
  constructor
  · apply finiteDiamondDistance_le_of_uniform _ _ (((2 : ℝ)⁻¹)^s) (by positivity)
    intro r X
    rw [fairQdriftActualMap_reference, tensorLeft_conjBranch]
    exact fairQdrift_computed_budget_trace L D T s r w j0 K t X hW ht hK
  · intro omega
    exact fair_bit_qdrift_actual_quantum_and_classical_path_counts L D
      (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) w j0 K t omega hW
      (fun j => (hK j).1)

end Qatlib.Concepts.RandCompile.ChannelBudget
