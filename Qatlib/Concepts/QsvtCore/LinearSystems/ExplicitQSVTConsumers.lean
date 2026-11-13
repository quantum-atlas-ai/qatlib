/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitNoisyQSVTSolver

/-!
# Scalar consumers of explicit QSVT inversion

This module supplies a two dimensional unitary oracle and a one dimensional frame encoding the
scalar `κ⁻¹`. The fixed precision consumer specializes the explicit noisy inverse solver to the
scalar matrix `1/2` and records its concrete counts and postselection guarantee. The
mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `explicit_inverse_scalar_unitary_input`: a unitary encoding of the reciprocal scalar.
* `explicit_inverse_fixed_precision_actual_consumer`: a concrete circuit with forty-seven
  queries and forty-eight gates.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- The two by two real rotation matrix with diagonal `κ⁻¹` and off diagonal magnitude `√(1 - (κ
* κ)⁻¹)`. -/
noncomputable def scalarInverseOracle (κ : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    if i = j then ((κ:ℝ)⁻¹ : ℂ)
    else if i then (-(Real.sqrt (1 - (((κ*κ : ℕ):ℝ))⁻¹) : ℂ))
      else ((Real.sqrt (1 - (((κ*κ : ℕ):ℝ))⁻¹) : ℂ))

/-- The frame embedding the one dimensional input into the false coordinate of `Bool`. -/
def scalarInverseFrame : Matrix Bool (Fin 1) ℂ :=
  Matrix.of fun b _ => if b then 0 else 1

/-- The scalar inverse frame is an isometry. -/
theorem scalarInverseFrame_isIsometry : IsIsometry scalarInverseFrame := by
  unfold IsIsometry
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarInverseFrame, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Compressing the scalar inverse oracle by its frame gives the one by one matrix with entry
`κ⁻¹`. -/
theorem scalarInverseFrame_compress (κ : ℕ) :
    scalarInverseFrameᴴ * scalarInverseOracle κ * scalarInverseFrame =
      Matrix.of (fun _ _ : Fin 1 => ((κ:ℝ)⁻¹ : ℂ)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarInverseFrame, scalarInverseOracle, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- For positive `κ`, the scalar inverse oracle is unitary. -/
theorem scalarInverseOracle_unitary {κ : ℕ} (hκ : 0 < κ) :
    scalarInverseOracle κ ∈ Matrix.unitaryGroup Bool ℂ := by
  have hpos : (0:ℝ) < (κ:ℝ)⁻¹ := by positivity
  have ha1 : ((κ:ℝ)⁻¹) ≤ 1 :=
    (inv_le_one₀ (Nat.cast_pos.mpr hκ)).mpr (by exact_mod_cast hκ)
  have h1 : (Real.sqrt (1 - ((κ:ℝ)⁻¹^2)))^2 = 1 - ((κ:ℝ)⁻¹)^2 :=
    Real.sq_sqrt (by nlinarith [ha1, hpos])
  have hkeyC : (Complex.ofReal (Real.sqrt (1 - ((κ:ℝ)⁻¹^2))) ^ 2 +
      ((Nat.cast κ : ℂ))⁻¹ ^ 2 = 1) := by
    have e0 : ((Nat.cast κ : ℂ))⁻¹ = Complex.ofReal ((κ:ℝ)⁻¹) := by
      push_cast
      rfl
    have hreal : (Real.sqrt (1 - ((κ:ℝ)⁻¹^2)))^2 + ((κ:ℝ)⁻¹)^2 = (1:ℝ) := by
      linarith [h1]
    rw [e0, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      ← Complex.ofReal_one]
    exact congrArg _ hreal
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [scalarInverseOracle, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Complex.conj_ofReal]
  all_goals ring_nf
  all_goals first
    | exact hkeyC
    | (rw [add_comm]; exact hkeyC)

/-- Every positive `κ` gives a unitary scalar inverse oracle and an isometric frame whose
compression is `κ⁻¹`. -/
theorem explicit_inverse_scalar_unitary_input :
    ∀ (κ : ℕ), 0<κ →
      scalarInverseOracle κ ∈ Matrix.unitaryGroup Bool ℂ ∧
      scalarInverseFrameᴴ * scalarInverseFrame = 1 ∧
      scalarInverseFrameᴴ * scalarInverseOracle κ * scalarInverseFrame =
        Matrix.of (fun _ _ : Fin 1 => ((κ:ℝ)⁻¹:ℂ)) := by
  intro κ hκ
  exact ⟨scalarInverseOracle_unitary hκ, scalarInverseFrame_isIsometry,
    scalarInverseFrame_compress κ⟩

/-- The one by one matrix with entry `1/2` acts on Euclidean space by scalar multiplication by
`1/2`. -/
private theorem scalarA_toEuclideanLin (u : EuclideanSpace ℂ (Fin 1)) :
    (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))).toEuclideanLin u = (1/2:ℂ) • u := by
  have hA : (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))) =
      (1/2:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [Matrix.smul_apply]
  rw [hA, map_smul, Matrix.toLpLin_one]
  simp

/-- The singular value indexed by the input dimension of the one by one matrix `1/2` is `1/2`. -/
theorem scalar_matrixSingularValues (i : Fin (Fintype.card (Fin 1))) :
    matrixSingularValues (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))) i = 1/2 := by
  have h := norm_apply_rightSingularBasis (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))) i
  rw [scalarA_toEuclideanLin, norm_smul, norm_rightSingularBasis] at h
  have hn : ‖(1/2:ℂ)‖ = 1/2 := by norm_num
  rw [hn, mul_one] at h
  exact h.symm

/-- A unitary oracle within `inverseScale 24 / 768` of the scalar oracle at `κ = 2` gives a
circuit with forty-seven queries and forty-eight gates, success probability at least `1 /
384`, and solution state error at most `3 / 8`. -/
theorem explicit_inverse_fixed_precision_actual_consumer :
    ∀ (V : Matrix Bool Bool ℂ), V ∈ Matrix.unitaryGroup Bool ℂ →
      ‖V-scalarInverseOracle 2‖ ≤ inverseScale 24/768 →
      let A := Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))
      let cs :=
          explicitInverseCircuit A (scalarInverseOracle 2) scalarInverseFrame scalarInverseFrame 2 3
      adjointQueryCount cs = 47 ∧ adjointGateCount cs = 48 ∧
      1/384 ≤ postselectionProbability (evaluate (parallelOracle V) cs) (averageFrame scalarInverseFrame) (averageFrame scalarInverseFrame) (Ket (0:Fin 1)) ∧
      ∃ φ, postselectionOutput (evaluate (parallelOracle V) cs) (averageFrame scalarInverseFrame) (averageFrame scalarInverseFrame) (Ket (0:Fin 1)) = some φ ∧
        IsMinimumNormSolutionState A (Ket (0:Fin 1)) φ (3/8) := by
  intro V hV hnoise A cs
  have hcut : explicitInverseCutoff 2 3 = 24 := rfl
  have hcounts := explicit_inverse_actual_circuit_counts A (scalarInverseOracle 2)
    scalarInverseFrame scalarInverseFrame 2 3 (by norm_num)
  have henc : ProjectedUnitaryEncoding A (scalarInverseOracle 2)
      scalarInverseFrame scalarInverseFrame := by
    refine ⟨scalarInverseOracle_unitary (by norm_num), scalarInverseFrame_isIsometry,
      scalarInverseFrame_isIsometry, ?_⟩
    show scalarInverseFrameᴴ * scalarInverseOracle 2 * scalarInverseFrame =
      Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))
    rw [scalarInverseFrame_compress 2]
    ext a b
    fin_cases a
    fin_cases b
    norm_num
  have hgap : ∀ i : Fin (Fintype.card (Fin 1)), 0 < matrixSingularValues A i →
      (2:ℝ)⁻¹ ≤ matrixSingularValues A i := by
    intro i _
    show (2:ℝ)⁻¹ ≤ matrixSingularValues (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))) i
    rw [scalar_matrixSingularValues]
    norm_num
  have hrange : ∃ z : QState (Fin 1), A *ᵥ z = Ket (0:Fin 1) := by
    refine ⟨fun _ => (2:ℂ), ?_⟩
    show (Matrix.of (fun _ _ : Fin 1 => (1/2:ℂ))) *ᵥ (fun _ => (2:ℂ)) = Ket (0:Fin 1)
    funext j
    fin_cases j
    simp [Matrix.mulVec, dotProduct, Ket]
  have hnoise' : ‖V - scalarInverseOracle 2‖ ≤
      inverseScale (explicitInverseCutoff 2 3) * ((2:ℝ)⁻¹^3)/
        (4*((explicitInverseCutoff 2 3 : ℕ):ℝ)) := by
    have h2 : ((2:ℝ)⁻¹^3) = 1/8 := by norm_num
    have heq : inverseScale 24 * ((1:ℝ)/8)/(4*((24:ℕ):ℝ)) = inverseScale 24/768 := by
      field_simp
      ring
    rw [hcut, h2, heq]
    exact hnoise
  have hmain := explicit_inverse_noisy_same_path_solution A (scalarInverseOracle 2) V
    scalarInverseFrame scalarInverseFrame 2 3 (Ket (0:Fin 1)) henc hV (by norm_num)
    (by norm_num) (normalized_ket (0:Fin 1)) hrange hgap hnoise'
  obtain ⟨hp, φ, hout, hspec⟩ := hmain
  refine ⟨?_, ?_, ?_, φ, hout, ?_⟩
  · rw [hcounts.1, hcut]
  · rw [hcounts.2, hcut]
  · calc (1:ℝ)/384 = 1/(16*((explicitInverseCutoff 2 3 : ℕ):ℝ)) := by
          rw [hcut]
          norm_num
    _ ≤ postselectionProbability (evaluate (parallelOracle V) cs)
        (averageFrame scalarInverseFrame) (averageFrame scalarInverseFrame) (Ket (0:Fin 1)) := hp
  · obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := hspec
    refine ⟨x, hx1, hx2, hx3, hx4, ?_⟩
    have hacc : 3*((2:ℝ)⁻¹^3) = 3/8 := by norm_num
    rw [hacc] at hx5
    exact hx5

end Qatlib.Concepts.QsvtCore.LinearSystems
