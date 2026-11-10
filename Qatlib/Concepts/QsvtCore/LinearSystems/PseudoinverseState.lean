/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.BlockEncoding.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def IsMinimumNormSolutionState (A : Matrix O I ℂ) (b : QState O)
    (φ : QState I) (η : ℝ) : Prop :=
  ∃ x : QState I,
    A *ᵥ x = b ∧
    (∀ y : QState I, A *ᵥ y = b → ‖stateVector x‖ ≤ ‖stateVector y‖) ∧
    x ≠ 0 ∧ Normalized φ ∧
    ‖stateVector φ - NormedSpace.normalize (stateVector x)‖ ≤ η

omit [DecidableEq O] in

theorem matrixPseudoinverse_mulVec_solves (A : Matrix O I ℂ) (b : QState O)
    (hb : ∃ z : QState I, A *ᵥ z = b) : A *ᵥ (matrixPseudoinverse A *ᵥ b) = b := by
  obtain ⟨z, rfl⟩ := hb
  calc
    A *ᵥ (matrixPseudoinverse A *ᵥ (A *ᵥ z)) =
        (A * matrixPseudoinverse A * A) *ᵥ z := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = A *ᵥ z := by rw [mul_matrixPseudoinverse_mul]

omit [DecidableEq O] in

theorem matrixPseudoinverse_mulVec_minimumNorm (A : Matrix O I ℂ) (b : QState O)
    {y : QState I} (hy : A *ᵥ y = b) :
    ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ ≤ ‖stateVector y‖ := by
  have he : matrixPseudoinverse A *ᵥ b = (matrixPseudoinverse A * A) *ᵥ y := by
    rw [← hy, Matrix.mulVec_mulVec]
  rw [he]
  calc
    _ ≤ ‖matrixPseudoinverse A * A‖ * ‖stateVector y‖ := stateVector_mulVec_norm_le _ _
    _ ≤ 1 * ‖stateVector y‖ := mul_le_mul_of_nonneg_right
      (orthogonalProjector_spectralNorm_le_one (matrixPseudoinverse_projectors A).2)
      (norm_nonneg _)
    _ = ‖stateVector y‖ := one_mul _

theorem one_le_pseudoinverse_mulVec_norm {A : Matrix O I ℂ} (hA : ‖A‖ ≤ 1)
    {b : QState O} (hb : Normalized b) (hrange : ∃ z : QState I, A *ᵥ z = b) :
    1 ≤ ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := by
  have hs := matrixPseudoinverse_mulVec_solves A b hrange
  calc
    1 = ‖stateVector b‖ := ((normalized_iff_stateVector_norm b).mp hb).symm
    _ = ‖stateVector (A *ᵥ (matrixPseudoinverse A *ᵥ b))‖ := by rw [hs]
    _ ≤ ‖A‖ * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := stateVector_mulVec_norm_le _ _
    _ ≤ 1 * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := one_mul _

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem scaledPseudoinverse_postselection
    {A : Matrix O I ℂ} {U W : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {c ε : ℝ}
    (hW : BlockEncoding ((c : ℂ) • matrixPseudoinverse A) W R L 1 ε)
    {b : QState O} (hb : Normalized b) (hrange : ∃ z : QState I, A *ᵥ z = b)
    (hgap : ε < c) :
    (c - ε) ^ 2 ≤ postselectionProbability W R L b ∧
    0 < postselectionProbability W R L b ∧
      ∃ φ : QState I, postselectionOutput W R L b = some φ ∧
        IsMinimumNormSolutionState A b φ (2 * ε / c) := by
  have hc : 0 < c := lt_of_le_of_lt hW.error_nonneg hgap
  have hA : ‖A‖ ≤ 1 := by
    rw [← h.encoded]
    exact (compress_norm_le h.left_isometry h.right_isometry U).trans
      (unitary_norm_le_one h.unitary)
  have hnorm := one_le_pseudoinverse_mulVec_norm hA hb hrange
  have ht : stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b) =
      c • stateVector (matrixPseudoinverse A *ᵥ b) := by
    rw [Matrix.smul_mulVec]
    ext i
    simp [stateVector, Complex.real_smul]
  have htnorm : ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ =
      c * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := by
    rw [ht, norm_smul, Real.norm_of_nonneg hc.le]
  have htarget : c ≤ ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := by
    rw [htnorm]
    nlinarith
  have hactualGap := hgap.trans_le htarget
  have hlower :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hW hb hactualGap.le
  simp only [div_one] at hlower
  obtain ⟨hp, φ, hφ, happ⟩ :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap hW hb hactualGap
  refine ⟨?_, hp, φ, hφ, matrixPseudoinverse A *ᵥ b,
    matrixPseudoinverse_mulVec_solves A b hrange, ?_, ?_, happ.2.1, ?_⟩
  · exact (pow_le_pow_left₀ (sub_nonneg.mpr hgap.le)
      (sub_le_sub_right htarget ε) 2).trans hlower
  · intro y hy
    exact matrixPseudoinverse_mulVec_minimumNorm A b hy
  · intro hz
    have hn : ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ = 0 := by simp [hz]
    linarith
  · calc
      ‖stateVector φ - NormedSpace.normalize (stateVector (matrixPseudoinverse A *ᵥ b))‖ =
          ‖stateVector φ - NormedSpace.normalize
            (stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b))‖ := by
        rw [ht, NormedSpace.normalize_smul_of_pos hc]
      _ ≤ 2 * ε / ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := happ.2.2
      _ ≤ 2 * ε / c := div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) hW.error_nonneg) hc htarget

theorem qsvt_pseudoinverse_counted_output
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hbase : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) -
        (c : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ ε)
    {b : QState O} (hb : Normalized b) (hrange : ∃ z : QState I, A *ᵥ z = b)
    (hgap : ε < c) :
    ∃ cs : List (AdjointStep H),
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 ∧
      (c - ε) ^ 2 ≤ postselectionProbability (evaluate U cs) R L b ∧
      0 < postselectionProbability (evaluate U cs) R L b ∧
      ∃ φ : QState I, postselectionOutput (evaluate U cs) R L b = some φ ∧
        IsMinimumNormSolutionState A b φ (2 * ε / c) := by
  obtain ⟨cs, hcs, hqueries, hgates⟩ :=
    qsvt_pseudoinverse_counted_approximation h hbase zs hzs hodd c hε happrox
  exact ⟨cs, hqueries, hgates, scaledPseudoinverse_postselection h hcs hb hrange hgap⟩

end Qatlib.Concepts.QsvtCore.LinearSystems
