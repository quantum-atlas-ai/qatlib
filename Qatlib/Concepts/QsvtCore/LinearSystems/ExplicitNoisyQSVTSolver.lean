/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ConstructivePseudoinverse
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitReciprocalCutoff

/-!
# Explicit inverse circuits with noisy oracle access

This module chooses reciprocal response phases and compiles `explicitInverseCircuit` at the
integer cutoff `explicitInverseCutoff`. It proves exact circuit counts and a scaled
pseudoinverse encoding, then bounds the effect of replacing the unitary oracle by a nearby
unitary on the same circuit. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `explicit_inverse_constructed_encoding`: the explicit reciprocal approximation as a block
  encoding.
* `explicit_inverse_noisy_access_encoding`: an encoding error bound linear in query count and
  oracle error.
* `explicit_inverse_noisy_same_path_solution`: a solution state and probability bound under a
  noise threshold.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix Polynomial
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

section PhaseWord

/-- A chosen base unit phase for the reciprocal response at positive index, with value one at
index zero. -/
noncomputable def inversePhaseBase : ℕ → ℂ
  | 0 => 1
  | (m + 1) => Classical.choose (exists_inverse_phases (n := m + 1) (Nat.succ_pos m))

/-- A chosen reciprocal response phase list at positive index, with the empty list at index
zero. -/
noncomputable def inversePhaseList : ℕ → List ℂ
  | 0 => []
  | (m + 1) =>
      Classical.choose (Classical.choose_spec
        (exists_inverse_phases (n := m + 1) (Nat.succ_pos m)))

/-- For positive `n`, the chosen phases are unit phases of length `2 * n - 1` and their response
real part is the scaled reciprocal polynomial. -/
theorem inversePhaseWord_spec {n : ℕ} (hn : 0 < n) :
    IsPhase (inversePhaseBase n) ∧ (∀ z ∈ inversePhaseList n, IsPhase z) ∧
      (inversePhaseList n).length = 2 * n - 1 ∧
      ∀ x : ℝ, ((responseP (inversePhaseBase n) (inversePhaseList n)).eval (x : ℂ)).re =
        inverseScale n * (reciprocalPolynomial n).eval x := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ m =>
    exact Classical.choose_spec (Classical.choose_spec
      (exists_inverse_phases (n := m + 1) (Nat.succ_pos m)))

end PhaseWord

/-- The adjoint compiled real part QSVT circuit using the chosen reciprocal phases at cutoff
`explicitInverseCutoff κ k`. -/
noncomputable def explicitInverseCircuit {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (_A : Matrix O I ℂ) (_U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (κ k : ℕ) : List (AdjointStep (Bool × H)) :=
  adjointCircuit (compileRealPartQSVT (rangeProjector R) (rangeProjector L)
    (inversePhaseBase (explicitInverseCutoff κ k)) (inversePhaseList (explicitInverseCutoff κ k)))

/-- For positive `κ`, the explicit inverse circuit has `2 * n - 1` queries and `2 * n` gates,
where `n = explicitInverseCutoff κ k`. -/
theorem explicit_inverse_actual_circuit_counts {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ k : ℕ)
    (hκ : 0 < κ) :
    adjointQueryCount (explicitInverseCircuit A U L R κ k) = 2*explicitInverseCutoff κ k-1 ∧
      adjointGateCount (explicitInverseCircuit A U L R κ k) = 2*explicitInverseCutoff κ k := by
  have hn : 0 < explicitInverseCutoff κ k := (explicit_inverse_cutoff_integer_formula κ k).2 hκ
  obtain ⟨_, _, hlen, _⟩ := inversePhaseWord_spec hn
  have hc : explicitInverseCircuit A U L R κ k = adjointCircuit (compileRealPartQSVT
      (rangeProjector R) (rangeProjector L)
      (inversePhaseBase (explicitInverseCutoff κ k))
      (inversePhaseList (explicitInverseCutoff κ k))) := rfl
  refine ⟨?_, ?_⟩
  · rw [hc, adjointQueryCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).1, hlen]
  · rw [hc, adjointGateCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).2, hlen]
    omega

/-- Under the singular value gap `κ⁻¹`, the explicit circuit block encodes the pseudoinverse
scaled by `inverseScale n` with error `inverseScale n * 2⁻ᵏ`. -/
theorem explicit_inverse_constructed_encoding {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ k : ℕ)
    (h : ProjectedUnitaryEncoding A U L R) (hκ : 0 < κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) :
    let n := explicitInverseCutoff κ k
    BlockEncoding ((inverseScale n:ℂ) • matrixPseudoinverse A)
        (evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k))
        (averageFrame R) (averageFrame L) 1 (inverseScale n * ((2:ℝ)⁻¹^k)) := by
  intro n
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula κ k).2 hκ
  obtain ⟨hb, hzs, hlen, hre⟩ := inversePhaseWord_spec hn
  have hc := inverseScale_pos hn
  have hδ : 0 < (κ:ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hκ)
  have hodd : (inversePhaseList n).length % 2 = 1 := by rw [hlen]; omega
  have happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(((responseP (inversePhaseBase n) (inversePhaseList n)).eval
          (matrixSingularValues A i : ℂ)).re : ℂ) -
        (inverseScale n : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤
          inverseScale n * ((2:ℝ)⁻¹^k) := by
    intro i hi
    have hx : matrixSingularValues A i ∈ Set.Icc (κ:ℝ)⁻¹ 1 :=
      ⟨hgap i hi, (encoded_singularValues_mem_unitInterval h i).2⟩
    have hs := scaledReciprocalPolynomial_error_le n (inverseScale n) hδ hx
    rw [abs_of_pos hc] at hs
    have he : (((responseP (inversePhaseBase n) (inversePhaseList n)).eval
        (matrixSingularValues A i : ℂ)).re : ℂ) =
        (C (inverseScale n : ℂ) * complexReciprocalPolynomial n).eval
          (matrixSingularValues A i : ℂ) := by
      rw [hre]
      simp [complexReciprocalPolynomial_eval_real]
    rw [he]
    calc
      _ ≤ inverseScale n * reciprocalError (κ:ℝ)⁻¹ n := hs
      _ ≤ inverseScale n * ((2:ℝ)⁻¹^k) :=
          mul_le_mul_of_nonneg_left (explicit_inverse_geometric_precision κ k hκ) hc.le
  have hW := realPart_pseudoinverse_approximation h hb (inversePhaseList n) hzs hodd
    (inverseScale n) (show 0 ≤ inverseScale n * ((2:ℝ)⁻¹^k) by positivity) happrox
  have hcir : explicitInverseCircuit A U L R κ k = adjointCircuit (compileRealPartQSVT
      (rangeProjector R) (rangeProjector L) (inversePhaseBase n) (inversePhaseList n)) := rfl
  rw [hcir, evaluate_adjointCircuit, evaluate_compileRealPartQSVT]
  exact hW

section NoisyAccess

variable {J H : Type} [Fintype J] [DecidableEq J] [Nonempty J]
  [Fintype H] [DecidableEq H]

/-- Parallel oracle lifting preserves the matrix operator norm. -/
theorem parallelOracle_norm (W : Matrix H H ℂ) :
    ‖parallelOracle (J := J) W‖ = ‖W‖ := by
  rw [parallelOracle_eq_kronecker, l2_norm_kronecker, l2_norm_one_eq, one_mul]

/-- Parallel oracle lifting preserves subtraction of matrices. -/
theorem parallelOracle_sub (U V : Matrix H H ℂ) :
    parallelOracle (J := J) (V - U) = parallelOracle (J := J) V - parallelOracle (J := J) U := by
  rw [parallelOracle_eq_kronecker V, parallelOracle_eq_kronecker U,
    parallelOracle_eq_kronecker (V - U), kronecker_sub_right]

/-- Parallel oracle lifting preserves the operator norm distance between matrices. -/
theorem parallelOracle_dist (U V : Matrix H H ℂ) :
    ‖parallelOracle (J := J) U - parallelOracle (J := J) V‖ = ‖U - V‖ := by
  rw [← parallelOracle_sub, parallelOracle_norm]

/-- A well formed adjoint circuit evaluated with a unitary parallel oracle has norm at most one. -/
theorem evaluate_parallelOracle_norm_le {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {cs : List (AdjointStep (J × H))}
    (hcs : WellFormedAdjointCircuit cs) :
    ‖evaluate (parallelOracle U) cs‖ ≤ 1 := by
  induction cs with
  | nil => exact matrix_one_norm_le
  | cons c cs ih =>
    cases c with
    | gate W =>
      simp only [WellFormedAdjointCircuit.gate_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      calc ‖W * evaluate (parallelOracle U) cs‖
          ≤ ‖W‖ * ‖evaluate (parallelOracle U) cs‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * 1 := by
            nlinarith [unitary_norm_le_one hcs.1, ih hcs.2, norm_nonneg W,
              norm_nonneg (evaluate (parallelOracle U) cs)]
        _ = 1 := by ring
    | forward =>
      simp only [WellFormedAdjointCircuit.forward_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      exact unitary_norm_le_one
        ((Matrix.unitaryGroup (J × H) ℂ).mul_mem (parallelOracle_unitary hU)
          (hcs.evaluate_unitary (parallelOracle_unitary hU)))
    | backward =>
      simp only [WellFormedAdjointCircuit.backward_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      exact unitary_norm_le_one
        ((Matrix.unitaryGroup (J × H) ℂ).mul_mem (adjoint_unitary (parallelOracle_unitary hU))
          (hcs.evaluate_unitary (parallelOracle_unitary hU)))

/-- Changing the unitary oracle in a well formed adjoint circuit changes its evaluation by at
most the query count times the oracle distance. -/
theorem evaluate_parallelOracle_oracle_error {U V : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (cs : List (AdjointStep (J × H))) (hcs : WellFormedAdjointCircuit cs) :
    ‖evaluate (parallelOracle V) cs - evaluate (parallelOracle U) cs‖ ≤
      (adjointQueryCount cs : ℝ) * ‖V - U‖ := by
  induction cs with
  | nil =>
    simp [evaluate]
  | cons c cs ih =>
    have htcs : WellFormedAdjointCircuit cs := by
      cases c with
      | gate W => exact ((WellFormedAdjointCircuit.gate_cons_iff W cs).mp hcs).2
      | forward => exact (WellFormedAdjointCircuit.forward_cons_iff cs).mp hcs
      | backward => exact (WellFormedAdjointCircuit.backward_cons_iff cs).mp hcs
    have hnormU : ‖evaluate (parallelOracle U) cs‖ ≤ 1 :=
      evaluate_parallelOracle_norm_le hU htcs
    cases c with
    | gate W =>
      simp only [WellFormedAdjointCircuit.gate_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      rw [← Matrix.mul_sub]
      calc ‖W * (evaluate (parallelOracle V) cs - evaluate (parallelOracle U) cs)‖
          ≤ ‖W‖ * ‖evaluate (parallelOracle V) cs - evaluate (parallelOracle U) cs‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ ‖W‖ * ((adjointQueryCount cs : ℝ) * ‖V - U‖) :=
            mul_le_mul_of_nonneg_left (ih htcs) (norm_nonneg W)
        _ ≤ 1 * ((adjointQueryCount cs : ℝ) * ‖V - U‖) :=
            mul_le_mul_of_nonneg_right (unitary_norm_le_one hcs.1) (by positivity)
        _ = (adjointQueryCount (AdjointStep.gate W :: cs) : ℝ) * ‖V - U‖ := by
            simp only [adjointQueryCount]
            ring
    | forward =>
      simp only [WellFormedAdjointCircuit.forward_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      have hstep := contractive_product_error (parallelOracle (J := J) V)
        (evaluate (parallelOracle V) cs) (parallelOracle (J := J) U)
        (evaluate (parallelOracle U) cs)
        (unitary_norm_le_one (parallelOracle_unitary hV)) hnormU
      calc ‖parallelOracle (J := J) V * evaluate (parallelOracle V) cs -
            parallelOracle (J := J) U * evaluate (parallelOracle U) cs‖
          ≤ ‖evaluate (parallelOracle V) cs - evaluate (parallelOracle U) cs‖ +
              ‖parallelOracle (J := J) V - parallelOracle (J := J) U‖ := hstep
        _ ≤ (adjointQueryCount cs : ℝ) * ‖V - U‖ + ‖V - U‖ := by
            rw [parallelOracle_dist]
            exact add_le_add (ih htcs) le_rfl
        _ = (adjointQueryCount (AdjointStep.forward :: cs) : ℝ) * ‖V - U‖ := by
            simp only [adjointQueryCount]
            push_cast
            ring
    | backward =>
      simp only [WellFormedAdjointCircuit.backward_cons_iff] at hcs
      simp only [evaluate, instructionMatrix]
      have hadj : ‖((parallelOracle (J := J) V))ᴴ - ((parallelOracle (J := J) U))ᴴ‖ =
          ‖V - U‖ := by
        rw [parallelOracle_adjoint V, parallelOracle_adjoint U, parallelOracle_dist,
          ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      have hstep := contractive_product_error ((parallelOracle (J := J) V))ᴴ
        (evaluate (parallelOracle V) cs) ((parallelOracle (J := J) U))ᴴ
        (evaluate (parallelOracle U) cs)
        (unitary_norm_le_one (adjoint_unitary (parallelOracle_unitary hV))) hnormU
      calc ‖((parallelOracle (J := J) V))ᴴ * evaluate (parallelOracle V) cs -
            ((parallelOracle (J := J) U))ᴴ * evaluate (parallelOracle U) cs‖
          ≤ ‖evaluate (parallelOracle V) cs - evaluate (parallelOracle U) cs‖ +
              ‖((parallelOracle (J := J) V))ᴴ - ((parallelOracle (J := J) U))ᴴ‖ := hstep
        _ ≤ (adjointQueryCount cs : ℝ) * ‖V - U‖ + ‖V - U‖ := by
            rw [hadj]
            exact add_le_add (ih htcs) le_rfl
        _ = (adjointQueryCount (AdjointStep.forward :: cs) : ℝ) * ‖V - U‖ := by
            simp only [adjointQueryCount]
            push_cast
            ring

end NoisyAccess

section Solver

variable {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

/-- An explicit inverse circuit built from a projected unitary encoding and positive `κ` is well
formed. -/
theorem explicitInverseCircuit_wellFormed {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (h : ProjectedUnitaryEncoding A U L R)
    (κ k : ℕ) (hκ : 0 < κ) :
    WellFormedAdjointCircuit (explicitInverseCircuit A U L R κ k) := by
  have hn : 0 < explicitInverseCutoff κ k := (explicit_inverse_cutoff_integer_formula κ k).2 hκ
  obtain ⟨hb, hzs, _, _⟩ := inversePhaseWord_spec hn
  exact compileRealPartQSVT_wellFormed_adjoint
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb _ hzs

/-- Replacing the oracle by a unitary within `δ` adds at most `(2 * n - 1) * δ` to the explicit
inverse encoding error under the stated singular value gap. -/
theorem explicit_inverse_noisy_access_encoding (A : Matrix O I ℂ) (U V : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ k : ℕ) (δ : ℝ)
    (h : ProjectedUnitaryEncoding A U L R) (hV : V ∈ Matrix.unitaryGroup H ℂ) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hnoise : ‖V-U‖ ≤ δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) :
    let n := explicitInverseCutoff κ k
    BlockEncoding ((inverseScale n:ℂ) • matrixPseudoinverse A)
        (evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k))
        (averageFrame R) (averageFrame L) 1
        (inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*δ) := by
  intro n
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula κ k).2 hκ
  have hc := inverseScale_pos hn
  have hclean : BlockEncoding
      ((inverseScale (explicitInverseCutoff κ k):ℂ) • matrixPseudoinverse A)
      (evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k))
      (averageFrame R) (averageFrame L) 1
      (inverseScale (explicitInverseCutoff κ k) * ((2:ℝ)⁻¹^k)) :=
    explicit_inverse_constructed_encoding A U L R κ k h hκ hgap
  have hwf := explicitInverseCircuit_wellFormed h κ k hκ
  have hWunit : evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k) ∈
      Matrix.unitaryGroup (Bool × H) ℂ :=
    hwf.evaluate_unitary (parallelOracle_unitary hV)
  have hq := explicit_inverse_actual_circuit_counts A U L R κ k hκ
  have hdist : ‖evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k) -
      evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)‖ ≤
      ((2*n-1 : ℕ):ℝ) * δ := by
    calc ‖evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k) -
          evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)‖
        = ‖evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k) -
            evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k)‖ :=
          norm_sub_rev _ _
      _ ≤ ((adjointQueryCount (explicitInverseCircuit A U L R κ k) : ℝ)) * ‖V - U‖ :=
          evaluate_parallelOracle_oracle_error h.unitary hV _ hwf
      _ = ((2*n-1 : ℕ):ℝ) * ‖V - U‖ := by rw [hq.1]
      _ ≤ ((2*n-1 : ℕ):ℝ) * δ := mul_le_mul_of_nonneg_left hnoise (by positivity)
  refine ⟨hWunit, hclean.left_isometry, hclean.right_isometry, by norm_num,
    add_nonneg (mul_nonneg hc.le (pow_nonneg (by norm_num) _))
      (mul_nonneg (by positivity) hδ), ?_⟩
  have hel := hclean.error_le
  rw [one_smul] at hel
  have hdecomp : ((inverseScale n:ℂ) • matrixPseudoinverse A) -
      compress (averageFrame R) (evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k))
        (averageFrame L) =
      (((inverseScale n:ℂ) • matrixPseudoinverse A) -
        compress (averageFrame R)
          (evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k)) (averageFrame L)) +
      (compress (averageFrame R)
          (evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k)) (averageFrame L) -
        compress (averageFrame R)
          (evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)) (averageFrame L)) := by
    abel
  rw [one_smul, hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add hel ?_
  calc ‖compress (averageFrame R)
        (evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k)) (averageFrame L) -
      compress (averageFrame R)
        (evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)) (averageFrame L)‖
      ≤ ‖evaluate (parallelOracle U) (explicitInverseCircuit A U L R κ k) -
          evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)‖ :=
        compress_sub_norm_le hclean.left_isometry hclean.right_isometry _ _
    _ ≤ ((2*n-1 : ℕ):ℝ) * δ := hdist

/-- For `k ≥ 2` and the stated oracle noise threshold, the explicit circuit yields a minimum
norm solution state within `3 * 2⁻ᵏ` with postselection probability at least `1 / (16 * n)`. -/
theorem explicit_inverse_noisy_same_path_solution (A : Matrix O I ℂ) (U V : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ k : ℕ) (b : QState O)
    (h : ProjectedUnitaryEncoding A U L R) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hκ : 0 < κ) (hk : 2 ≤ k) (hb : Normalized b) (hrange : ∃ z : QState I, A *ᵥ z = b)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) :
    let n := explicitInverseCutoff κ k
    ‖V-U‖ ≤ inverseScale n * ((2:ℝ)⁻¹^k)/(4*(n:ℝ)) →
    let W := evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k)
    1/(16*(n:ℝ)) ≤ postselectionProbability W (averageFrame R) (averageFrame L) b ∧
      ∃ φ : QState I, postselectionOutput W (averageFrame R) (averageFrame L) b = some φ ∧
        IsMinimumNormSolutionState A b φ (3*((2:ℝ)⁻¹^k)) := by
  intro n hnoise W
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula κ k).2 hκ
  have hc := inverseScale_pos hn
  have hη4 : (2:ℝ)⁻¹^k ≤ 1/4 := by
    have h1 : (2:ℝ)⁻¹^k ≤ (2:ℝ)⁻¹^2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2:ℝ)⁻¹^2 = 1/4 := by norm_num
    linarith
  have hnoisy : BlockEncoding
      ((inverseScale (explicitInverseCutoff κ k):ℂ) • matrixPseudoinverse A)
      (evaluate (parallelOracle V) (explicitInverseCircuit A U L R κ k))
      (averageFrame R) (averageFrame L) 1
      (inverseScale (explicitInverseCutoff κ k) * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖) :=
    explicit_inverse_noisy_access_encoding A U V L R κ k (‖V - U‖) h hV hκ
      (norm_nonneg _) le_rfl hgap
  have hnr : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hε' : inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖ ≤
      3 * (inverseScale n * ((2:ℝ)⁻¹^k)) / 2 := by
    have h1 : ((2*n-1:ℕ):ℝ) * ‖V-U‖ ≤ inverseScale n * ((2:ℝ)⁻¹^k) / 2 := by
      have h2n1 : ((2*n-1:ℕ):ℝ) ≤ 2*(n:ℝ) := by
        exact_mod_cast (by omega : (2*n-1:ℕ) ≤ 2*n)
      calc ((2*n-1:ℕ):ℝ) * ‖V-U‖
          ≤ ((2*n-1:ℕ):ℝ) * (inverseScale n * ((2:ℝ)⁻¹^k)/(4*(n:ℝ))) :=
            mul_le_mul_of_nonneg_left hnoise (by positivity)
        _ ≤ (2*(n:ℝ)) * (inverseScale n * ((2:ℝ)⁻¹^k)/(4*(n:ℝ))) :=
            mul_le_mul_of_nonneg_right h2n1 (by positivity)
        _ = inverseScale n * ((2:ℝ)⁻¹^k) / 2 := by
            field_simp
            ring
    linarith
  have hE8 : inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖ ≤ 3 * inverseScale n / 8 := by
    have h3 : inverseScale n * ((2:ℝ)⁻¹^k) ≤ inverseScale n / 4 := by
      nlinarith [hc, hη4]
    linarith
  have hlt : inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖ < inverseScale n := by
    nlinarith [hc, hE8]
  obtain ⟨hlower, hp, φ, hout, hspec⟩ := scaledPseudoinverse_postselection
    (projectedEncoding_average_lift h) hnoisy hb hrange hlt
  refine ⟨?_, φ, hout, ?_⟩
  · have hhalf : inverseScale n / 2 ≤
        inverseScale n - (inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖) := by
      linarith
    calc 1/(16*(n:ℝ)) = inverseScale n ^ 2 / 4 := (inverseScale_sq_div_four hn).symm
      _ = (inverseScale n / 2)^2 := by ring
      _ ≤ (inverseScale n - (inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖))^2 :=
          pow_le_pow_left₀ (div_nonneg hc.le (by norm_num)) hhalf 2
      _ ≤ postselectionProbability W (averageFrame R) (averageFrame L) b := hlower
  · obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := hspec
    refine ⟨x, hx1, hx2, hx3, hx4, ?_⟩
    have hac : 2 * (inverseScale n * ((2:ℝ)⁻¹^k) + ((2*n-1:ℕ):ℝ)*‖V-U‖) / inverseScale n
        ≤ 3*((2:ℝ)⁻¹^k) := by
      rw [div_le_iff₀ hc]
      have h7 : (3*((2:ℝ)⁻¹^k)) * inverseScale n = 3 * (inverseScale n * ((2:ℝ)⁻¹^k)) := by ring
      rw [h7]
      linarith
    exact hx5.trans hac

end Solver

end Qatlib.Concepts.QsvtCore.LinearSystems
