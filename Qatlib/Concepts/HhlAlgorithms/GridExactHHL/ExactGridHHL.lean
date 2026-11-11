/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Exact grid HHL circuits and reciprocal rotations

This module constructs a matrix with eigenvalues on a finite grid, its root-of-unity oracle, and
the conditional reciprocal flag rotation. It assembles phase estimation, flag rotation, and
inverse phase estimation into `gridHHLCircuit`, an exact finite-grid version of the
linear-system construction in [HarrowHassidimLloyd2009].

The legality theorem counts seven matrix gates and zero query steps in this circuit
representation; the oracle powers are represented inside matrix gates.

## Main statements

* `grid_hhl_spectral_matrix_and_oracle_unitary`: the spectral matrix and unitary oracle.
* `grid_hhl_flag_rotation_actual`: unitarity and reciprocal flag amplitudes.
* `grid_hhl_actual_program_legality_and_macro_counts`: circuit legality and matrix-gate counts.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Matrix
open scoped Classical

/-- The matrix obtained by conjugating the diagonal grid values `label i / M` by `V` and `Vᴴ`. -/
noncomputable def gridHHLMatrix {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (fun i => ((label i).val : ℂ) / (M : ℂ)) * Vᴴ

/-- The matrix obtained by conjugating root-of-unity phases indexed by `label` by `V` and `Vᴴ`. -/
noncomputable def gridHHLOracle {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ))) * Vᴴ

/-- Every integer power of `primRoot M` has its complex conjugate as a multiplicative inverse. -/
theorem primRoot_zpow_conj_mul (M : ℕ) (k : ℤ) :
    (starRingEnd ℂ) (primRoot M ^ k) * primRoot M ^ k = 1 := by
  rw [primRoot_conj_zpow, ← zpow_add₀ (primRoot_ne_zero M), neg_add_cancel, zpow_zero]

/-- The diagonal matrix of grid oracle phases has adjoint-times-matrix product equal to the
identity. -/
theorem gridHHLOracleDiagonal_adjoint_mul {D M : ℕ} (label : Fin D → Fin M) :
    (Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ))))ᴴ
      * Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ))) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa using (primRoot_zpow_conj_mul M ((label i).val : ℤ))
  · simp [hij]

/-- The diagonal matrix of grid oracle phases is unitary. -/
theorem gridHHLOracleDiagonal_unitary {D M : ℕ} (label : Fin D → Fin M) :
    Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ)))
      ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact gridHHLOracleDiagonal_adjoint_mul label

/-- For a positive grid size and unitary `V`, the grid matrix and oracle have the displayed
spectral forms, and the oracle is unitary. -/
theorem grid_hhl_spectral_matrix_and_oracle_unitary :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (V : Operator D), 0 < M →
      V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      gridHHLMatrix label V
          = V * Matrix.diagonal (fun i => ((label i).val : ℂ) / (M : ℂ)) * Vᴴ ∧
      gridHHLOracle label V
          = V * Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ))) * Vᴴ ∧
      gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  intro D M label V hM hV
  set Od : Operator D := Matrix.diagonal (fun i => primRoot M ^ (((label i).val : ℤ)))
    with hDdef
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have h := gridHHLOracleDiagonal_adjoint_mul (D := D) (M := M) label
  have hDD : Odᴴ * Od = 1 := by rwa [← hDdef] at h
  refine ⟨rfl, rfl, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', gridHHLOracle, ← hDdef, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show Vᴴ * (V * (Od * Vᴴ)) = (Vᴴ * V) * (Od * Vᴴ) from
      (Matrix.mul_assoc Vᴴ V (Od * Vᴴ)).symm,
    hVU, Matrix.one_mul,
    show Odᴴ * (Od * Vᴴ) = (Odᴴ * Od) * Vᴴ from (Matrix.mul_assoc Odᴴ Od Vᴴ).symm,
    hDD, Matrix.one_mul, hUV]

/-- The grid matrix and oracle satisfy their spectral formulas, with a unitary oracle whenever
`V` is unitary and the grid size is positive. -/
theorem grid_hhl_actual_spectral_input :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (V : Operator D), 0 < M →
      V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      gridHHLMatrix label V = V * Matrix.diagonal
        (fun i => ((label i).val : ℂ) / (M : ℂ)) * Vᴴ ∧
      gridHHLOracle label V = V * Matrix.diagonal
        (fun i => primRoot M ^ (((label i).val : ℤ))) * Vᴴ ∧
      gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  grid_hhl_spectral_matrix_and_oracle_unitary

/-- The reciprocal flag amplitude `c / (j / M)` at nonzero grid labels, with value zero at label
zero. -/
noncomputable def gridHHLSin (M : ℕ) (c : ℝ) (j : Fin M) : ℝ :=
  if j.val = 0 then 0 else c / ((j.val : ℝ) / (M : ℝ))

/-- The nonnegative square root of one minus the square of `gridHHLSin`. -/
noncomputable def gridHHLCos (M : ℕ) (c : ℝ) (j : Fin M) : ℝ :=
  Real.sqrt (1 - gridHHLSin M c j ^ 2)

/-- For positive grid size and `0 ≤ c ≤ 1 / M`, every reciprocal flag amplitude lies in `[0,
1]`. -/
theorem gridHHLSin_mem_unit (M : ℕ) (c : ℝ) (hM : 0 < M) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / M)
    (j : Fin M) : 0 ≤ gridHHLSin M c j ∧ gridHHLSin M c j ≤ 1 := by
  by_cases hj : j.val = 0
  · simp [gridHHLSin, hj]
  · have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hjz : (0 : ℕ) < j.val := Nat.pos_of_ne_zero hj
    have hjz' : (0 : ℝ) < j.val := by exact_mod_cast hjz
    have hden : 0 < (j.val : ℝ) / M := div_pos hjz' hMpos
    have hfrac : 1 / M ≤ (j.val : ℝ) / M := by
      have h1 : (1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hjz
      exact (div_le_div_iff_of_pos_right hMpos).mpr h1
    have hle : c ≤ (j.val : ℝ) / M := by
      calc c ≤ 1 / M := hc1
        _ ≤ (j.val : ℝ) / M := hfrac
    have hcq : c / ((j.val : ℝ) / M) ≤ 1 := by
      refine (div_le_iff₀ hden).2 ?_
      simpa using hle
    refine ⟨by simpa [gridHHLSin, hj] using div_nonneg hc0 hden.le, ?_⟩
    simpa [gridHHLSin, hj] using hcq

/-- For positive grid size and `0 ≤ c ≤ 1 / M`, the squared cosine amplitude is one minus the
squared reciprocal flag amplitude. -/
theorem gridHHLCos_sq (M : ℕ) (c : ℝ) (hM : 0 < M) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / M)
    (j : Fin M) : gridHHLCos M c j ^ 2 = 1 - gridHHLSin M c j ^ 2 := by
  obtain ⟨hs0, hs1⟩ := gridHHLSin_mem_unit M c hM hc0 hc1 j
  have hsq0 : 0 ≤ gridHHLSin M c j ^ 2 := sq_nonneg _
  have hsq1 : gridHHLSin M c j ^ 2 ≤ 1 := by nlinarith
  have harg : 0 ≤ 1 - gridHHLSin M c j ^ 2 := by nlinarith
  show (Real.sqrt (1 - gridHHLSin M c j ^ 2)) ^ 2 = 1 - gridHHLSin M c j ^ 2
  rw [Real.sq_sqrt harg]

/-- The two-by-two flag block with entries given by `gridHHLCos` and `gridHHLSin`, using a
negative sine in the upper-right entry. -/
noncomputable def gridHHLBlock (M : ℕ) (c : ℝ) (j : Fin M) : Matrix Bool Bool ℂ :=
  Matrix.of fun p q => match p, q with
    | false, false => (gridHHLCos M c j : ℂ)
    | true, false => (gridHHLSin M c j : ℂ)
    | false, true => (-(gridHHLSin M c j) : ℂ)
    | true, true => (gridHHLCos M c j : ℂ)

/-- The block-diagonal flag transformation indexed by the phase-estimation grid label. -/
noncomputable def gridHHLRotation (M : ℕ) (c : ℝ) : Matrix (Fin M × Bool) (Fin M × Bool) ℂ :=
  BlockDiag (gridHHLBlock M c)

/-- Each flag block is unitary when the grid size is positive and `0 ≤ c ≤ 1 / M`. -/
theorem gridHHLBlock_unitary (M : ℕ) (c : ℝ) (hM : 0 < M) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / M)
    (j : Fin M) : gridHHLBlock M c j ∈ Matrix.unitaryGroup Bool ℂ := by
  have hone : (gridHHLCos M c j : ℂ) * (gridHHLCos M c j : ℂ)
      + (gridHHLSin M c j : ℂ) * (gridHHLSin M c j : ℂ) = 1 := by
    have hR : gridHHLCos M c j ^ 2 + gridHHLSin M c j ^ 2 = 1 := by
      nlinarith [gridHHLCos_sq M c hM hc0 hc1 j]
    have hR' : gridHHLCos M c j * gridHHLCos M c j
        + gridHHLSin M c j * gridHHLSin M c j = 1 := by simpa [pow_two] using hR
    norm_cast
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p q
  simp only [Matrix.mul_apply, Matrix.one_apply]
  show ∑ r : Bool, (starRingEnd ℂ) (gridHHLBlock M c j r p) * gridHHLBlock M c j r q
      = (if p = q then 1 else 0)
  rcases p with _ | _ <;> rcases q with _ | _
  · simp [gridHHLBlock, add_comm, hone]
  · simp [gridHHLBlock]
    ring
  · simp [gridHHLBlock]
    ring
  · simp [gridHHLBlock, hone]

/-- For positive grid size and `0 ≤ c ≤ 1 / M`, the flag rotation is unitary and its
false-to-true amplitude is the scaled reciprocal at nonzero labels and zero at label zero. -/
theorem grid_hhl_flag_rotation_actual :
    ∀ (M : ℕ) (c : ℝ), 0 < M → 0 ≤ c → c ≤ 1 / M →
      gridHHLRotation M c ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ ∧
      ∀ j : Fin M, gridHHLRotation M c (j, true) (j, false)
        = (if j.val = 0 then 0 else (c / ((j.val : ℝ) / (M : ℝ)) : ℂ)) := by
  intro M c hM hc0 hc1
  have hunit : gridHHLRotation M c ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ := by
    show BlockDiag (gridHHLBlock M c) ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ
    exact blockDiag_unitary _ fun j => gridHHLBlock_unitary M c hM hc0 hc1 j
  refine ⟨hunit, fun j => ?_⟩
  rw [gridHHLRotation, Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_pos rfl]
  show (gridHHLSin M c j : ℂ) = _
  simp only [gridHHLSin]
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj]

/-- The reciprocal flag rotation is unitary for `0 ≤ c ≤ 1 / M`, with the prescribed reciprocal
transition amplitudes and a zero amplitude at label zero. -/
theorem grid_hhl_reciprocal_rotation_unitary :
    ∀ (M : ℕ) (c : ℝ), 0 < M → 0 ≤ c → c ≤ 1 / (M : ℝ) →
      gridHHLRotation M c ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ ∧
      ∀ j : Fin M, gridHHLRotation M c (j, true) (j, false) =
        (if j.val = 0 then 0 else (c / ((j.val : ℝ) / (M : ℝ)) : ℂ)) :=
  grid_hhl_flag_rotation_actual

/-- The equivalence rearranging `((phase, data), flag)` into `(phase, (flag, data))`. -/
def gridHHLPhaseData {D M : ℕ} : (Fin M × Fin D) × Bool ≃ Fin M × (Bool × Fin D) :=
  (Equiv.prodAssoc (Fin M) (Fin D) Bool).trans
    (Equiv.prodCongr (Equiv.refl (Fin M)) (Equiv.prodComm (Fin D) Bool))

/-- The adjoint of a unitary complex matrix is unitary. -/
theorem mem_unitaryGroup_adjoint {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Aᴴ ∈ Matrix.unitaryGroup I ℂ := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  have hstar : star Aᴴ = A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff, hstar]
  exact h

/-- The equivalence reassociating `((phase, flag), data)` into `(phase, (flag, data))`. -/
def gridHHLFlagData {D M : ℕ} : (Fin M × Bool) × Fin D ≃ Fin M × (Bool × Fin D) :=
  Equiv.prodAssoc (Fin M) Bool (Fin D)

/-- Lift a matrix acting on the phase register to the HHL workspace, acting as the identity on
the flag and data registers. -/
noncomputable def gridHHLFourier {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLPhaseData (D := D) (M := M))
    (TensorGate (I := Fin M × Fin D) (J := Bool)
      (TensorGate (I := Fin M) (J := Fin D) Q 1) 1)

/-- Lift the controlled powers of a data matrix to the HHL workspace, acting as the identity on
the flag register. -/
noncomputable def gridHHLPowers {D M : ℕ} (U : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLPhaseData (D := D) (M := M))
    (TensorGate (I := Fin M × Fin D) (J := Bool) (ControlledPowers U M) 1)

/-- Lift the phase-controlled reciprocal flag rotation to the HHL workspace, acting as the
identity on the data register. -/
noncomputable def gridHHLFlag {D M : ℕ} (c : ℝ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLFlagData (D := D) (M := M))
    (TensorGate (I := Fin M × Bool) (J := Fin D) (gridHHLRotation M c) 1)

/-- Lifting a unitary phase-register matrix by `gridHHLFourier` gives a unitary workspace
matrix. -/
theorem gridHHLFourier_unitary {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin M) ℂ) :
    gridHHLFourier (D := D) (M := M) Q
      ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  (relabelGate_mem_unitaryGroup (gridHHLPhaseData (D := D) (M := M)) _).2
    (tensorGate_unitary (tensorGate_unitary hQ (Submonoid.one_mem _))
      (Submonoid.one_mem _))

/-- The lifted controlled-powers matrix is unitary when the data matrix is unitary. -/
theorem gridHHLPowers_unitary {D M : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLPowers (D := D) (M := M) U
      ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  (relabelGate_mem_unitaryGroup (gridHHLPhaseData (D := D) (M := M)) _).2
    (tensorGate_unitary (controlledPowers_unitary U hU) (Submonoid.one_mem _))

/-- The lifted flag matrix is unitary whenever the underlying reciprocal flag rotation is
unitary. -/
theorem gridHHLFlag_unitary {D M : ℕ} (c : ℝ) (hc : gridHHLRotation M c
    ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ) :
    gridHHLFlag (D := D) (M := M) c
      ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  (relabelGate_mem_unitaryGroup (gridHHLFlagData (D := D) (M := M)) _).2
    (tensorGate_unitary hc (Submonoid.one_mem _))

/-- The three-gate phase-estimation block consisting of a Fourier transform, controlled powers,
and an inverse Fourier transform. -/
noncomputable def gridHHLQPEBlock {D M : ℕ} (U : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) :=
  [Step.gate (gridHHLFourier (D := D) (M := M) (QFTMatrix M)),
    Step.gate (gridHHLPowers (D := D) (M := M) U),
    Step.gate (gridHHLFourier (D := D) (M := M) (QFTMatrix M)ᴴ)]

/-- The three-gate inverse phase-estimation block using adjoint controlled powers between
Fourier transforms. -/
noncomputable def gridHHLQPEBlockInv {D M : ℕ} (U : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) :=
  [Step.gate (gridHHLFourier (D := D) (M := M) (QFTMatrix M)),
    Step.gate (gridHHLPowers (D := D) (M := M) U)ᴴ,
    Step.gate (gridHHLFourier (D := D) (M := M) (QFTMatrix M)ᴴ)]

/-- The exact grid HHL circuit formed by phase estimation, reciprocal flag rotation, and inverse
phase estimation. -/
noncomputable def gridHHLCircuit {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) (c : ℝ) :
    Circuit (Fin M × (Bool × Fin D)) :=
  gridHHLQPEBlock (gridHHLOracle label V) ++
    [Step.gate (gridHHLFlag (D := D) (M := M) c)] ++
  gridHHLQPEBlockInv (gridHHLOracle label V)

/-- The phase-estimation block is a unitary circuit for positive grid size and a unitary data
matrix. -/
theorem gridHHLQPEBlock_unitary {D M : ℕ} (hM : 0 < M) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : IsUnitaryCircuit (gridHHLQPEBlock (M := M) U) := by
  simp only [gridHHLQPEBlock, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨gridHHLFourier_unitary (D := D) (Q := QFTMatrix M) (qftMatrix_unitary hM),
    gridHHLPowers_unitary (D := D) (M := M) U hU,
    gridHHLFourier_unitary (D := D) (Q := (QFTMatrix M)ᴴ)
      (mem_unitaryGroup_adjoint (qftMatrix_unitary hM))⟩

/-- The inverse phase-estimation block is a unitary circuit for positive grid size and a unitary
data matrix. -/
theorem gridHHLQPEBlockInv_unitary {D M : ℕ} (hM : 0 < M) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : IsUnitaryCircuit (gridHHLQPEBlockInv (M := M) U) := by
  simp only [gridHHLQPEBlockInv, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨gridHHLFourier_unitary (D := D) (Q := QFTMatrix M) (qftMatrix_unitary hM),
    mem_unitaryGroup_adjoint
      (gridHHLPowers_unitary (D := D) (M := M) U hU),
    gridHHLFourier_unitary (D := D) (Q := (QFTMatrix M)ᴴ)
      (mem_unitaryGroup_adjoint (qftMatrix_unitary hM))⟩

/-- For positive grid size, unitary `V`, and `0 ≤ c ≤ 1 / M`, the exact grid HHL circuit is
unitary and contains zero query steps and seven matrix gates. -/
theorem grid_hhl_actual_program_legality_and_macro_counts :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (V : Operator D) (c : ℝ), 0 < M →
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 ≤ c → c ≤ 1 / M →
      IsUnitaryCircuit (gridHHLCircuit label V c) ∧
      QueryCount (gridHHLCircuit label V c) = 0 ∧ GateCount (gridHHLCircuit label V c) = 7 := by
  intro D M label V c hM hV hc0 hc1
  have hrot : gridHHLRotation M c ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ :=
    (grid_hhl_flag_rotation_actual M c hM hc0 hc1).1
  have hOrt : gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    (grid_hhl_spectral_matrix_and_oracle_unitary D M label V hM hV).2.2
  have hleg : IsUnitaryCircuit (gridHHLCircuit label V c) := by
    simp only [gridHHLCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate]
    exact ⟨⟨gridHHLQPEBlock_unitary hM (gridHHLOracle label V) hOrt,
      gridHHLFlag_unitary c hrot, isUnitaryCircuit_nil⟩,
      gridHHLQPEBlockInv_unitary hM (gridHHLOracle label V) hOrt⟩
  have hq : QueryCount (gridHHLCircuit label V c) = 0 := by
    rw [gridHHLCircuit, queryCount_append, queryCount_append, queryCount_gate,
      queryCount_nil, gridHHLQPEBlock, gridHHLQPEBlockInv]
    simp only [queryCount_nil, queryCount_gate]
  have hg : GateCount (gridHHLCircuit label V c) = 7 := by
    rw [gridHHLCircuit, gateCount_append, gateCount_append, gateCount_gate,
      gateCount_nil, gridHHLQPEBlock, gridHHLQPEBlockInv]
    simp only [gateCount_nil, gateCount_gate]
  exact ⟨hleg, hq, hg⟩

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
