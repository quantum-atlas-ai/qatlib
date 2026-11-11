/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.ThermalTrace
import Qatlib.Papers.ThermalRate98.MainResults.PhysicalRateFormula
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Uniform initialization and physical propagation

This module defines `uniformPreparationWord` and proves that its parallel Hadamard gate prepares
the normalized uniform register state. It also records the register dimension identity
associated with the position encoding in [LidarWang1999].

For finite matrices, the module establishes the adjoint formula, unitarity, preservation of
state normalization, and the time composition law for `physicalPropagation`.

## Main statements

* `uniformPreparationWord_run`: the preparation word sends the zero basis state to the uniform
  state.
* `uniformPreparationWord_resources`: the word is unitary and contains one gate step and no
  queries.
* `physicalPropagation_unitary`: a Hermitian Hamiltonian generates unitary propagation.
* `physicalPropagation_mul`: propagation times add under matrix multiplication.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The circuit consisting of one `HadamardN n` gate step on the `n`-qubit register. -/
def uniformPreparationWord (n : ℕ) : Circuit (Reg n) :=
  [Step.gate (HadamardN n)]

/-- Running the uniform preparation word on the all-zero basis state produces the uniform
register state. -/
theorem uniformPreparationWord_run (n : ℕ) :
    Run 1 (uniformPreparationWord n) (Ket (ZeroStr n)) = Uniform (Reg n) := by
  simpa only [uniformPreparationWord, run_gate, run_nil, ApplyGate]
    using applyGate_hadamardN_ket_zero n

/-- The uniform preparation word is a unitary circuit with one gate step and zero query steps. -/
theorem uniformPreparationWord_resources (n : ℕ) :
    IsUnitaryCircuit (uniformPreparationWord n) ∧
      GateCount (uniformPreparationWord n) = 1 ∧
      QueryCount (uniformPreparationWord n) = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [uniformPreparationWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact hadamardN_unitary n

/-- The state obtained by running the uniform preparation word on the zero basis state is
normalized. -/
theorem uniformPreparationWord_normalized (n : ℕ) :
    Normalized (Run 1 (uniformPreparationWord n) (Ket (ZeroStr n))) := by
  rw [uniformPreparationWord_run]
  exact normalized_uniform (by simp)

/-- An `l * M` qubit register has dimension equal to the product of `M` coordinate dimensions `2
^ l`. -/
theorem uniformPreparationWord_register_count (l M : ℕ) :
    (2 : ℕ) ^ (l * M) = ((2 : ℕ) ^ l) ^ M :=
  source_register_dimension l M

/-- For Hermitian `H`, the adjoint of physical propagation is the exponential of `(i t/ħ) H`. -/
theorem physicalPropagation_adjoint (t ħ : ℝ) (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (physicalPropagation t ħ H)ᴴ =
      NormedSpace.exp ((Complex.I * ((t/ħ : ℝ) : ℂ)) • H) := by
  unfold physicalPropagation
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- A complex diagonal matrix is unitary if every diagonal entry has complex conjugate times
itself equal to one. -/
theorem diagonal_unitary_of_unit {d : I → ℂ}
    (hd : ∀ i, star (d i) * d i = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simpa only [Complex.star_def] using! hd i
  · simp [h]

/-- Physical propagation is unitary when `H` has the given unitary diagonalization with real
eigenvalues. -/
theorem physicalPropagation_unitary_spectral (t ħ : ℝ) (H V : Matrix I I ℂ) (E : I → ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V * Matrix.diagonal (fun i => (E i : ℂ)) * Vᴴ) :
    physicalPropagation t ħ H ∈ Matrix.unitaryGroup I ℂ := by
  rw [physicalPropagation,
    physical_scaled_exp (-Complex.I * ((t/ħ : ℝ) : ℂ)) H V E hV hH]
  have hD : Matrix.diagonal
      (fun i => Complex.exp ((-Complex.I * ((t/ħ : ℝ) : ℂ)) * (E i : ℂ))) ∈
      Matrix.unitaryGroup I ℂ := by
    apply diagonal_unitary_of_unit
    intro i
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    have hz : (starRingEnd ℂ)
        (-Complex.I * ((t/ħ : ℝ) : ℂ) * (E i : ℂ)) +
        (-Complex.I * ((t/ħ : ℝ) : ℂ) * (E i : ℂ)) = 0 := by
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hz, Complex.exp_zero]
  have hVadj : Vᴴ ∈ Matrix.unitaryGroup I ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hV
  exact (Matrix.unitaryGroup I ℂ).mul_mem
    ((Matrix.unitaryGroup I ℂ).mul_mem hV hD) hVadj

/-- A finite Hermitian Hamiltonian generates a unitary physical propagation matrix for all real
`t` and `ħ`. -/
theorem physicalPropagation_unitary (t ħ : ℝ) (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    physicalPropagation t ħ H ∈ Matrix.unitaryGroup I ℂ := by
  obtain ⟨V, E, hV, hdiag⟩ := physical_hamiltonian_spectral_exists H hH
  exact physicalPropagation_unitary_spectral t ħ H V E hV hdiag

/-- Physical propagation generated by a Hermitian Hamiltonian preserves normalization of the
input state. -/
theorem physicalPropagation_normalized (t ħ : ℝ) (H : Matrix I I ℂ) (hH : H.IsHermitian)
    {ψ : QState I} (hψ : Normalized ψ) :
    Normalized (physicalPropagation t ħ H *ᵥ ψ) :=
  normalized_applyGate (physicalPropagation_unitary t ħ H hH) hψ

/-- Multiplying physical propagation matrices at times `t₁` and `t₂` gives physical propagation
at time `t₁ + t₂`. -/
theorem physicalPropagation_mul (t₁ t₂ ħ : ℝ) (H : Matrix I I ℂ) :
    physicalPropagation t₁ ħ H * physicalPropagation t₂ ħ H =
      physicalPropagation (t₁ + t₂) ħ H := by
  have hc : Commute ((-Complex.I * ((t₁/ħ : ℝ) : ℂ)) • H)
      ((-Complex.I * ((t₂/ħ : ℝ) : ℂ)) • H) :=
    ((Commute.refl H).smul_right (-Complex.I * ((t₂/ħ : ℝ) : ℂ))).smul_left
      (-Complex.I * ((t₁/ħ : ℝ) : ℂ))
  unfold physicalPropagation
  rw [← Matrix.exp_add_of_commute _ _ hc]
  congr 1
  rw [← add_smul]
  congr 1
  have e1 : ((t₁/ħ : ℝ) : ℂ) = (t₁ : ℂ) * (ħ : ℂ)⁻¹ := by
    rw [Complex.ofReal_div]; ring
  have e2 : ((t₂/ħ : ℝ) : ℂ) = (t₂ : ℂ) * (ħ : ℂ)⁻¹ := by
    rw [Complex.ofReal_div]; ring
  have e3 : (((t₁ + t₂)/ħ : ℝ) : ℂ) = ((t₁ : ℂ) + (t₂ : ℂ)) * (ħ : ℂ)⁻¹ := by
    rw [Complex.ofReal_div, Complex.ofReal_add]; ring
  rw [e1, e2, e3]
  ring

end Qatlib.Papers.ThermalRate98.MainResults
