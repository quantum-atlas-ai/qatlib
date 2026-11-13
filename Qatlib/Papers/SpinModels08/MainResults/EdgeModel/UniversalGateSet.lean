/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.EdgeModel.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Edge-model realizations of elementary gates

This module constructs single-qubit and diagonal two-qubit gates from edge weights and factors
an edge-model layer into these two kinds of layers. It realizes the displayed elementary gates
as edge gates and identifies partition contractions with circuit matrix elements in the setting
of [VanDenNestEtAl2009].

## Main statements

* `emLayer_eq_sqLayer_mul_diagLayer`: an edge-model layer factors into single-qubit and diagonal
  layers.
* `universal_gate_set_isEdgeModel`: each displayed elementary gate has an edge-weight
  representation.
* `isingType_amplitude_eq_partition`: the all-zero matrix element equals the partition
  contraction.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet

open Qatlib.Papers.SpinModels08.MainResults
open Qatlib.Papers.SpinModels08.MainResults.EdgeModel

/-- The single-qubit matrix with entries given by the edge weight `w`. -/
def singleQubitGate (w : EdgeW 2) : Matrix (Fin 2) (Fin 2) ℂ := fun i j => w i j

/-- The entries of a single-qubit edge gate are its edge weights. -/
theorem singleQubitGate_apply (w : EdgeW 2) (i j : Fin 2) :
    singleQubitGate w i j = w i j := rfl

/-- The diagonal two-qubit matrix with diagonal entries given by `v`. -/
def diagTwoQubitGate (v : EdgeW 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => if i = k ∧ j = l then v i j else 0

/-- A diagonal two-qubit edge gate has weight `v i j` on its diagonal and zero elsewhere. -/
theorem diagTwoQubitGate_apply (v : EdgeW 2) (i j k l : Fin 2) :
    diagTwoQubitGate v (i, j) (k, l) = if i = k ∧ j = l then v i j else 0 := rfl

/-- The configuration matrix whose entries are products of independent single-site edge weights. -/
def sqLayer {N : ℕ} (hW : Fin N → EdgeW 2) : Matrix (Config 2 N) (Config 2 N) ℂ :=
  fun l j => ∏ r, hW r (l r) (j r)

/-- The diagonal configuration matrix whose diagonal is the nearest-neighbor bond product. -/
def diagLayer {N : ℕ} (vW : Fin N → EdgeW 2) : Matrix (Config 2 N) (Config 2 N) ℂ :=
  fun l j => if l = j then bondProd vW j else 0

/-- An edge-model transfer layer factors as its single-qubit layer followed by its diagonal bond
layer. -/
theorem emLayer_eq_sqLayer_mul_diagLayer {N : ℕ} (hW vW : Fin N → EdgeW 2) :
    emLayer (fun (_ : Fin 1) => hW) (fun (_ : Fin 1) => vW) 0
      = sqLayer hW * diagLayer vW := by
  ext l j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [emLayer, sqLayer, diagLayer]
  · intro k _ hk
    simp [diagLayer, hk]
  · intro hj
    simp at hj

/-- The unnormalized Hadamard weights, equal to minus one only at `(1, 1)`. -/
def hadamardWeight : EdgeW 2 := fun i j => if i = 1 ∧ j = 1 then -1 else 1

/-- The controlled-phase weights, equal to minus one only when both spins are one. -/
def cpWeight : EdgeW 2 := fun i j => if i = 1 ∧ j = 1 then -1 else 1

/-- The identity matrix on a single qubit. -/
def gateI1 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- The Hadamard matrix obtained by normalizing `hadamardWeight` by `sqrt 2`. -/
def gateH : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • singleQubitGate hadamardWeight

/-- The single-qubit diagonal phase gate with entries one and `exp (I * π / 8)`. -/
def gateP : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, Complex.exp ((Real.pi / 8 : ℝ) * Complex.I)]

/-- The identity matrix on two qubits. -/
def gateI2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1

/-- The diagonal controlled-phase gate constructed from `cpWeight`. -/
def gateCP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := diagTwoQubitGate cpWeight

/-- The single-qubit identity has the Kronecker-delta entries. -/
theorem gateI1_apply (i j : Fin 2) :
    gateI1 i j = if i = j then 1 else 0 := Matrix.one_apply

/-- Each Hadamard entry is the corresponding Hadamard weight divided by `sqrt 2`. -/
theorem gateH_apply (i j : Fin 2) :
    gateH i j = ((Real.sqrt 2)⁻¹ : ℂ) * hadamardWeight i j := by
  simp [gateH, singleQubitGate, Matrix.smul_apply]

/-- The phase gate is diagonal, with entries one and `exp (I * π / 8)`. -/
theorem gateP_apply (i j : Fin 2) :
    gateP i j = if i = j then (if i = 0 then 1 else Complex.exp ((Real.pi / 8 : ℝ) * Complex.I))
      else 0 := by
  fin_cases i <;> fin_cases j <;> simp [gateP]

/-- The two-qubit identity has entry one exactly when both spin indices agree. -/
theorem gateI2_apply (i j k l : Fin 2) :
    gateI2 (i, j) (k, l) = if i = k ∧ j = l then 1 else 0 := by
  simp [gateI2, Matrix.one_apply, Prod.mk.injEq]

/-- The controlled-phase gate has the specified edge weights on the diagonal and zero elsewhere. -/
theorem gateCP_apply (i j k l : Fin 2) :
    gateCP (i, j) (k, l) = if i = k ∧ j = l then cpWeight i j else 0 := rfl

/-- The controlled-phase diagonal entry is minus one exactly for the spin pair `(1, 1)`. -/
theorem gateCP_diag (i j : Fin 2) :
    gateCP (i, j) (i, j) = if i = 1 ∧ j = 1 then -1 else 1 := by
  rw [gateCP_apply]
  simp [cpWeight]

/-- The single-qubit identity is the edge gate for the Kronecker-delta weights. -/
theorem gateI1_eq_edgeGate :
    gateI1 = singleQubitGate (fun i j => if i = j then (1 : ℂ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gateI1, singleQubitGate]

/-- The Hadamard gate is the edge gate for the normalized Hadamard weights. -/
theorem gateH_eq_edgeGate :
    gateH = singleQubitGate (fun i j => ((Real.sqrt 2)⁻¹ : ℂ) * hadamardWeight i j) := by
  ext i j
  exact gateH_apply i j

/-- The phase gate is the edge gate for its diagonal exponential weights. -/
theorem gateP_eq_edgeGate :
    gateP = singleQubitGate (fun i j =>
      if i = j then (if i = 0 then 1 else Complex.exp ((Real.pi / 8 : ℝ) * Complex.I))
      else 0) := by
  ext i j
  exact gateP_apply i j

/-- The two-qubit identity is the diagonal edge gate with constant weight one. -/
theorem gateI2_eq_edgeGate :
    gateI2 = diagTwoQubitGate (fun _ _ => (1 : ℂ)) := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp [gateI2, diagTwoQubitGate, Matrix.one_apply, Prod.mk.injEq]

/-- The controlled-phase gate is the diagonal edge gate associated with `cpWeight`. -/
theorem gateCP_eq_edgeGate : gateCP = diagTwoQubitGate cpWeight := rfl

/-- Each of the five displayed elementary gates possesses the stated single-qubit or diagonal
two-qubit edge-weight representation [VanDenNestEtAl2009]. -/
theorem universal_gate_set_isEdgeModel :
    (∃ w : EdgeW 2, gateI1 = singleQubitGate w) ∧
    (∃ w : EdgeW 2, gateH = singleQubitGate w) ∧
    (∃ w : EdgeW 2, gateP = singleQubitGate w) ∧
    (∃ v : EdgeW 2, gateI2 = diagTwoQubitGate v) ∧
    (∃ v : EdgeW 2, gateCP = diagTwoQubitGate v) :=
  ⟨⟨_, gateI1_eq_edgeGate⟩, ⟨_, gateH_eq_edgeGate⟩, ⟨_, gateP_eq_edgeGate⟩,
    ⟨_, gateI2_eq_edgeGate⟩, ⟨_, gateCP_eq_edgeGate⟩⟩

/-- The configuration with spin zero at every site. -/
def allZeroConfig (N : ℕ) : Config 2 N := fun _ => 0

/-- The all-zero circuit matrix element equals the corresponding edge-model partition
contraction [VanDenNestEtAl2009]. -/
theorem isingType_amplitude_eq_partition {N M : ℕ}
    (hW vW : Fin M → Fin N → EdgeW 2) :
    matElem (emCircuit M hW vW) (allZeroConfig N) (allZeroConfig N) =
      emPartition0 M hW vW (allZeroConfig N) (allZeroConfig N) :=
  matElem_emCircuit_eq M hW vW _ _

/-- The property that every supplied binary edge-model partition contraction can be represented
as a matrix element. -/
def IsingAmplitudeForm : Prop :=
  ∀ (N M : ℕ) (hW vW : Fin M → Fin N → EdgeW 2) (L R : Config 2 N),
    ∃ (C : Matrix (Config 2 N) (Config 2 N) ℂ),
      matElem C L R = emPartition0 M hW vW L R

/-- Every binary edge-model partition contraction has the matrix-element representation
specified by `IsingAmplitudeForm`. -/
theorem ising_amplitude_form : IsingAmplitudeForm := by
  intro N M hW vW L R
  exact ⟨emCircuit M hW vW, matElem_emCircuit_eq M hW vW L R⟩

end Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet
