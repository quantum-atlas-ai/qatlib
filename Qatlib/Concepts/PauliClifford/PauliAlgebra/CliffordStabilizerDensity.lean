/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDimension

/-!
# Density operators of stabilizer codes

This module scales the tableau projector product by the reciprocal of 2^(n - k), defining
`codeDensityMatrix` and its relabeled operator `codeDensity`. For consistent tableaux with
independent generators, it proves positivity, unit trace, and the expected range dimension,
relating stabilizer codes to density operators as in [NielsenChuang2010].

Full independent tableaux give pure density operators, while tableaux with no rows give the
maximally mixed operator.

## Main statements

* `codeDensity_isDensityOperator`: Consistency and generator independence give a valid density
  operator.
* `codeDensityMatrix_range`: For a consistent tableau, the matrix range is its code space.
* `codeDensity_full_isPure`: A consistent full independent tableau gives a pure density
  operator.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix
open scoped Classical ComplexOrder

/-- The tableau projector product scaled by the reciprocal of 2^(n - k), for k rows on n qubits. -/
def codeDensityMatrix {n k : ℕ} (t : Tableau n k) : Matrix (Reg n) (Reg n) ℂ :=
  ((2 : ℂ) ^ (n - k))⁻¹ • projectorAux (tableauGenerators t)

/-- The projector product of commuting Hermitian Pauli generators is positive semidefinite. -/
theorem projectorAux_posSemidef {n : ℕ} (gs : List (PauliElem n))
    (hcomm : CommutingHermitianPaulis gs) : (projectorAux gs).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (projectorAux gs)
  rw [projectorAux_star gs hcomm, projectorAux_mul_self gs hcomm] at h
  exact h

/-- The scaled projector matrix of a consistent tableau is positive semidefinite. -/
theorem codeDensityMatrix_posSemidef {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) : (codeDensityMatrix t).PosSemidef := by
  have hc : (0 : ℂ) ≤ ((2 : ℂ) ^ (n - k))⁻¹ := by
    rw [show ((2 : ℂ) ^ (n - k)) = (((2 : ℝ) ^ (n - k) : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (by positivity))
  exact Matrix.PosSemidef.smul
    (projectorAux_posSemidef _ (generators_commuting t ht)) hc

/-- The scaled projector matrix of a consistent tableau with independent generators has trace
one. -/
theorem codeDensityMatrix_trace {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Matrix.trace (codeDensityMatrix t) = 1 := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  rw [codeDensityMatrix, Matrix.trace_smul,
    trace_projectorAux_eq_pow _ (tableauGenerators_length t) hk hind, smul_eq_mul]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

/-- The tableau's scaled projector matrix relabeled as an operator on a space of dimension 2^n. -/
def codeDensity {n k : ℕ} (t : Tableau n k) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (codeDensityMatrix t)

/-- A consistent tableau with independent generators defines a density operator. -/
theorem codeDensity_isDensityOperator {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    IsDensityOperator (codeDensity t) :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.relabel_density (bitVecEquiv n) (codeDensityMatrix t)
    ⟨codeDensityMatrix_posSemidef t ht, codeDensityMatrix_trace t ht hind⟩

/-- The range of the scaled projector matrix of a consistent tableau is its code space. -/
theorem codeDensityMatrix_range {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) :
    (codeDensityMatrix t).toLin'.range = codeSpace t := by
  rw [codeDensityMatrix, map_smul,
    LinearMap.range_smul _ _ (inv_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))),
    ← codeSpace_eq_range t ht]

/-- The range of the density matrix of a consistent k-row tableau with independent generators
has dimension 2^(n - k). -/
theorem codeDensityMatrix_finrank {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ ((codeDensityMatrix t).toLin'.range) = 2 ^ (n - k) := by
  rw [codeDensityMatrix_range t ht]
  exact finrank_codeSpace_of_independent t ht hind

/-- On the code space of a consistent tableau, its scaled projector acts by the scalar 1 / 2^(n
- k). -/
theorem codeDensityMatrix_mulVec_of_mem {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    codeDensityMatrix t *ᵥ ψ = ((2 : ℂ) ^ (n - k))⁻¹ • ψ := by
  rw [codeDensityMatrix, Matrix.smul_mulVec]
  congr 1
  exact (stabilizerProjector_mem_codeSpace t ht ψ).mp hψ

/-- For a tableau with n rows on n qubits, the density matrix equals the unscaled projector
product. -/
theorem codeDensityMatrix_full {n : ℕ} (t : Tableau n n) :
    codeDensityMatrix t = projectorAux (tableauGenerators t) := by
  simp [codeDensityMatrix]

/-- The density matrix of a consistent tableau with n rows on n qubits is idempotent. -/
theorem codeDensityMatrix_full_idem {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) : codeDensityMatrix t * codeDensityMatrix t = codeDensityMatrix t := by
  simp only [codeDensityMatrix_full]
  exact projectorAux_mul_self _ (generators_commuting t ht)

/-- A consistent tableau with n independent generators on n qubits defines a pure density
operator. -/
theorem codeDensity_full_isPure {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    IsPureDensityOperator (codeDensity t) := by
  refine ⟨codeDensity_isDensityOperator t ht hind, ?_⟩
  change relabelGate (bitVecEquiv n) (codeDensityMatrix t) *
    relabelGate (bitVecEquiv n) (codeDensityMatrix t) =
      relabelGate (bitVecEquiv n) (codeDensityMatrix t)
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
      codeDensityMatrix_full_idem t ht]

/-- The density matrix of a tableau with no rows is the identity scaled by 1 / 2^n. -/
theorem codeDensityMatrix_empty_rows {n : ℕ} (t : Tableau n 0) :
    codeDensityMatrix t = ((2 : ℂ) ^ n)⁻¹ • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  have hgs : tableauGenerators t = [] := by
    exact List.length_eq_zero_iff.mp (tableauGenerators_length t)
  simp [codeDensityMatrix, hgs, projectorAux]

/-- For the empty tableau on zero qubits, the density matrix is the identity. -/
theorem codeDensityMatrix_empty_register (t : Tableau 0 0) :
    codeDensityMatrix t = (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  simp [codeDensityMatrix_empty_rows]

end Qatlib.Concepts.PauliClifford.PauliAlgebra
