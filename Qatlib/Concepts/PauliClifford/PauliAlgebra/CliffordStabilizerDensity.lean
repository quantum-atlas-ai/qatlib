/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDimension
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

def codeDensityMatrix {n k : ℕ} (t : Tableau n k) : Matrix (Reg n) (Reg n) ℂ :=
  ((2 : ℂ) ^ (n - k))⁻¹ • projectorAux (tableauGenerators t)

theorem projectorAux_posSemidef {n : ℕ} (gs : List (PauliElem n))
    (hcomm : CommutingHermitianPaulis gs) : (projectorAux gs).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (projectorAux gs)
  rw [projectorAux_star gs hcomm, projectorAux_mul_self gs hcomm] at h
  exact h

theorem codeDensityMatrix_posSemidef {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) : (codeDensityMatrix t).PosSemidef := by
  have hc : (0 : ℂ) ≤ ((2 : ℂ) ^ (n - k))⁻¹ := by
    rw [show ((2 : ℂ) ^ (n - k)) = (((2 : ℝ) ^ (n - k) : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (by positivity))
  exact Matrix.PosSemidef.smul
    (projectorAux_posSemidef _ (generators_commuting t ht)) hc

theorem codeDensityMatrix_trace {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Matrix.trace (codeDensityMatrix t) = 1 := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  rw [codeDensityMatrix, Matrix.trace_smul,
    trace_projectorAux_eq_pow _ (tableauGenerators_length t) hk hind, smul_eq_mul]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

def codeDensity {n k : ℕ} (t : Tableau n k) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (codeDensityMatrix t)

theorem codeDensity_isDensityOperator {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    IsDensityOperator (codeDensity t) :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.relabel_density (bitVecEquiv n) (codeDensityMatrix t)
    ⟨codeDensityMatrix_posSemidef t ht, codeDensityMatrix_trace t ht hind⟩

theorem codeDensityMatrix_range {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) :
    (codeDensityMatrix t).toLin'.range = codeSpace t := by
  rw [codeDensityMatrix, map_smul,
    LinearMap.range_smul _ _ (inv_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))),
    ← codeSpace_eq_range t ht]

theorem codeDensityMatrix_finrank {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ ((codeDensityMatrix t).toLin'.range) = 2 ^ (n - k) := by
  rw [codeDensityMatrix_range t ht]
  exact finrank_codeSpace_of_independent t ht hind

theorem codeDensityMatrix_mulVec_of_mem {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    codeDensityMatrix t *ᵥ ψ = ((2 : ℂ) ^ (n - k))⁻¹ • ψ := by
  rw [codeDensityMatrix, Matrix.smul_mulVec]
  congr 1
  exact (stabilizerProjector_mem_codeSpace t ht ψ).mp hψ

theorem codeDensityMatrix_full {n : ℕ} (t : Tableau n n) :
    codeDensityMatrix t = projectorAux (tableauGenerators t) := by
  simp [codeDensityMatrix]

theorem codeDensityMatrix_full_idem {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) : codeDensityMatrix t * codeDensityMatrix t = codeDensityMatrix t := by
  simp only [codeDensityMatrix_full]
  exact projectorAux_mul_self _ (generators_commuting t ht)

theorem codeDensity_full_isPure {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    IsPureDensityOperator (codeDensity t) := by
  refine ⟨codeDensity_isDensityOperator t ht hind, ?_⟩
  change relabelGate (bitVecEquiv n) (codeDensityMatrix t) *
    relabelGate (bitVecEquiv n) (codeDensityMatrix t) =
      relabelGate (bitVecEquiv n) (codeDensityMatrix t)
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
      codeDensityMatrix_full_idem t ht]

theorem codeDensityMatrix_empty_rows {n : ℕ} (t : Tableau n 0) :
    codeDensityMatrix t = ((2 : ℂ) ^ n)⁻¹ • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  have hgs : tableauGenerators t = [] := by
    exact List.length_eq_zero_iff.mp (tableauGenerators_length t)
  simp [codeDensityMatrix, hgs, projectorAux]

theorem codeDensityMatrix_empty_register (t : Tableau 0 0) :
    codeDensityMatrix t = (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  simp [codeDensityMatrix_empty_rows]

end Qatlib.Concepts.PauliClifford.PauliAlgebra
