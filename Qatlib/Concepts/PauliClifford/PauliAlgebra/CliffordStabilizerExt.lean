/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerMeasurement
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCanonical

/-!
# Combined guarantees for Clifford stabilizer evolution

This module combines projector covariance, code density, code-space dimension, exclusion of the
negative identity, and Pauli measurement covariance for legal Clifford runs. The theorem
`frontier1` packages these guarantees for consistent tableaux with independent generators, in
the binary stabilizer setting of [DehaeneDeMoor2003].

For full independent tableaux it also proves purity and uniqueness of normalized evolved code
states up to a scalar of norm one.

## Main statements

* `frontier1`: The combined projector, density, dimension, subgroup, and measurement guarantees.
* `pure_density_after_run`: Full independent tableaux retain pure code density after a legal
  run.
* `normalized_run_unique`: Normalized states in the evolved full code differ by a scalar of norm
  one.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix

/-- A legal Clifford run on a consistent tableau with independent generators preserves projector
covariance, a valid code density, dimension 2^(n - k), and exclusion of the negative
identity. Simultaneously transforming a Hermitian Pauli observable preserves its measurement
probabilities. -/
theorem frontier1 {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t))
    (gates : List (CliffordGate n)) (hg : ∀ g ∈ gates, legalGate g) :
    projectorAux (tableauGenerators (run gates t)) =
      conjugate (Uword gates) (projectorAux (tableauGenerators t)) ∧
    IsDensityOperator (codeDensity (run gates t)) ∧
    Module.finrank ℂ (codeSpace (run gates t)) = 2^(n-k) ∧
    Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.minusI n ∉
      generatedSubgroup (tableauGenerators (run gates t)) ∧
    ∀ (p : PauliElem n) (hp : IsHermitianPauli p) (b : Bool),
      instrumentProb (pauliInstrument (actionWord gates p) ((actionWord_hermitian_iff gates p).mpr hp))
        (codeDensity (run gates t)) b =
      instrumentProb (pauliInstrument p hp) (codeDensity t) b := by
  exact ⟨tableau_projector_covariance gates hg t,
    codeDensity_run_isDensityOperator gates hg t ht hind,
    finrank_codeSpace_run gates hg t ht hind,minusI_not_mem_run gates hg t ht hind,
    fun p hp b => pauliInstrument_run_probability gates hg t p hp b⟩

/-- A legal Clifford run on a consistent tableau with n independent generators on n qubits
yields a pure code density operator. -/
theorem pure_density_after_run {n : ℕ} (t : Tableau n n) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t))
    (gates : List (CliffordGate n)) (hg : ∀ g ∈ gates, legalGate g) :
    IsPureDensityOperator (codeDensity (run gates t)) := by
  refine ⟨codeDensity_run_isDensityOperator gates hg t ht hind,?_⟩
  change relabelGate (bitVecEquiv n) (codeDensityMatrix (run gates t)) *
    relabelGate (bitVecEquiv n) (codeDensityMatrix (run gates t)) =
      relabelGate (bitVecEquiv n) (codeDensityMatrix (run gates t))
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
    codeDensityMatrix_full_idem (run gates t) (consistent_run gates hg t ht)]

/-- Two normalized vectors in a one-dimensional complex subspace of register states differ by a
scalar of norm one. -/
theorem normalized_line_unique {n : ℕ} (S : Submodule ℂ (QState (Reg n)))
    (hdim : Module.finrank ℂ S = 1) (ψ φ : QState (Reg n))
    (hψ : ψ ∈ S) (hφ : φ ∈ S) (hnψ : Normalized ψ) (hnφ : Normalized φ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ φ = lam • ψ := by
  have hψne : ψ ≠ 0 := by
    intro hz
    have hsum := hnψ
    simp [Normalized, hz] at hsum
  let ψS : S := ⟨ψ, hψ⟩
  have hψSne : ψS ≠ 0 := by
    intro hz
    exact hψne (congrArg Subtype.val hz)
  obtain ⟨lam, hlam⟩ := exists_smul_eq_of_finrank_eq_one hdim hψSne (⟨φ, hφ⟩ : S)
  have hrel : φ = lam • ψ := (congrArg Subtype.val hlam).symm
  exact ⟨lam, norm_eq_one_of_normalized_smul ψ lam hnψ (hrel ▸ hnφ), hrel⟩

/-- The code space after a legal Clifford run on a consistent tableau with independent
generators contains a normalized state. -/
theorem exists_normalized_run {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧ ψ ∈ codeSpace (run gates t) := by
  obtain ⟨ψ, hnψ, hψ⟩ := exists_normalized_of_independent t ht hind
  exact ⟨Uword gates *ᵥ ψ, normalized_applyGate (Uword_unitary gates hg) hnψ,
    (mem_run_iff gates hg t ψ).mpr hψ⟩

/-- Two normalized states in the code space after a legal Clifford run on a consistent full
independent tableau differ by a scalar of norm one. -/
theorem normalized_run_unique {n : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n n) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t))
    (ψ φ : QState (Reg n)) (hψ : ψ ∈ codeSpace (run gates t))
    (hφ : φ ∈ codeSpace (run gates t)) (hnψ : Normalized ψ) (hnφ : Normalized φ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ φ = lam • ψ := by
  have hdim : Module.finrank ℂ (codeSpace (run gates t)) = 1 := by
    simpa using! finrank_codeSpace_run gates hg t ht hind
  exact normalized_line_unique _ hdim ψ φ hψ hφ hnψ hnφ

end Qatlib.Concepts.PauliClifford.PauliAlgebra
