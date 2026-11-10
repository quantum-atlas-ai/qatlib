/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerConjugation
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDensity
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix
open scoped Classical ComplexOrder

theorem cnotPhaseCorrection_even (a b : Pauli1) :
    cnotPhaseCorrection a b = 0 ∨ cnotPhaseCorrection a b = 2 := by
  unfold cnotPhaseCorrection
  split_ifs <;> simp

theorem verifiedAction_hermitian_iff {n : ℕ} (g : CliffordGate n) (p : PauliElem n) :
    IsHermitianPauli (verifiedCliffordAction g p) ↔ IsHermitianPauli p := by
  cases g with
  | H i =>
      change IsHermitianPauli (cliffordAction (.H i) p) ↔ IsHermitianPauli p
      exact cliffordAction_hermitian_iff (.H i) p
  | S i =>
      change IsHermitianPauli (cliffordAction (.S i) p) ↔ IsHermitianPauli p
      exact cliffordAction_hermitian_iff (.S i) p
  | CNOT i j =>
      change (p.phase + cnotPhaseCorrection (p.word i) (p.word j) = 0 ∨
        p.phase + cnotPhaseCorrection (p.word i) (p.word j) = 2) ↔
          (p.phase = 0 ∨ p.phase = 2)
      exact even_phase_add (cnotPhaseCorrection_even (p.word i) (p.word j))

theorem actionWord_hermitian_iff {n : ℕ} (gates : List (CliffordGate n)) (p : PauliElem n) :
    IsHermitianPauli (actionWord gates p) ↔ IsHermitianPauli p := by
  induction gates generalizing p with
  | nil => rfl
  | cons g gates ih =>
      change IsHermitianPauli (actionWord gates (verifiedCliffordAction g p)) ↔
        IsHermitianPauli p
      exact (ih _).trans (verifiedAction_hermitian_iff g p)

theorem consistent_run {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) (ht : ConsistentTableau t) :
    ConsistentTableau (run gates t) := by
  constructor
  · intro a
    rw [run_decode gates hg t a]
    exact (actionWord_hermitian_iff gates (t a).decode).mpr (ht.1 a)
  · intro a b
    have hU := Uword_unitary gates hg
    have ha : op (run gates t a).decode = conjugate (Uword gates) (op (t a).decode) :=
      run_op gates hg t a
    have hb : op (run gates t b).decode = conjugate (Uword gates) (op (t b).decode) :=
      run_op gates hg t b
    rw [ha, hb, ← conjugate_mul (Uword gates) hU, ht.2 a b,
      conjugate_mul (Uword gates) hU]

theorem codeDensityMatrix_run_covariance {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) :
    codeDensityMatrix (run gates t) = conjugate (Uword gates) (codeDensityMatrix t) := by
  rw [codeDensityMatrix, tableau_projector_covariance gates hg]
  exact (conjugate_smul (Uword gates) (projectorAux (tableauGenerators t))
    (((2 : ℂ) ^ (n - k))⁻¹)).symm

theorem codeDensity_run_isDensityOperator {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    IsDensityOperator (codeDensity (run gates t)) := by
  apply relabel_density (bitVecEquiv n) (codeDensityMatrix (run gates t))
  refine ⟨codeDensityMatrix_posSemidef _ (consistent_run gates hg t ht), ?_⟩
  rw [codeDensityMatrix_run_covariance gates hg,
    conjugate_trace _ (Uword_unitary gates hg), codeDensityMatrix_trace t ht hind]

theorem finrank_codeSpace_run {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ (codeSpace (run gates t)) = 2 ^ (n - k) := by
  rw [finrank_run gates hg t]
  exact finrank_codeSpace_of_independent t ht hind

theorem codeSpace_eq_bot_of_generated_minusI {n k : ℕ} (t : Tableau n k)
    (hminus : minusI n ∈ generatedSubgroup (tableauGenerators t)) : codeSpace t = ⊥ := by
  obtain ⟨mask, hmask, hprod⟩ := hminus
  apply bot_unique
  intro ψ hψ
  change ψ = 0
  have hfix := op_maskProduct_fixes_codeSpace t ψ hψ mask hmask
  rw [hprod] at hfix
  have hminusop : op (minusI n) = -1 := minusI_op n
  rw [hminusop] at hfix
  funext b
  have hb := congrFun hfix b
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply] at hb
  change ψ b = 0
  linear_combination (-(1 / 2 : ℂ)) * hb

theorem minusI_not_mem_run {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    minusI n ∉ generatedSubgroup (tableauGenerators (run gates t)) := by
  intro hminus
  have hz := codeSpace_eq_bot_of_generated_minusI (run gates t) hminus
  have hfr := finrank_codeSpace_run gates hg t ht hind
  rw [hz, finrank_bot] at hfr
  exact (Nat.ne_of_gt (by positivity : 0 < (2 : ℕ) ^ (n - k))) hfr.symm

end Qatlib.Concepts.PauliClifford.PauliAlgebra
