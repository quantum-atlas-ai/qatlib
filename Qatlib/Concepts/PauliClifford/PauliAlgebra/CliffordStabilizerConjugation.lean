/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
import Mathlib.Tactic.NoncommRing

/-!
# Clifford covariance of stabilizer projectors

This module defines matrix `conjugate` and proves its algebraic and trace properties under the
stated unitarity hypotheses. It then transports generator projector products and Pauli branch
projectors through legal Clifford circuits, using the operator description of stabilizers in
[DehaeneDeMoor2003].

## Main statements

* `projector_covariance`: Generator projector products transform by circuit conjugation.
* `tableau_projector_covariance`: Tableau projector products obey the same covariance law.
* `branch_projector_covariance`: Each Pauli branch projector transforms by circuit conjugation.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Matrix

/-- Conjugation of a matrix A by U, given by U A Uᴴ. -/
def conjugate {n : ℕ} (U A : Matrix (Reg n) (Reg n) ℂ) := U*A*Uᴴ

/-- Conjugation by a unitary matrix fixes the identity. -/
theorem conjugate_one {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) : conjugate U 1 = 1 := by
  simpa only [conjugate,Matrix.mul_one] using! (Matrix.mem_unitaryGroup_iff.mp hU)

/-- Matrix conjugation distributes over addition. -/
theorem conjugate_add {n : ℕ} (U A B : Matrix (Reg n) (Reg n) ℂ) :
    conjugate U (A+B) = conjugate U A+conjugate U B := by
  simp only [conjugate,Matrix.mul_add,Matrix.add_mul]

/-- Matrix conjugation commutes with complex scalar multiplication. -/
theorem conjugate_smul {n : ℕ} (U A : Matrix (Reg n) (Reg n) ℂ) (c : ℂ) :
    conjugate U (c • A) = c • conjugate U A := by
  simp only [conjugate,Matrix.mul_smul,Matrix.smul_mul]

/-- Conjugation by a unitary matrix preserves matrix multiplication. -/
theorem conjugate_mul {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) (A B : Matrix (Reg n) (Reg n) ℂ) :
    conjugate U (A*B) = conjugate U A*conjugate U B := by
  have hinv : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hU
  dsimp [conjugate]
  calc
    U*(A*B)*Uᴴ = U*A*(Uᴴ*U)*B*Uᴴ := by rw [hinv]; simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = _ := by noncomm_ring

/-- Conjugation by a unitary matrix preserves the trace. -/
theorem conjugate_trace {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) (A : Matrix (Reg n) (Reg n) ℂ) :
    Matrix.trace (conjugate U A) = Matrix.trace A := by
  have hinv : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hU
  unfold conjugate
  rw [Matrix.trace_mul_cycle,hinv,Matrix.one_mul]

/-- The projector product for Pauli generators transformed by a legal Clifford circuit is the
conjugate of the original projector product. -/
theorem projector_covariance {n : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (rows : List (PauliElem n)) :
    projectorAux (rows.map (actionWord gates)) = conjugate (Uword gates) (projectorAux rows) := by
  have hU := Uword_unitary gates hg
  induction rows with
  | nil => simpa only [List.map_nil,projectorAux] using! (conjugate_one (Uword gates) hU).symm
  | cons p rows ih =>
      have hp : op (actionWord gates p) = conjugate (Uword gates) (op p) :=
          (Uword_conj gates p hg).symm
      simp only [List.map_cons,projectorAux]
      rw [ih,hp,← conjugate_mul (Uword gates) hU,← conjugate_add,← conjugate_smul]

/-- The generators of a tableau after a legal Clifford run are the original generators mapped by
the circuit's Pauli action. -/
theorem run_generators {n m : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n m) :
    tableauGenerators (run gates t) = (tableauGenerators t).map (actionWord gates) := by
  simp only [tableauGenerators,List.map_map]
  apply List.map_congr_left
  intro a _
  exact run_decode gates hg t a

/-- The projector product of a tableau transforms by unitary conjugation under a legal Clifford
run. -/
theorem tableau_projector_covariance {n m : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n m) :
    projectorAux (tableauGenerators (run gates t)) =
      conjugate (Uword gates) (projectorAux (tableauGenerators t)) := by
  rw [run_generators gates hg,projector_covariance gates hg]

/-- Pauli branch projectors transform by conjugation under a legal Clifford circuit. -/
theorem branch_projector_covariance {n : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (p : PauliElem n) (b : Bool) :
    pauliBranchProjector (actionWord gates p) b =
      conjugate (Uword gates) (pauliBranchProjector p b) := by
  have hp : op (actionWord gates p) = conjugate (Uword gates) (op p) := (Uword_conj gates p hg).symm
  have h1 := conjugate_one (Uword gates) (Uword_unitary gates hg)
  cases b <;> simp only [pauliBranchProjector,conjugate_smul,conjugate_add,hp]
  · dsimp [conjugate] at h1 ⊢
    rw [Matrix.mul_sub,Matrix.sub_mul,h1]
  · rw [h1]

end Qatlib.Concepts.PauliClifford.PauliAlgebra
