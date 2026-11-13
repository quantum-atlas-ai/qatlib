/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Isometric workspace embeddings

`workspaceEmbedding` enlarges only the auxiliary factor of a quantum register, while
`forwardWorkspaceOracle` acts on the original oracle factor. The embedding intertwines these
oracle actions and preserves trace and density operators.

The completed operator `workspaceGate` acts as the original gate on the embedded subspace and as
the identity on its orthogonal complement. These finite-dimensional isometric constructions use
the quantum operation framework of [Watrous2018].

## Main statements

* `workspaceEmbedding_intertwine`: workspace embeddings intertwine the enlarged oracle actions.
* `workspaceEmbedding_density`: embedding preserves density operators.
* `workspaceGate_unitary`: completing an embedded unitary yields a unitary ambient gate.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
namespace Qatlib.Concepts.Execution.WorkspaceCP
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Kronecker

/-- The oracle `U` tensored with the identity on a workspace of dimension `k`, reindexed as an
operator on `Fin (d * k)`. -/
noncomputable def forwardWorkspaceOracle {d : ℕ} (k : ℕ) (U : Operator d) :
    Operator (d * k) :=
  relabelGate finProdFinEquiv (TensorGate U (1 : Operator k))

/-- The coordinate inclusion of a workspace of dimension `k` into one of dimension `K`. -/
private noncomputable def workspaceAuxEmbedding {k K : ℕ} (h : k ≤ K) :
    Matrix (Fin K) (Fin k) ℂ := fun a b => if a = Fin.castLE h b then 1 else 0

/-- The isometric coordinate inclusion that preserves the oracle register and enlarges its
auxiliary workspace. -/
noncomputable def workspaceEmbedding {d k K : ℕ} (h : k ≤ K) :
    Matrix (Fin (d * K)) (Fin (d * k)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((1 : Operator d) ⊗ₖ workspaceAuxEmbedding h)

/-- Each workspace embedding entry is the product of an oracle-register identity entry and the
auxiliary inclusion indicator. -/
theorem workspaceEmbedding_apply {d k K : ℕ} (h : k ≤ K)
    (a : Fin (d * K)) (b : Fin (d * k)) :
    workspaceEmbedding (d := d) h a b =
      (1 : Operator d) (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 *
        (if (finProdFinEquiv.symm a).2 = Fin.castLE h (finProdFinEquiv.symm b).2
          then 1 else 0) := rfl

/-- The auxiliary coordinate inclusion has adjoint times itself equal to the identity. -/
private theorem workspaceAuxEmbedding_isometry {k K : ℕ} (h : k ≤ K) :
    (workspaceAuxEmbedding h)ᴴ * workspaceAuxEmbedding h = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, workspaceAuxEmbedding]
  rw [Finset.sum_eq_single (Fin.castLE h i)]
  · simp [Matrix.one_apply, (Fin.castLE_injective h).eq_iff]
  · intro a _ ha
    simp [ha]
  · simp

/-- The workspace coordinate embedding is an isometry. -/
theorem workspaceEmbedding_isometry {d k K : ℕ} (h : k ≤ K) :
    IsIsometry (workspaceEmbedding (d := d) h) := by
  unfold IsIsometry workspaceEmbedding
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul,
    workspaceAuxEmbedding_isometry, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- Embedding a workspace into itself gives the identity matrix. -/
theorem workspaceEmbedding_self (d k : ℕ) :
    workspaceEmbedding (d := d) (Nat.le_refl k) = 1 := by
  have ha : workspaceAuxEmbedding (Nat.le_refl k) = (1 : Operator k) := by
    ext a b
    simp [workspaceAuxEmbedding, Matrix.one_apply]
  simp [workspaceEmbedding, ha, Matrix.one_kronecker_one,
    Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- The workspace embedding intertwines the oracle tensored with the identity at the two
workspace widths. -/
theorem workspaceEmbedding_intertwine {d k K : ℕ} (h : k ≤ K) (U : Operator d) :
    forwardWorkspaceOracle K U * workspaceEmbedding (d := d) h =
      workspaceEmbedding (d := d) h * forwardWorkspaceOracle k U := by
  unfold forwardWorkspaceOracle workspaceEmbedding relabelGate
  simp only [Matrix.reindex_apply, TensorGate]
  rw [Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

/-- Tensoring a unitary oracle with a workspace identity yields a unitary operator. -/
theorem forwardWorkspaceOracle_unitary {d : ℕ} (k : ℕ) (U : Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    forwardWorkspaceOracle k U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ :=
  relabelGate_mem_unitary
    (tensorGate_unitary hU (Matrix.unitaryGroup _ _).one_mem) _

/-- Oracle conjugation commutes with embedding an input operator into the larger workspace. -/
theorem workspaceEmbedding_conjBranch {d k K : ℕ} (h : k ≤ K)
    (U : Operator d) (A : Operator (d * k)) :
    conjBranch (forwardWorkspaceOracle K U) (conjBranch (workspaceEmbedding (d := d) h) A) =
      conjBranch (workspaceEmbedding (d := d) h) (conjBranch (forwardWorkspaceOracle k U) A) := by
  change (conjBranch (forwardWorkspaceOracle K U) ∘ₗ
      conjBranch (workspaceEmbedding (d := d) h)) A =
    (conjBranch (workspaceEmbedding (d := d) h) ∘ₗ conjBranch (forwardWorkspaceOracle k U)) A
  rw [conjBranch_comp, conjBranch_comp, workspaceEmbedding_intertwine (d := d) h U]

/-- Conjugation by the workspace embedding preserves the trace of every input operator. -/
theorem workspaceEmbedding_trace {d k K : ℕ} (h : k ≤ K) (A : Operator (d * k)) :
    trace (conjBranch (workspaceEmbedding (d := d) h) A) = trace A := by
  have hi : (workspaceEmbedding (d := d) h)ᴴ * workspaceEmbedding (d := d) h = 1 :=
    workspaceEmbedding_isometry (d := d) h
  rw [conjBranch_apply, Matrix.trace_mul_cycle, hi, Matrix.one_mul]

/-- Embedding by conjugation preserves density operators. -/
theorem workspaceEmbedding_density {d k K : ℕ} (h : k ≤ K)
    (rho : Operator (d * k)) (hrho : IsDensityOperator rho) :
    IsDensityOperator (conjBranch (workspaceEmbedding (d := d) h) rho) := by
  exact ⟨(completelyPositive_conjBranch _).positive hrho.1,
    (workspaceEmbedding_trace h rho).trans hrho.2⟩

/-- The extension of `G` to the ambient workspace that acts as the identity on the orthogonal
complement of the embedded subspace. -/
noncomputable def workspaceGate {d k K : ℕ} (h : k ≤ K) (G : Operator (d * k)) :
    Operator (d * K) :=
  workspaceEmbedding (d := d) h * G * (workspaceEmbedding (d := d) h)ᴴ +
    (1 - rangeProjector (workspaceEmbedding (d := d) h))

/-- The completed ambient gate agrees with the original gate after workspace embedding. -/
theorem workspaceGate_intertwine {d k K : ℕ} (h : k ≤ K) (G : Operator (d * k)) :
    workspaceGate (d := d) h G * workspaceEmbedding (d := d) h = workspaceEmbedding (d := d) h * G := by
  have hi : (workspaceEmbedding (d := d) h)ᴴ * workspaceEmbedding (d := d) h = 1 :=
    workspaceEmbedding_isometry (d := d) h
  simp [workspaceGate, rangeProjector, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc, hi]

/-- The completed ambient gate fixes the orthogonal complement of the embedded workspace. -/
theorem workspaceGate_complement {d k K : ℕ} (h : k ≤ K) (G : Operator (d * k)) :
    workspaceGate (d := d) h G * (1 - rangeProjector (workspaceEmbedding (d := d) h)) =
      1 - rangeProjector (workspaceEmbedding (d := d) h) := by
  let E := workspaceEmbedding (d := d) h
  have hi : Eᴴ * E = 1 := workspaceEmbedding_isometry (d := d) h
  have hp : rangeProjector E * rangeProjector E = rangeProjector E :=
    (rangeProjector_isOrthogonalProjector (workspaceEmbedding_isometry (d := d) h)).1
  have hz : Eᴴ * (1 - rangeProjector E) = 0 := by
    simp [rangeProjector, Matrix.mul_sub, ← Matrix.mul_assoc, hi]
  change (E * G * Eᴴ + (1 - rangeProjector E)) * (1 - rangeProjector E) = _
  rw [Matrix.add_mul, Matrix.mul_assoc, hz, Matrix.mul_zero, zero_add]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    hp, sub_self, sub_zero]
  rfl

/-- Completing a unitary workspace gate by the identity on the complement yields a unitary
ambient gate. -/
theorem workspaceGate_unitary {d k K : ℕ} (h : k ≤ K) (G : Operator (d * k))
    (hG : G ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ) :
    workspaceGate (d := d) h G ∈ Matrix.unitaryGroup (Fin (d * K)) ℂ := by
  let E := workspaceEmbedding (d := d) h
  have hi : Eᴴ * E = 1 := workspaceEmbedding_isometry (d := d) h
  have hu : Gᴴ * G = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hG
  let P := E * Eᴴ
  let A := E * G * Eᴴ
  have hpE : P * E = E := by simp [P, Matrix.mul_assoc, hi]
  have hPP : P * P = P := by
    calc
      P * P = (P * E) * Eᴴ := by simp only [P, Matrix.mul_assoc]
      _ = P := by rw [hpE]
  have hpA : P * A = A := by simp only [A, ← Matrix.mul_assoc, hpE]
  have hstar : Aᴴ = E * Gᴴ * Eᴴ := by simp [A, Matrix.mul_assoc]
  have hAA : Aᴴ * A = P := by
    rw [hstar]
    simp only [A, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ E, hi, Matrix.one_mul,
      ← Matrix.mul_assoc Gᴴ G, hu, Matrix.one_mul]
  have hpstar : Pᴴ = P := by simp [P]
  have hAQ : Aᴴ * (1 - P) = 0 := by
    have hh := congrArg Matrix.conjTranspose hpA
    simp only [Matrix.conjTranspose_mul, hpstar] at hh
    rw [Matrix.mul_sub, Matrix.mul_one, hh, sub_self]
  have hQA : (1 - P) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hpA, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (A + (1 - P))ᴴ * (A + (1 - P)) = 1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hpstar]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAA, hAQ, hQA, hQQ]
  abel

/-- Conjugation by a completed workspace gate commutes with embedding the original gate's
conjugation output. -/
theorem workspaceGate_conjBranch {d k K : ℕ} (h : k ≤ K) (G A : Operator (d * k)) :
    conjBranch (workspaceGate (d := d) h G) (conjBranch (workspaceEmbedding (d := d) h) A) =
      conjBranch (workspaceEmbedding (d := d) h) (conjBranch G A) := by
  change (conjBranch (workspaceGate (d := d) h G) ∘ₗ conjBranch (workspaceEmbedding (d := d) h)) A =
    (conjBranch (workspaceEmbedding (d := d) h) ∘ₗ conjBranch G) A
  rw [conjBranch_comp, conjBranch_comp, workspaceGate_intertwine (d := d) h G]

end Qatlib.Concepts.Execution.WorkspaceCP
