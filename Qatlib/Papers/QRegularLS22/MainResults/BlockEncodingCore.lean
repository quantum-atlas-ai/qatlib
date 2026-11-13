/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Module.Normalize

set_option backward.isDefEq.respectTransparency false

/-!
# QRegularLS22 — paper-level block-encoding interface

Fixed paper version: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19),
"Quantum Regularized Least Squares". Page numbers below refer to the
accepted-Quantum pagination.

This module fixes the paper's notion of an **`(α, ε)`-approximate block encoding**
(GSLW Definition 24 convention, as used throughout the paper):

* the workspace is `K × I`, where `K` is the ancilla register (the paper writes
  `2 ^ a` for its dimension, `a` ancilla qubits) and `I` is the data register;
* `k₀ : K` is the distinguished ancilla state `|0…0⟩`;
* the encoded operator is the `(k₀, k₀)`-corner `BlockCorner U k₀` of the unitary
  `U`, and the approximation is measured in the spectral (`L2` operator) norm:
  `‖A - α • BlockCorner U k₀‖ ≤ ε`.

This is the library's matrix form of GSLW's block encoding; for `ε = 0` it
coincides with `Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsBlockEncoding`
(see `blockEncodes_iff_isBlockEncoding`). Scope note: this module formalizes the
block-encoding interface; query counts and efficient synthesis are outside its
scope. The paper's `O(·)` cost expressions are recorded in the docstrings of the
individual results without an algorithmic cost model.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

/-! ## The paper's approximate block encoding -/

/-- **Paper-level `(α, ε)`-approximate block encoding.**  `U` is a unitary on the
`K × I` workspace and its `k₀`-corner is an `ε`-spectral approximation (after the
scale `α`) of `A`.  This is the `(α, a, ε)`-block-encoding of arXiv:2206.13143
with `|K| = 2 ^ a`; the ancilla depth `a` is read off from `K` in the statements
that mention it. -/
def BlockEncodes {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (U : Matrix (K × I) (K × I) ℂ) (k₀ : K) (A : Matrix I I ℂ) (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (K × I) ℂ ∧ 0 < α ∧ 0 ≤ ε ∧
    ‖A - ((α : ℂ) • BlockCorner U k₀)‖ ≤ ε

/-- A two-level (nested) corner encoding, used for the LCU workspace where the
outer index `J` is the SELECT ancilla and the inner index `K` is the per-branch
block-encoding ancilla. -/
def BlockEncodes₂ {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (U : Matrix (J × (K × I)) (J × (K × I)) ℂ) (j₀ : J) (k₀ : K)
    (A : Matrix I I ℂ) (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × (K × I)) ℂ ∧ 0 < α ∧ 0 ≤ ε ∧
    ‖A - ((α : ℂ) • BlockCorner (BlockCorner U j₀) k₀)‖ ≤ ε

/-- The corner is additive over a finite sum. -/
theorem blockCorner_finset_sum {J I : Type*} [Fintype J] [Fintype I]
    {ι : Type*} (s : Finset ι) (M : ι → Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    BlockCorner (s.sum M) j₀ = s.sum (fun i => BlockCorner (M i) j₀) := by
  ext a b
  simp [BlockCorner, Matrix.sum_apply]

/-- The corner commutes with real scalar multiplication. -/
theorem blockCorner_smul {J I : Type*} [Fintype J] [Fintype I]
    (c : ℝ) (M : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    BlockCorner (c • M) j₀ = c • BlockCorner M j₀ := by
  ext a b
  simp [BlockCorner, Matrix.smul_apply]

/-- An exact `(α, 0)` encoding is exactly the library's `IsBlockEncoding`. -/
theorem blockEncodes_iff_isBlockEncoding {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (U : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (A : Matrix I I ℂ) (α : ℝ) :
    BlockEncodes U j₀ A α 0 ↔
      Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsBlockEncoding U j₀ A α := by
  constructor
  · rintro ⟨hU, hα, _, hzero⟩
    refine ⟨hU, hα, ?_⟩
    have hnorm : A - ((α : ℂ) • BlockCorner U j₀) = 0 :=
      norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
    have hA : A = ((α : ℂ) • BlockCorner U j₀) := sub_eq_zero.mp hnorm
    have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    rw [hA, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hαc, one_smul]
  · rintro ⟨hU, hα, hcorner⟩
    refine ⟨hU, hα, le_refl 0, ?_⟩
    have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    rw [hcorner, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hαc, one_smul, sub_self,
      norm_zero]

/-- Relaxing the error preserves an encoding. -/
theorem BlockEncodes.mono {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    {U : Matrix (K × I) (K × I) ℂ} {k₀ : K} {A : Matrix I I ℂ} {α ε δ : ℝ}
    (h : BlockEncodes U k₀ A α ε) (hεδ : ε ≤ δ) : BlockEncodes U k₀ A α δ :=
  ⟨h.1, h.2.1, h.2.2.1.trans hεδ, h.2.2.2.trans hεδ⟩

/-! ## Bridge to the rectangular `BlockEncoding`

`BlockEncodes` is the coordinate-corner form of the frame encoding
`Qatlib.Concepts.BlockEncoding.BlockEncoding`. The bridge is used
throughout: paper statements are proved against the library's postselection and
robust-QSVT machinery, whose hypotheses are stated for
`BlockEncoding A U L R α ε` with explicit frames `L`, `R`. -/

open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-- Real and complex scalar multiplication agree on complex matrices. -/
theorem real_smul_eq_complex_smul {m n : Type*} (a : ℝ) (X : Matrix m n ℂ) :
    a • X = (a : ℂ) • X := by
  ext i j
  simp [Complex.real_smul]

/-- A corner `(α, ε)`-encoding is exactly a frame encoding between the
`k₀`-coordinate fibers, with the same scale and error. -/
theorem blockEncodes_iff_blockEncoding {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (U : Matrix (K × I) (K × I) ℂ) (k₀ : K)
    (A : Matrix I I ℂ) (α ε : ℝ) :
    BlockEncodes U k₀ A α ε ↔
      Qatlib.Concepts.BlockEncoding.BlockEncoding A U
        (encodingFiber k₀) (encodingFiber k₀) α ε := by
  constructor
  · rintro ⟨hU, hα, hε, herr⟩
    exact ⟨hU, encodingFiber_isIsometry k₀, encodingFiber_isIsometry k₀, hα, hε, by
      simpa only [compress_encodingFiber_blockCorner, real_smul_eq_complex_smul] using herr⟩
  · rintro ⟨hU, -, -, hα, hε, herr⟩
    refine ⟨hU, hα, hε, ?_⟩
    simpa only [compress_encodingFiber_blockCorner, real_smul_eq_complex_smul] using herr

/-- The corner of a unitary is contractive: `‖BlockCorner U k₀‖ ≤ 1`.  This is the
quantitative input of Lemma 21 (tensor products) and of all success-probability
bounds: the compressed block of a unitary never amplifies. -/
theorem blockCorner_norm_le_one {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] {U : Matrix (K × I) (K × I) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (K × I) ℂ) (k₀ : K) :
    ‖BlockCorner U k₀‖ ≤ 1 := by
  rw [← compress_encodingFiber_blockCorner k₀ U]
  exact (compress_norm_le (encodingFiber_isIsometry k₀) (encodingFiber_isIsometry k₀) U).trans
    (unitary_norm_le_one hU)

/-! ## Register conventions and the paper's `(α, a, ε)`-block encoding

The paper writes a block encoding as `(α, a, ε)`-block-encoding, where `a` is the
number of ancilla qubits, i.e. the ancilla register is `Fin (2 ^ a)`.  `IsEnc`
fixes the all-zero ancilla corner and reads the workspace as `Enc a I`. -/

universe u

/-- Paper register layout: `a` ancilla qubits (`Fin (2 ^ a)`) together with the
data register `I`. -/
abbrev Enc (a : ℕ) (I : Type u) : Type u := Fin (2 ^ a) × I

/-- The paper's `(α, a, ε)`-block-encoding: a unitary on `Enc a I` whose
all-zero-ancilla corner `α`-approximates `A` in spectral norm. -/
def IsEnc {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ}
    (U : Matrix (Enc a I) (Enc a I) ℂ) (A : Matrix I I ℂ) (α ε : ℝ) : Prop :=
  BlockEncodes U (0 : Fin (2 ^ a)) A α ε

/-- `IsEnc` is the frame encoding of the zero fiber. -/
theorem isEnc_iff_blockEncoding {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ}
    (U : Matrix (Enc a I) (Enc a I) ℂ) (A : Matrix I I ℂ) (α ε : ℝ) :
    IsEnc U A α ε ↔
      Qatlib.Concepts.BlockEncoding.BlockEncoding A U
        (encodingFiber (0 : Fin (2 ^ a))) (encodingFiber (0 : Fin (2 ^ a))) α ε :=
  blockEncodes_iff_blockEncoding U 0 A α ε

/-! ## Polynomial evaluation at a matrix

QSVT (Theorem 8, and every consumer in the paper) applies a polynomial `P` of
degree `d` to a block-encoded `A / α`.  `evalPoly P A` is the matrix `P(A)`
under the usual polynomial functional calculus for square matrices. -/

/-- Evaluate a complex polynomial at a square complex matrix,
`evalPoly P A = ∑ k ≤ deg P, P.coeff k • A ^ k`. -/
noncomputable def evalPoly {I : Type*} [Fintype I] [DecidableEq I]
    (P : Polynomial ℂ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • A ^ k

/-- `evalPoly` of the identity polynomial is the identity matrix. -/
theorem evalPoly_X {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    evalPoly Polynomial.X A = A := by
  simp only [evalPoly, Polynomial.natDegree_X]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Polynomial.coeff_X]

/-- `evalPoly` of a constant polynomial is the constant scalar matrix. -/
theorem evalPoly_C {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ)
    (A : Matrix I I ℂ) : evalPoly (Polynomial.C c) A = c • 1 := by
  simp [evalPoly]

/-! ## State closeness and the paper's least-squares targets

All quantum outputs of the paper are states.  `StateClose ψ v δ` says that the
prepared state `ψ` is normalized and `δ`-close, in the Euclidean (`ℓ²`) norm of
`stateVector`, to the normalized target vector `v`.  `QState I = I → ℂ` carries
the Pi (sup) norm, so every quantitative statement below is phrased through the
Euclidean representative `stateVector`, exactly as in the library's postselection
API.  The target vectors are the classical solutions of Eq. (31) and its
weighted/generalized variants, with the transpose convention `Aᵀ A` of the
paper (the source is real; `ℂ` is used for the state space only). -/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath

/-- `ψ` is a normalized state within Euclidean distance `δ` of the normalized
target vector `v`.  This is the paper's `‖|ψ⟩ - |x⟩‖ ≤ δ` output convention. -/
def StateClose {I : Type*} [Fintype I] (ψ v : QState I) (δ : ℝ) : Prop :=
  Normalized ψ ∧ ‖stateVector ψ - NormedSpace.normalize (stateVector v)‖ ≤ δ

/-- Regularized least-squares solution of Eq. (31),
`x = (AᵀA + λ LᵀL)⁻¹ Aᵀ b`. -/
noncomputable def regLSVec {N d : Type*} [Fintype N] [DecidableEq N]
    [Fintype d] [DecidableEq d] (A L : Matrix N d ℂ) (lam : ℝ) (b : QState N) : QState d :=
  (Aᵀ * A + (lam : ℂ) • (Lᵀ * L))⁻¹ *ᵥ (Aᵀ *ᵥ b)

/-- Weighted regularized least-squares solution of Eq. (33),
`x = (AᵀWA + λ LᵀL)⁻¹ AᵀW b`. -/
noncomputable def weightedLSVec {N d : Type*} [Fintype N] [DecidableEq N]
    [Fintype d] [DecidableEq d] (A L : Matrix N d ℂ) (W : Matrix N N ℂ) (lam : ℝ)
    (b : QState N) : QState d :=
  (Aᵀ * W * A + (lam : ℂ) • (Lᵀ * L))⁻¹ *ᵥ ((Aᵀ * W) *ᵥ b)

/-- Generalized regularized least-squares solution of Eq. (35),
`x = (AᵀΩ⁻¹A + λ LᵀL)⁻¹ AᵀΩ⁻¹ b`. -/
noncomputable def generalizedLSVec {N d : Type*} [Fintype N] [DecidableEq N]
    [Fintype d] [DecidableEq d] (A L : Matrix N d ℂ) (Ω : Matrix N N ℂ) (lam : ℝ)
    (b : QState N) : QState d :=
  (Aᵀ * Ω⁻¹ * A + (lam : ℂ) • (Lᵀ * L))⁻¹ *ᵥ ((Aᵀ * Ω⁻¹) *ᵥ b)

/-- The augmented matrix `A_L = [[A, 0], [√λ L, 0]]` of Eq. (32).  The singular
values of `A_L` are those of `A` together with those of `√λ L`, so a `(α, a, ε)`
encoding of `A_L` gives a QSVT input whose non-zero singular values include the
regularization directions. -/
noncomputable def augmentedMatrix {N d : Type*} (A L : Matrix N d ℂ) (lam : ℝ) :
    Matrix (Sum N N) (Sum d d) ℂ :=
  Matrix.fromBlocks A 0 ((Real.sqrt lam : ℝ) • L) 0

end Qatlib.Papers.QRegularLS22.MainResults
