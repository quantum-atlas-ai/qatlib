/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source definitions of the QSVT paper

This module formalizes the objects introduced in the definitions of
Gilyén–Su–Low–Wiebe, *Quantum singular value transformation and beyond*,
arXiv:1806.01838v1:

* Definition 1 (printed p. 6): the right and left **singular value projectors**
  `V Σ_S V†` and `W Σ_S W†` attached to a singular value decomposition
  `A = W Σ V†`;
* Definition 2 (printed p. 7): the **`CΠNOT` gate** `X ⊗ Π + I ⊗ (I − Π)`,
  together with the fact that it is unitary whenever `Π` is an orthogonal
  projector;
* Definition 24 (printed p. 26): the **singular value threshold projectors**
  `Π_{≥δ}`, `Π_{>δ}`, … obtained from Definition 1 by taking the index set
  `S` to be the corresponding real interval;
* Definition 44 (printed p. 41): the **trivial block-encoding**, i.e. a unitary
  is a `(1,0,0)`-block-encoding of itself.

The task of this file is definitional: it records the objects and the small
facts that they have the stated shape (self-adjoint idempotents, unitarity,
exact self-encoding).  It does not prove the singular value decomposition
existence theorem or the invariant-subspace decomposition of Lemma 14.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.QsVtMain.SourceDefinitions

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding
open scoped Kronecker Matrix.Norms.L2Operator

/-! ## Definition 1 — singular value projectors -/

/-- The singular-value indicator matrix `Σ_S`: it keeps a `1` on the diagonal
entries whose singular value lies in `S` and puts `0` elsewhere.  This is the
matrix `Σ_S` of Definition 1. -/
def svIndicator {K : Type*} [DecidableEq K] (σ : K → ℝ) (S : Set ℝ) :
    Matrix K K ℂ :=
  Matrix.diagonal fun k =>
    @ite ℂ (σ k ∈ S) (Classical.propDecidable _) (1 : ℂ) 0

/-- The right singular value projector `V Σ_S V†` of the singular value
decomposition `A = W Σ V†` (Definition 1). -/
def rightSingularValueProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (S : Set ℝ) : Matrix I I ℂ :=
  V * svIndicator σ S * Vᴴ

/-- The left singular value projector `W Σ_S W†` of the singular value
decomposition `A = W Σ V†` (Definition 1). -/
def leftSingularValueProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (S : Set ℝ) : Matrix O O ℂ :=
  W * svIndicator σ S * Wᴴ

/-- The indicator matrix of a real value set is self-adjoint. -/
theorem svIndicator_conjTranspose {K : Type*} [Fintype K] [DecidableEq K]
    (σ : K → ℝ) (S : Set ℝ) : (svIndicator σ S)ᴴ = svIndicator σ S := by
  unfold svIndicator
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  by_cases h : σ k ∈ S <;> simp [h]

/-- The indicator matrix of a real value set is idempotent. -/
theorem svIndicator_mul_self {K : Type*} [Fintype K] [DecidableEq K]
    (σ : K → ℝ) (S : Set ℝ) : svIndicator σ S * svIndicator σ S = svIndicator σ S := by
  unfold svIndicator
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : σ k ∈ S <;> simp [h]

/-- **Definition 1, right side.**  For an isometric singular-vector frame `V`
the right singular value projector `V Σ_S V†` is an orthogonal projector. -/
theorem rightSingularValueProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (S : Set ℝ) :
    IsOrthogonalProjector (rightSingularValueProjector V σ S) := by
  have hV' : Vᴴ * V = 1 := hV
  have hD : svIndicator σ S * svIndicator σ S = svIndicator σ S :=
    svIndicator_mul_self σ S
  have hDstar : (svIndicator σ S)ᴴ = svIndicator σ S :=
    svIndicator_conjTranspose σ S
  refine ⟨?_, ?_⟩
  · show rightSingularValueProjector V σ S * rightSingularValueProjector V σ S =
      rightSingularValueProjector V σ S
    unfold rightSingularValueProjector
    have reassoc : (V * svIndicator σ S * Vᴴ) * (V * svIndicator σ S * Vᴴ)
        = V * svIndicator σ S * (Vᴴ * V) * svIndicator σ S * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [reassoc, hV', Matrix.mul_one]
    rw [Matrix.mul_assoc V (svIndicator σ S) (svIndicator σ S), hD]
  · show star (rightSingularValueProjector V σ S) = rightSingularValueProjector V σ S
    rw [Matrix.star_eq_conjTranspose]
    unfold rightSingularValueProjector
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDstar]
    rw [Matrix.mul_assoc]

/-- **Definition 1, left side.**  For an isometric singular-vector frame `W`
the left singular value projector `W Σ_S W†` is an orthogonal projector. -/
theorem leftSingularValueProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (S : Set ℝ) :
    IsOrthogonalProjector (leftSingularValueProjector W σ S) :=
  rightSingularValueProjector_isOrthogonalProjector W hW σ S

/-- The indicator matrix of the empty value set is zero. -/
theorem svIndicator_empty {K : Type*} [Fintype K] [DecidableEq K] (σ : K → ℝ) :
    svIndicator σ ∅ = 0 := by
  ext i j
  unfold svIndicator
  rw [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- The right singular value projector attached to the empty set is zero: no
singular vector is retained. -/
theorem rightSingularValueProjector_empty {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (V : Matrix I K ℂ) (σ : K → ℝ) :
    rightSingularValueProjector V σ ∅ = 0 := by
  unfold rightSingularValueProjector
  rw [svIndicator_empty σ]
  simp

/-! ## Definition 24 — singular value threshold projectors -/

/-- The right singular value threshold projector `Π_{≥δ} = Π V Σ_{[δ,∞)} V†`
(Definition 24). -/
def rightThresholdProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix I I ℂ :=
  rightSingularValueProjector V σ (Set.Ici δ)

/-- The right singular value strict threshold projector `Π_{>δ}`. -/
def rightStrictThresholdProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix I I ℂ :=
  rightSingularValueProjector V σ (Set.Ioi δ)

/-- **Definition 24.**  The right singular value threshold projector `Π_{≥δ}`
is an orthogonal projector. -/
theorem rightThresholdProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (rightThresholdProjector V σ δ) :=
  rightSingularValueProjector_isOrthogonalProjector V hV σ (Set.Ici δ)

/-- **Definition 24.**  The strict right threshold projector `Π_{>δ}` is an
orthogonal projector. -/
theorem rightStrictThresholdProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (rightStrictThresholdProjector V σ δ) :=
  rightSingularValueProjector_isOrthogonalProjector V hV σ (Set.Ioi δ)

/-- The right singular value threshold projector `Π_{≤δ}` (Definition 24). -/
def rightLeThresholdProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix I I ℂ :=
  rightSingularValueProjector V σ (Set.Iic δ)

/-- The right singular value strict threshold projector `Π_{<δ}`. -/
def rightLtThresholdProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix I I ℂ :=
  rightSingularValueProjector V σ (Set.Iio δ)

/-- The right singular value threshold projector `Π_{=δ}` onto one value. -/
def rightEqThresholdProjector {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix I I ℂ :=
  rightSingularValueProjector V σ ({δ} : Set ℝ)

/-- The left singular value threshold projector `Π̃_{≥δ}` (Definition 24). -/
def leftThresholdProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix O O ℂ :=
  leftSingularValueProjector W σ (Set.Ici δ)

/-- The left singular value strict threshold projector `Π̃_{>δ}`. -/
def leftStrictThresholdProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix O O ℂ :=
  leftSingularValueProjector W σ (Set.Ioi δ)

/-- The left singular value threshold projector `Π̃_{≤δ}`. -/
def leftLeThresholdProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix O O ℂ :=
  leftSingularValueProjector W σ (Set.Iic δ)

/-- The left singular value strict threshold projector `Π̃_{<δ}`. -/
def leftLtThresholdProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix O O ℂ :=
  leftSingularValueProjector W σ (Set.Iio δ)

/-- The left singular value threshold projector `Π̃_{=δ}`. -/
def leftEqThresholdProjector {O K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (σ : K → ℝ) (δ : ℝ) : Matrix O O ℂ :=
  leftSingularValueProjector W σ ({δ} : Set ℝ)

/-- **Definition 24.**  The right projector `Π_{≤δ}` is an orthogonal projector. -/
theorem rightLeThresholdProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (rightLeThresholdProjector V σ δ) :=
  rightSingularValueProjector_isOrthogonalProjector V hV σ (Set.Iic δ)

/-- **Definition 24.**  The right projector `Π_{<δ}` is an orthogonal projector. -/
theorem rightLtThresholdProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (rightLtThresholdProjector V σ δ) :=
  rightSingularValueProjector_isOrthogonalProjector V hV σ (Set.Iio δ)

/-- **Definition 24.**  The right projector `Π_{=δ}` is an orthogonal projector. -/
theorem rightEqThresholdProjector_isOrthogonalProjector {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (hV : IsIsometry V) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (rightEqThresholdProjector V σ δ) :=
  rightSingularValueProjector_isOrthogonalProjector V hV σ ({δ} : Set ℝ)

/-- **Definition 24.**  The left projector `Π̃_{≥δ}` is an orthogonal projector. -/
theorem leftThresholdProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (leftThresholdProjector W σ δ) :=
  leftSingularValueProjector_isOrthogonalProjector W hW σ (Set.Ici δ)

/-- **Definition 24.**  The left projector `Π̃_{>δ}` is an orthogonal projector. -/
theorem leftStrictThresholdProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (leftStrictThresholdProjector W σ δ) :=
  leftSingularValueProjector_isOrthogonalProjector W hW σ (Set.Ioi δ)

/-- **Definition 24.**  The left projector `Π̃_{≤δ}` is an orthogonal projector. -/
theorem leftLeThresholdProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (leftLeThresholdProjector W σ δ) :=
  leftSingularValueProjector_isOrthogonalProjector W hW σ (Set.Iic δ)

/-- **Definition 24.**  The left projector `Π̃_{<δ}` is an orthogonal projector. -/
theorem leftLtThresholdProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (leftLtThresholdProjector W σ δ) :=
  leftSingularValueProjector_isOrthogonalProjector W hW σ (Set.Iio δ)

/-- **Definition 24.**  The left projector `Π̃_{=δ}` is an orthogonal projector. -/
theorem leftEqThresholdProjector_isOrthogonalProjector {O K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
    (W : Matrix O K ℂ) (hW : IsIsometry W) (σ : K → ℝ) (δ : ℝ) :
    IsOrthogonalProjector (leftEqThresholdProjector W σ δ) :=
  leftSingularValueProjector_isOrthogonalProjector W hW σ ({δ} : Set ℝ)

/-- The threshold projectors are the indicator projectors of the corresponding
interval of singular values. -/
theorem rightThresholdProjector_eq {I K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix I K ℂ) (σ : K → ℝ) (δ : ℝ) :
    rightThresholdProjector V σ δ = V * svIndicator σ (Set.Ici δ) * Vᴴ :=
  rfl

/-! ## Definition 2 — the `CΠNOT` gate -/

/-- The Pauli `X` matrix on a single qubit (`Bool`). -/
def pauliX : Matrix Bool Bool ℂ := Matrix.of fun a b => if a = b then 0 else 1

/-- The Pauli `X` matrix is self-adjoint. -/
theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, Matrix.conjTranspose_apply]

/-- The Pauli `X` matrix squares to the identity. -/
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]

/-- **Definition 2.**  The `Π`-controlled NOT gate
`CΠNOT := X ⊗ Π + I ⊗ (I − Π)` acting on `Bool × I`. -/
def cPiNot {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) : Matrix (Bool × I) (Bool × I) ℂ :=
  pauliX ⊗ₖ P + (1 : Matrix Bool Bool ℂ) ⊗ₖ (1 - P)

/-- `CΠNOT` is self-adjoint for every orthogonal projector `Π`. -/
theorem cPiNot_conjTranspose {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P) :
    (cPiNot P)ᴴ = cPiNot P := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint
  have hstar1 : (1 - P)ᴴ = (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
  unfold cPiNot
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, pauliX_conjTranspose, hstar, hstar1,
    Matrix.conjTranspose_one]

/-- **Definition 2.**  For an orthogonal projector `Π` the gate
`CΠNOT = X ⊗ Π + I ⊗ (I − Π)` is unitary. -/
theorem cPiNot_mem_unitaryGroup {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P) :
    cPiNot P ∈ Matrix.unitaryGroup (Bool × I) ℂ := by
  have hIdem : P * P = P := hP.isIdempotentElem
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    cPiNot_conjTranspose P hP]
  unfold cPiNot
  -- cross terms vanish, diagonal ones are `1 ⊗ P` and `1 ⊗ (1 − P)`
  have hleft : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hIdem, sub_self]
  have hright : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hIdem, sub_self]
  have hboth : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hIdem, sub_self,
      sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, pauliX_mul_self,
    hIdem, hleft, hright, hboth, Matrix.one_mul, Matrix.mul_one, Matrix.kronecker_zero,
    zero_add, add_zero]
  rw [← Matrix.kronecker_add]
  have hPsum : P + (1 - P) = 1 := by abel
  rw [hPsum, Matrix.one_kronecker_one]

/-! ## Definition 44 — the trivial block-encoding -/

/-- **Definition 44.**  A unitary matrix is a `(1,0,0)`-block-encoding of
itself: taking the trivial one-dimensional frames `L = R = I`, the compressed
operator is the unitary itself and the error is zero.  (The `(1,0,0)`
convention counts `α = 1`, zero ancillas, and `ε = 0`; the `BlockEncoding`
structure here has no separate ancilla parameter.) -/
theorem trivialBlockEncoding {H : Type*} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    BlockEncoding U U 1 1 (1 : ℝ) 0 := by
  refine ⟨hU, ?_, ?_, by norm_num, le_rfl, ?_⟩
  · show (1 : Matrix H H ℂ)ᴴ * 1 = 1
    simp
  · show (1 : Matrix H H ℂ)ᴴ * 1 = 1
    simp
  · have hcomp : compress (1 : Matrix H H ℂ) U (1 : Matrix H H ℂ) = U := by
      unfold compress
      simp
    rw [hcomp]
    simp

end Qatlib.Papers.QSingValue19.QsVtMain.SourceDefinitions
