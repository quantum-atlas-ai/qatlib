/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression16.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourcePrediction — c001 of QRegression16

Fixed arXiv:1601.07823v2 (Schuld–Sinayskiy–Petruccione), *Prediction by linear
regression on a quantum computer*.

Claim c001 is the main result stated in the abstract and Sections II–III: the
algorithm works with amplitude-encoded data and outputs the linear-regression
prediction for a new input, using a reduced singular value decomposition of the
data matrix `X`. The Lean contract formalised here is the mathematical kernel
of that statement:

* Eq. (2)–(3), p.2: `w = X⁺ y` and `ỹ = x̃ᵀ w = Σ_r σ_r⁻¹(v_rᵀx̃)(u_rᵀy)`;
* Eq. (7), p.3: the data matrix is reconstructed from only `R` singular
  components, `X = U Σ Vᵀ`, so no sparsity of `X` is assumed;
* the fitted weights satisfy the least-squares normal equations
  `XᵀXw = Xᵀy`, equivalently `Xᵀ(Xw − y) = 0`, whose entrywise spelling is the
  stationarity condition of the classical least-squares problem.

The shared Moore–Penrose contract behind the identification `X⁺ = VΣ⁻¹Uᵀ` is
the one proved at complex level in
`Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_unique`
and its normal-equation corollary
`Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_normal`;
the paper's data are real, so the real Moore–Penrose identities are re-proved
here with the paper's transpose convention.

Scope note: the asymptotic runtime `O(log N κ² ε⁻³)` of Section IV is outside
the scope of this file. Its
`log N` and `ε⁻³` factors come from the quantum-PCA/density-matrix
exponentiation subroutine of [14] (Lloyd–Mohseni–Rebentrost), which is not part
of this paper's own mathematical derivation; the κ-dependence is covered by
claim c002 in `Postselection/SourcePostselection.lean`. The statement below is
therefore the algebraic prediction contract, not a circuit-level complexity
bound.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QRegression16.MainResults.Prediction

open Qatlib.Papers.QRegression16.MainResults.SourceModel

variable {N M R : ℕ}

/-- Fixed arXiv:1601.07823v2, Section II p.2 Eq. (3): the prediction written in
the source's singular-component form
`ỹ = Σ_r σ_r⁻¹ (Σ_j v_r(j) x̃_j)(Σ_m u_r(m) y_m)`. -/
theorem predictionFromSVD_eq_source_formula (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    predictionFromSVD σ U V x y =
      ∑ r, (σ r)⁻¹ * (∑ j, V j r * x j) * (∑ m, U m r * y m) :=
  rfl

/-- Fixed arXiv:1601.07823v2, Section II p.2 Eq. (2)–(3): evaluating the
prediction through the fitted parameter vector `w = X⁺ y` gives exactly the
singular-component prediction of Eq. (3). This is the algebraic readout used by
the algorithm; no orthonormality is needed for the identity itself. -/
theorem predictionByWeights_eq_predictionFromSVD (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    predictionByWeights σ U V x y = predictionFromSVD σ U V x y := by
  have hXp : pseudoinverseCandidate σ U V *ᵥ y =
      V *ᵥ (fun r => (σ r)⁻¹ * ((Uᵀ *ᵥ y) r)) := by
    rw [pseudoinverseCandidate]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    funext r
    rw [Matrix.mulVec_diagonal]
  unfold predictionByWeights fittedWeights predictionFromSVD
  rw [hXp, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- **Moore–Penrose identity 1** for the reduced-SVD candidate `X⁺ = VΣ⁻¹Uᵀ`:
`X X⁺ = U Uᵀ`. This is the central computation of the pseudoinverse contract,
`U Σ Vᵀ V Σ⁻¹ Uᵀ = U Σ Σ⁻¹ Uᵀ = U Uᵀ`, using `VᵀV = 1`. -/
theorem dataMatrix_mul_pseudoinverse (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hV : Vᵀ * V = 1) (hσ : ∀ r, σ r ≠ 0) :
    dataMatrix σ U V * pseudoinverseCandidate σ U V = U * Uᵀ := by
  have hD : diagonal σ * diagonal (fun r => (σ r)⁻¹) = (1 : Matrix (Fin R) (Fin R) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext r
    exact mul_inv_cancel₀ (hσ r)
  unfold dataMatrix pseudoinverseCandidate
  calc (U * diagonal σ * Vᵀ) * (V * diagonal (fun r => (σ r)⁻¹) * Uᵀ)
      = U * (diagonal σ * (Vᵀ * (V * (diagonal (fun r => (σ r)⁻¹) * Uᵀ)))) := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal σ * ((Vᵀ * V) * (diagonal (fun r => (σ r)⁻¹) * Uᵀ))) := by
        rw [← Matrix.mul_assoc (Vᵀ) V (diagonal (fun r => (σ r)⁻¹) * Uᵀ)]
    _ = U * (diagonal σ * ((1 : Matrix (Fin R) (Fin R) ℝ) * (diagonal (fun r => (σ r)⁻¹) * Uᵀ))) := by
        rw [hV]
    _ = U * (diagonal σ * (diagonal (fun r => (σ r)⁻¹) * Uᵀ)) := by
        rw [Matrix.one_mul]
    _ = U * ((diagonal σ * diagonal (fun r => (σ r)⁻¹)) * Uᵀ) := by
        rw [Matrix.mul_assoc (diagonal σ) (diagonal (fun r => (σ r)⁻¹)) Uᵀ]
    _ = U * ((1 : Matrix (Fin R) (Fin R) ℝ) * Uᵀ) := by rw [hD]
    _ = U * Uᵀ := by rw [Matrix.one_mul]

/-- **Moore–Penrose identity 2**: `X⁺ X = V Vᵀ`, obtained symmetrically from
`X⁺ X = V Σ⁻¹ (UᵀU) Σ Vᵀ` and `UᵀU = 1`. -/
theorem pseudoinverse_mul_dataMatrix (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hU : Uᵀ * U = 1) (hσ : ∀ r, σ r ≠ 0) :
    pseudoinverseCandidate σ U V * dataMatrix σ U V = V * Vᵀ := by
  have hD : diagonal (fun r => (σ r)⁻¹) * diagonal σ = (1 : Matrix (Fin R) (Fin R) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext r
    exact inv_mul_cancel₀ (hσ r)
  unfold dataMatrix pseudoinverseCandidate
  calc (V * diagonal (fun r => (σ r)⁻¹) * Uᵀ) * (U * diagonal σ * Vᵀ)
      = V * (diagonal (fun r => (σ r)⁻¹) * (Uᵀ * (U * (diagonal σ * Vᵀ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (diagonal (fun r => (σ r)⁻¹) * ((Uᵀ * U) * (diagonal σ * Vᵀ))) := by
        rw [← Matrix.mul_assoc (Uᵀ) U (diagonal σ * Vᵀ)]
    _ = V * (diagonal (fun r => (σ r)⁻¹) * ((1 : Matrix (Fin R) (Fin R) ℝ) * (diagonal σ * Vᵀ))) := by
        rw [hU]
    _ = V * (diagonal (fun r => (σ r)⁻¹) * (diagonal σ * Vᵀ)) := by
        rw [Matrix.one_mul]
    _ = V * ((diagonal (fun r => (σ r)⁻¹) * diagonal σ) * Vᵀ) := by
        rw [Matrix.mul_assoc (diagonal (fun r => (σ r)⁻¹)) (diagonal σ) Vᵀ]
    _ = V * ((1 : Matrix (Fin R) (Fin R) ℝ) * Vᵀ) := by rw [hD]
    _ = V * Vᵀ := by rw [Matrix.one_mul]

/-- **Moore–Penrose identity 3**: `(X X⁺)ᵀ = X X⁺`. -/
theorem dataMatrix_mul_pseudoinverse_symm (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hV : Vᵀ * V = 1) (hσ : ∀ r, σ r ≠ 0) :
    (dataMatrix σ U V * pseudoinverseCandidate σ U V)ᵀ =
      dataMatrix σ U V * pseudoinverseCandidate σ U V := by
  rw [dataMatrix_mul_pseudoinverse σ U V hV hσ]
  simp [Matrix.transpose_mul]

/-- **Moore–Penrose identity 4**: `(X⁺ X)ᵀ = X⁺ X`. -/
theorem pseudoinverse_mul_dataMatrix_symm (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hU : Uᵀ * U = 1) (hσ : ∀ r, σ r ≠ 0) :
    (pseudoinverseCandidate σ U V * dataMatrix σ U V)ᵀ =
      pseudoinverseCandidate σ U V * dataMatrix σ U V := by
  rw [pseudoinverse_mul_dataMatrix σ U V hU hσ]
  simp [Matrix.transpose_mul]

/-- Fixed arXiv:1601.07823v2, Section II p.2 Eq. (2): `w = X⁺ y` satisfies the
least-squares normal equations `Xᵀ X w = Xᵀ y`. This is the stationarity
condition of the (unregularised) least-squares problem minimised in the paper,
and the real-level counterpart of
`Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_normal`
(which states `Aᴴ (A x − b) = 0` over `ℂ`). -/
theorem fittedWeights_normal_equations (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hσ : ∀ r, σ r ≠ 0)
    (y : Fin M → ℝ) :
    (dataMatrix σ U V)ᵀ *ᵥ (dataMatrix σ U V *ᵥ fittedWeights σ U V y) =
      (dataMatrix σ U V)ᵀ *ᵥ y := by
  have hXw : dataMatrix σ U V *ᵥ fittedWeights σ U V y = U *ᵥ (Uᵀ *ᵥ y) := by
    unfold fittedWeights
    rw [Matrix.mulVec_mulVec, dataMatrix_mul_pseudoinverse σ U V hV hσ,
      ← Matrix.mulVec_mulVec]
  have htrans : (dataMatrix σ U V)ᵀ = V * diagonal σ * Uᵀ := by
    simp [dataMatrix, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [hXw, htrans]
  calc (V * diagonal σ * Uᵀ) *ᵥ (U *ᵥ (Uᵀ *ᵥ y))
      = ((V * diagonal σ * Uᵀ) * U) *ᵥ (Uᵀ *ᵥ y) := by rw [Matrix.mulVec_mulVec]
    _ = (V * diagonal σ * (Uᵀ * U)) *ᵥ (Uᵀ *ᵥ y) := by
        rw [Matrix.mul_assoc (V * diagonal σ) Uᵀ U]
    _ = (V * diagonal σ * (1 : Matrix (Fin R) (Fin R) ℝ)) *ᵥ (Uᵀ *ᵥ y) := by rw [hU]
    _ = (V * diagonal σ) *ᵥ (Uᵀ *ᵥ y) := by rw [Matrix.mul_one]
    _ = (V * diagonal σ * Uᵀ) *ᵥ y := by rw [Matrix.mulVec_mulVec]

/-- Fixed arXiv:1601.07823v2, Section II p.2: the residual `X w − y` is
orthogonal to the column space of `X`, i.e. `(X z)ᵀ(X w − y) = 0` for every `z`.
This is the coordinate-free least-squares optimality statement behind Eq. (2). -/
theorem fittedWeights_residual_orthogonal (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hσ : ∀ r, σ r ≠ 0)
    (y : Fin M → ℝ) (z : Fin N → ℝ) :
    (dataMatrix σ U V *ᵥ z) ⬝ᵥ
        (dataMatrix σ U V *ᵥ fittedWeights σ U V y - y) = 0 := by
  have hnorm := fittedWeights_normal_equations σ U V hU hV hσ y
  have hzero : (dataMatrix σ U V)ᵀ *ᵥ
      (dataMatrix σ U V *ᵥ fittedWeights σ U V y - y) = 0 := by
    rw [Matrix.mulVec_sub, hnorm, sub_self]
  have hdot : (dataMatrix σ U V *ᵥ z) ⬝ᵥ
      (dataMatrix σ U V *ᵥ fittedWeights σ U V y - y) =
      z ⬝ᵥ ((dataMatrix σ U V)ᵀ *ᵥ
        (dataMatrix σ U V *ᵥ fittedWeights σ U V y - y)) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose,
      ← dotProduct_comm]
  rw [hdot, hzero, dotProduct_zero]

/-- **Claim c001 (fixed arXiv:1601.07823v2, abstract and Sections II–III).**
Main result contract for the quantum linear-regression prediction algorithm:

For real data given by a reduced SVD `X = UΣVᵀ` with orthonormal singular-vector
matrices and nonzero singular values, the fitted weights `w = X⁺ y` computed
from the rank-`R` data

1. yield the singular-component prediction `ỹ = Σ_r σ_r⁻¹(v_rᵀx̃)(u_rᵀy)`
   of Eq. (3) for every new input `x̃`;
2. satisfy the least-squares normal equations `XᵀXw = Xᵀy`;
3. have residual orthogonal to the column space of `X`;
4. satisfy the four Moore–Penrose identities, so the candidate `VΣ⁻¹Uᵀ` is the
   reduced-SVD Moore–Penrose pseudoinverse (the same contract that
   `matrixPseudoinverse_unique` proves in `ℂ`).

The hypothesis list contains only orthonormality of the singular vectors and
nonvanishing of the `R` used singular values: no sparsity of `X` is assumed,
matching the paper's low-rank requirement on `X†X`. Runtime statements are
Section IV and documented as out of scope above. -/
theorem source_linear_regression_prediction (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hσ : ∀ r, σ r ≠ 0)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    predictionByWeights σ U V x y = predictionFromSVD σ U V x y ∧
    (dataMatrix σ U V)ᵀ *ᵥ (dataMatrix σ U V *ᵥ fittedWeights σ U V y) =
      (dataMatrix σ U V)ᵀ *ᵥ y ∧
    (∀ z : Fin N → ℝ, (dataMatrix σ U V *ᵥ z) ⬝ᵥ
      (dataMatrix σ U V *ᵥ fittedWeights σ U V y - y) = 0) ∧
    dataMatrix σ U V * pseudoinverseCandidate σ U V * dataMatrix σ U V =
      dataMatrix σ U V ∧
    pseudoinverseCandidate σ U V * dataMatrix σ U V * pseudoinverseCandidate σ U V =
      pseudoinverseCandidate σ U V ∧
    (dataMatrix σ U V * pseudoinverseCandidate σ U V)ᵀ =
      dataMatrix σ U V * pseudoinverseCandidate σ U V ∧
    (pseudoinverseCandidate σ U V * dataMatrix σ U V)ᵀ =
      pseudoinverseCandidate σ U V * dataMatrix σ U V := by
  refine ⟨predictionByWeights_eq_predictionFromSVD σ U V x y,
    fittedWeights_normal_equations σ U V hU hV hσ y,
    fun z => fittedWeights_residual_orthogonal σ U V hU hV hσ y z, ?_, ?_, ?_, ?_⟩
  · -- X X⁺ X = X
    rw [dataMatrix_mul_pseudoinverse σ U V hV hσ]
    unfold dataMatrix
    calc (U * Uᵀ) * (U * diagonal σ * Vᵀ)
        = U * (Uᵀ * (U * (diagonal σ * Vᵀ))) := by simp only [Matrix.mul_assoc]
      _ = U * ((Uᵀ * U) * (diagonal σ * Vᵀ)) := by
          rw [← Matrix.mul_assoc Uᵀ U (diagonal σ * Vᵀ)]
      _ = U * ((1 : Matrix (Fin R) (Fin R) ℝ) * (diagonal σ * Vᵀ)) := by rw [hU]
      _ = U * (diagonal σ * Vᵀ) := by rw [Matrix.one_mul]
      _ = U * diagonal σ * Vᵀ := by rw [← Matrix.mul_assoc]
  · -- X⁺ X X⁺ = X⁺
    rw [pseudoinverse_mul_dataMatrix σ U V hU hσ]
    unfold pseudoinverseCandidate
    calc (V * Vᵀ) * (V * diagonal (fun r => (σ r)⁻¹) * Uᵀ)
        = V * (Vᵀ * (V * (diagonal (fun r => (σ r)⁻¹) * Uᵀ))) := by
          simp only [Matrix.mul_assoc]
      _ = V * ((Vᵀ * V) * (diagonal (fun r => (σ r)⁻¹) * Uᵀ)) := by
          rw [← Matrix.mul_assoc Vᵀ V (diagonal (fun r => (σ r)⁻¹) * Uᵀ)]
      _ = V * ((1 : Matrix (Fin R) (Fin R) ℝ) * (diagonal (fun r => (σ r)⁻¹) * Uᵀ)) := by rw [hV]
      _ = V * (diagonal (fun r => (σ r)⁻¹) * Uᵀ) := by rw [Matrix.one_mul]
      _ = V * diagonal (fun r => (σ r)⁻¹) * Uᵀ := by rw [← Matrix.mul_assoc]
  · exact dataMatrix_mul_pseudoinverse_symm σ U V hV hσ
  · exact pseudoinverse_mul_dataMatrix_symm σ U V hU hσ

end Qatlib.Papers.QRegression16.MainResults.Prediction
