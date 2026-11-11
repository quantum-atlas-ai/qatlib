/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ENNReal.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# PauliPrecond26 / EncodingObstr — Theorem 3 and Corollary 4

Source: H. Nie, Z. Lai, D. An, *Pauli-structured preconditioning for quantum
linear system solvers*, arXiv:2606.01733v1 (2026-06-01), Theorem 3 (pp. 5--6)
and Corollary 4 (p. 6).

This file formalises the oracle-model obstruction of separate block-encoding
composition.  The paper writes `κ_A := 1 / σ_min(A)` and, for a normalized
operator `M` with block-encoding normalization `α`, the effective QLS
condition parameter `κ_eff(M; α) := α / σ_min(M)`, with the convention
`κ_eff(M; α) = +∞` when `M` is singular.  We encode that value as an element of
`ℝ≥0∞` using the elementary identity `σ_min(M) = ‖M⁻¹‖⁻¹` for invertible `M`;
the singular branch is the top element.

The two core inequalities are

* `κ_eff(PA; α_P α_A) ≥ α_A / σ_min(A)`  (left composition),
* `κ_eff(PAPᴴ; α_P² α_A) ≥ α_A / σ_min(A)`  (symmetric composition),

under the certified-normalization hypothesis `α_P ≥ ‖P‖`.  The proof is the
norm inequality `‖A⁻¹‖ ≤ ‖(PA)⁻¹‖ ‖P‖` (resp.
`‖A⁻¹‖ ≤ ‖P‖² ‖(PAPᴴ)⁻¹‖`), obtained from the telescoping identities
`A⁻¹ = (PA)⁻¹ P` and `A⁻¹ = Pᴴ (PAPᴴ)⁻¹ P`.

-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal NNReal

namespace Qatlib.Papers.PauliPrecond26.EncodingObstr

variable {N : ℕ}

/-- The effective QLS condition parameter `κ_eff(M; α) = α / σ_min(M)` of
Theorem 3, with the convention `+∞` for singular `M`.

`σ_min(M)` is represented through `‖M⁻¹‖⁻¹`; for invertible `M` this is the
smallest singular value, and for singular `M` the value is set to `⊤`.
Docstring source: Theorem 3, p. 5, the definition `κ_L := κ_eff(PA; α_L)` and
`κ_S := κ_eff(PAPᴴ; α_S)` with the `+∞` convention stated on p. 6. -/
def kappaEff (M : Matrix (Fin N) (Fin N) ℂ) (α : ℝ≥0) : ℝ≥0∞ := by
  classical
  exact if IsUnit M.det then (α : ℝ≥0∞) * (‖M⁻¹‖₊ : ℝ≥0∞) else ⊤

/-- On the invertible branch `kappaEff` is the product of the normalization and
the inverse operator norm.  Reused in the proofs below and by consumers. -/
theorem kappaEff_of_isUnit {M : Matrix (Fin N) (Fin N) ℂ} {α : ℝ≥0}
    (hM : IsUnit M.det) :
    kappaEff M α = (α : ℝ≥0∞) * (‖M⁻¹‖₊ : ℝ≥0∞) := by
  unfold kappaEff
  rw [if_pos hM]

/-- On the singular branch the effective condition parameter is `+∞`. -/
theorem kappaEff_of_not_isUnit {M : Matrix (Fin N) (Fin N) ℂ} {α : ℝ≥0}
    (hM : ¬ IsUnit M.det) : kappaEff M α = ⊤ := by
  unfold kappaEff
  rw [if_neg hM]

/-- Theorem 3, left-composition step: for an invertible `A`, the inverse of the
left product satisfies `A⁻¹ = (PA)⁻¹ P`, hence
`‖A⁻¹‖ ≤ ‖(PA)⁻¹‖ ‖P‖`.

Source: Theorem 3, pp. 5--6, proof identity `(PA)⁻¹ = A⁻¹ P⁻¹` in operator
form.  No block-encoding structure is needed for this algebraic inequality. -/
theorem inv_norm_le_inv_mul_norm_left {A P : Matrix (Fin N) (Fin N) ℂ}
    (hPA : IsUnit (P * A).det) (hA : IsUnit A.det) :
    ‖A⁻¹‖ ≤ ‖(P * A)⁻¹‖ * ‖P‖ := by
  have hPAinv : (P * A)⁻¹ * (P * A) = 1 := Matrix.nonsing_inv_mul _ hPA
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hrepr : A⁻¹ = (P * A)⁻¹ * P := by
    calc
      A⁻¹ = 1 * A⁻¹ := (one_mul _).symm
      _ = ((P * A)⁻¹ * (P * A)) * A⁻¹ := by rw [hPAinv]
      _ = (P * A)⁻¹ * P * (A * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (P * A)⁻¹ * P * 1 := by rw [hAinv]
      _ = (P * A)⁻¹ * P := by rw [Matrix.mul_one]
  calc
    ‖A⁻¹‖ = ‖(P * A)⁻¹ * P‖ := by rw [hrepr]
    _ ≤ ‖(P * A)⁻¹‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _

/-- The conjugate-transpose inverse of a matrix is a left inverse. -/
theorem conjTranspose_nonsing_inv_mul {P : Matrix (Fin N) (Fin N) ℂ}
    (hPH : IsUnit (Pᴴ).det) : (Pᴴ)⁻¹ * Pᴴ = 1 :=
  Matrix.nonsing_inv_mul _ hPH

/-- Theorem 3, symmetric-composition step: for invertible `A` and `Pᴴ`, the
inverse of `Q = PAPᴴ` satisfies `A⁻¹ = Pᴴ Q⁻¹ P`.

Source: Theorem 3, p. 6, proof of the symmetric inequality
`κ_S = α_P² α_A / σ_min(PAPᴴ)`. -/
theorem inv_eq_conj_mul_inv_mul {A P : Matrix (Fin N) (Fin N) ℂ}
    (hQ : IsUnit (P * A * Pᴴ).det) (hPH : IsUnit (Pᴴ).det) :
    A⁻¹ = Pᴴ * (P * A * Pᴴ)⁻¹ * P := by
  have hQinv : (P * A * Pᴴ)⁻¹ * (P * A * Pᴴ) = 1 := Matrix.nonsing_inv_mul _ hQ
  have hPHright : Pᴴ * (Pᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPH
  have hstep : (P * A * Pᴴ)⁻¹ * P * A = (Pᴴ)⁻¹ := by
    calc
      (P * A * Pᴴ)⁻¹ * P * A
          = (P * A * Pᴴ)⁻¹ * P * A * 1 := (Matrix.mul_one _).symm
      _ = (P * A * Pᴴ)⁻¹ * P * A * (Pᴴ * (Pᴴ)⁻¹) := by rw [hPHright]
      _ = ((P * A * Pᴴ)⁻¹ * (P * A * Pᴴ)) * (Pᴴ)⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = 1 * (Pᴴ)⁻¹ := by rw [hQinv]
      _ = (Pᴴ)⁻¹ := one_mul _
  have hleft : (Pᴴ * (P * A * Pᴴ)⁻¹ * P) * A = 1 := by
    calc
      (Pᴴ * (P * A * Pᴴ)⁻¹ * P) * A
          = Pᴴ * ((P * A * Pᴴ)⁻¹ * P * A) := by simp only [Matrix.mul_assoc]
      _ = Pᴴ * (Pᴴ)⁻¹ := by rw [hstep]
      _ = 1 := hPHright
  exact Matrix.inv_eq_left_inv hleft

/-- Theorem 3, symmetric-composition norm bound:
`‖A⁻¹‖ ≤ ‖P‖² ‖(PAPᴴ)⁻¹‖`, obtained by taking norms in
`A⁻¹ = Pᴴ (PAPᴴ)⁻¹ P` and using `‖Pᴴ‖ = ‖P‖`.

Source: Theorem 3, p. 6 (the displayed chain
`κ_S = α_P² α_A / σ_min(PAPᴴ) ≥ α_P² α_A / (‖P‖² σ_min(A)) ≥ α_A / σ_min(A)`). -/
theorem inv_norm_le_conj_mul_inv_mul_norm {A P : Matrix (Fin N) (Fin N) ℂ}
    (hQ : IsUnit (P * A * Pᴴ).det) (hPH : IsUnit (Pᴴ).det) :
    ‖A⁻¹‖ ≤ ‖P‖ * ‖(P * A * Pᴴ)⁻¹‖ * ‖P‖ := by
  have hrepr := inv_eq_conj_mul_inv_mul (A := A) (P := P) hQ hPH
  calc
    ‖A⁻¹‖ = ‖Pᴴ * (P * A * Pᴴ)⁻¹ * P‖ := by rw [hrepr]
    _ ≤ ‖Pᴴ * (P * A * Pᴴ)⁻¹‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Pᴴ‖ * ‖(P * A * Pᴴ)⁻¹‖) * ‖P‖ := by
          exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖P‖ * ‖(P * A * Pᴴ)⁻¹‖ * ‖P‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]

/-- **c001, Theorem 3 (left branch).**  Assume `A` is invertible and the
preconditioner normalization is certified, `α_P ≥ ‖P‖`.  Then the effective
QLS condition parameter of the left preconditioned operator obeys
`κ_eff(PA; α_P α_A) ≥ α_A / σ_min(A) = α_A κ_A`, with the singular branch read
as `+∞`.

Source: Theorem 3, pp. 5--6, first displayed inequality
`κ_L ≥ α_A κ_A`. -/
theorem limitation_left (A P : Matrix (Fin N) (Fin N) ℂ)
    (αA αP : ℝ≥0) (hA : IsUnit A.det) (hPnorm : ‖P‖₊ ≤ αP) :
    kappaEff A αA ≤ kappaEff (P * A) (αP * αA) := by
  classical
  by_cases hPA : IsUnit (P * A).det
  · rw [kappaEff_of_isUnit hA, kappaEff_of_isUnit hPA]
    apply ENNReal.coe_le_coe.mpr
    have hnorm : ‖A⁻¹‖₊ ≤ ‖(P * A)⁻¹‖₊ * ‖P‖₊ := by
      exact_mod_cast inv_norm_le_inv_mul_norm_left hPA hA
    calc
      αA * ‖A⁻¹‖₊ ≤ αA * (‖(P * A)⁻¹‖₊ * ‖P‖₊) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ αA * (‖(P * A)⁻¹‖₊ * αP) := by
        gcongr
      _ = (αP * αA) * ‖(P * A)⁻¹‖₊ := by ring
  · rw [kappaEff_of_not_isUnit hPA]
    exact le_top

/-- **c001, Theorem 3 (symmetric branch).**  Assume `A` is invertible and
`α_P ≥ ‖P‖`.  Then
`κ_eff(PAPᴴ; α_P² α_A) ≥ α_A / σ_min(A) = α_A κ_A`, with the singular branch
read as `+∞`.

Source: Theorem 3, pp. 5--6, second displayed inequality `κ_S ≥ α_A κ_A`. -/
theorem limitation_symm (A P : Matrix (Fin N) (Fin N) ℂ)
    (αA αP : ℝ≥0) (hA : IsUnit A.det) (hPnorm : ‖P‖₊ ≤ αP) :
    kappaEff A αA ≤ kappaEff (P * A * Pᴴ) (αP ^ 2 * αA) := by
  classical
  by_cases hQ : IsUnit (P * A * Pᴴ).det
  · have hdet : (P * A * Pᴴ).det = P.det * A.det * star P.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hPdet : IsUnit P.det := by
      have h0 : IsUnit (P.det * A.det * star P.det) := by simpa [hdet] using hQ
      exact (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp h0).1).1
    have hPH : IsUnit (Pᴴ).det := by
      rw [Matrix.det_conjTranspose]
      exact IsUnit.star hPdet
    rw [kappaEff_of_isUnit hA, kappaEff_of_isUnit hQ]
    apply ENNReal.coe_le_coe.mpr
    have hnorm : ‖A⁻¹‖₊ ≤ ‖P‖₊ * ‖(P * A * Pᴴ)⁻¹‖₊ * ‖P‖₊ := by
      exact_mod_cast inv_norm_le_conj_mul_inv_mul_norm hQ hPH
    calc
      αA * ‖A⁻¹‖₊ ≤ αA * (‖P‖₊ * ‖(P * A * Pᴴ)⁻¹‖₊ * ‖P‖₊) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ αA * (αP * ‖(P * A * Pᴴ)⁻¹‖₊ * αP) := by
        gcongr
      _ = (αP ^ 2 * αA) * ‖(P * A * Pᴴ)⁻¹‖₊ := by ring
  · rw [kappaEff_of_not_isUnit hQ]
    exact le_top

/-- **c001, Theorem 3 (combined form).**  Under the hypotheses of Theorem 3,
both effective QLS condition parameters satisfy the obstruction bounds.

Source: Theorem 3, pp. 5--6.  The system matrix obeys `‖A‖ ≤ 1` and `α_A ≥ 1`
in the paper, but these hypotheses are not used by the norm inequality; they are
kept out of the Lean statement to avoid strengthening the theorem. -/
theorem limitation_separate_blockencoding (A P : Matrix (Fin N) (Fin N) ℂ)
    (αA αP : ℝ≥0) (hA : IsUnit A.det) (hPnorm : ‖P‖₊ ≤ αP) :
    kappaEff A αA ≤ kappaEff (P * A) (αP * αA) ∧
    kappaEff A αA ≤ kappaEff (P * A * Pᴴ) (αP ^ 2 * αA) :=
  ⟨limitation_left A P αA αP hA hPnorm,
   limitation_symm A P αA αP hA hPnorm⟩

/-- **c002, Corollary 4.**  Let `S` be any oracle query complexity function
that is monotone nondecreasing in the effective QLS condition parameter.  Then
within the separate block-encoding composition model, preconditioning cannot
decrease either `S(κ_L)` or `S(κ_S)` below the baseline value `S(α_A κ_A)`.

Source: Corollary 4, p. 6, whose proof invokes Theorem 3 and monotonicity. -/
theorem preconditioning_cannot_improve_query
    (S : ℝ≥0∞ → ℝ≥0∞) (hmono : Monotone S)
    (A P : Matrix (Fin N) (Fin N) ℂ) (αA αP : ℝ≥0)
    (hA : IsUnit A.det) (hPnorm : ‖P‖₊ ≤ αP) :
    S (kappaEff A αA) ≤ S (kappaEff (P * A) (αP * αA)) ∧
    S (kappaEff A αA) ≤ S (kappaEff (P * A * Pᴴ) (αP ^ 2 * αA)) :=
  ⟨hmono (limitation_left A P αA αP hA hPnorm),
   hmono (limitation_symm A P αA αP hA hPnorm)⟩

end Qatlib.Papers.PauliPrecond26.EncodingObstr
