/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.NativeDomination

/-!
# Reduced-state bounds for orthogonal purification errors

`reduced` assigns an amplitude matrix its row Gram matrix. Orthogonality between ideal
purification rows and error rows removes cross terms, giving a positive error decomposition and
a semidefinite domination estimate.

When both amplitude matrices are normalized, a lower bound on the squared ideal coefficients
yields the trace-distance estimate `orthogonal_errors_distance`. Equality of amplitude Gram
matrices also transports through any common output matrix. See [Watrous2018].

## Main statements

* `reduced_errors`: decomposition into ideal and positive error terms.
* `reduced_errors_domination`: domination from coefficient lower bounds.
* `orthogonal_errors_distance`: the normalized reduced-state trace-distance bound.
* `reduced_gram_transport`: common multiplication preserves equality of reduced operators.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification
variable {I O P : Type*} [Fintype I] [Fintype O] [Fintype P] [DecidableEq I]

/-- The reduced operator `A * Aᴴ` associated with a rectangular amplitude matrix. -/
def reduced (A : Matrix O P ℂ) : Matrix O O ℂ := A * Aᴴ

/-- The trace of the reduced operator is the sum of the squared moduli of all amplitude entries. -/
theorem trace_reduced (A : Matrix O P ℂ) :
    Matrix.trace (reduced A) = ((∑ o, ∑ p, ‖A o p‖^2 : ℝ) : ℂ) := by
  simp only [reduced, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p _
  rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

omit [Fintype O] in

/-- If the rows of `Phi` are orthonormal, the reduced operator of `V * Phi` is `V * Vᴴ`. -/
theorem reduced_orthonormal (V : Matrix O I ℂ) (Phi : Matrix I P ℂ)
    (hPhi : Phi * Phiᴴ = 1) : reduced (V * Phi) = V * Vᴴ := by
  simp only [reduced, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Phi,
    hPhi, Matrix.one_mul]

omit [Fintype O] in

/-- For orthonormal rows of `Phi` and `Phi * Eᴴ = 0`, the reduced perturbed amplitude splits
into its squared-coefficient ideal term and the positive error term `(V * E) * (V * E)ᴴ`. -/
theorem reduced_errors (V : Matrix O I ℂ) (Phi E : Matrix I P ℂ)
    (alpha : I → ℂ) (hPhi : Phi * Phiᴴ = 1) (hE : Phi * Eᴴ = 0) :
    reduced (V * (Matrix.diagonal alpha * Phi + E)) =
      V * Matrix.diagonal (fun i => ((‖alpha i‖^2 : ℝ) : ℂ)) * Vᴴ +
        (V * E) * (V * E)ᴴ := by
  have hE' : E * Phiᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hE
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have hD : Matrix.diagonal alpha * (Matrix.diagonal alpha)ᴴ =
      Matrix.diagonal (fun i => ((‖alpha i‖^2 : ℝ) : ℂ)) := by
    ext i j
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    change alpha k * star (alpha k) = _
    rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hm : (Matrix.diagonal alpha * Phi + E) *
      (Matrix.diagonal alpha * Phi + E)ᴴ =
        Matrix.diagonal (fun i => ((‖alpha i‖^2 : ℝ) : ℂ)) + E * Eᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.add_mul, Matrix.mul_add]
    rw [Matrix.mul_assoc (Matrix.diagonal alpha), ← Matrix.mul_assoc Phi, hPhi,
      Matrix.one_mul, hD, Matrix.mul_assoc (Matrix.diagonal alpha), hE,
      Matrix.mul_zero, ← Matrix.mul_assoc E, hE', Matrix.zero_mul]
    simp
  simp only [reduced, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal alpha * Phi + E), hm,
    Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc]

/-- Under row orthonormality and error orthogonality, coefficient bounds `1 - delta ≤ ‖alpha i‖
^ 2` imply that the perturbed reduced operator dominates `(1 - delta)` times the ideal
reduced operator. -/
theorem reduced_errors_domination (V : Matrix O I ℂ) (Phi E : Matrix I P ℂ)
    (alpha : I → ℂ) (delta : ℝ)
    (hPhi : Phi * Phiᴴ = 1) (hE : Phi * Eᴴ = 0)
    (halpha : ∀ i, 1-delta ≤ ‖alpha i‖^2) :
    (reduced (V * (Matrix.diagonal alpha * Phi + E)) -
      (((1-delta : ℝ) : ℂ) • reduced (V * Phi))).PosSemidef := by
  have hdiag : (Matrix.diagonal (fun i =>
      ((‖alpha i‖^2 - (1-delta) : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (halpha i))
  have hpos := hdiag.mul_mul_conjTranspose_same V
  have herror := Matrix.posSemidef_self_mul_conjTranspose (V * E)
  have heq : reduced (V * (Matrix.diagonal alpha * Phi + E)) -
      (((1-delta : ℝ) : ℂ) • reduced (V * Phi)) =
      V * Matrix.diagonal (fun i => ((‖alpha i‖^2-(1-delta) : ℝ) : ℂ)) * Vᴴ +
        (V * E) * (V * E)ᴴ := by
    rw [reduced_errors V Phi E alpha hPhi hE, reduced_orthonormal V Phi hPhi]
    have hD : Matrix.diagonal (fun i => ((‖alpha i‖^2-(1-delta) : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => ((‖alpha i‖^2 : ℝ) : ℂ)) -
          (((1-delta : ℝ) : ℂ) • (1 : Matrix I I ℂ)) := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [hD, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    abel
  rw [heq]
  exact hpos.add herror

/-- If both ideal and perturbed amplitudes are normalized, row orthonormality, orthogonal
errors, and `1 - delta ≤ ‖alpha i‖ ^ 2` with nonnegative `delta` bound their reduced trace
distance by `delta`. -/
theorem orthogonal_errors_distance (V : Matrix O I ℂ) (Phi E : Matrix I P ℂ)
    (alpha : I → ℂ) (delta : ℝ) (hd : 0 ≤ delta)
    (hPhi : Phi * Phiᴴ = 1) (hE : Phi * Eᴴ = 0)
    (halpha : ∀ i, 1-delta ≤ ‖alpha i‖^2)
    (hunit : ∑ o, ∑ p, ‖(V * Phi) o p‖^2 = 1)
    (hunit' : ∑ o, ∑ p, ‖(V * (Matrix.diagonal alpha * Phi + E)) o p‖^2 = 1) :
    Matrix.traceNorm (reduced (V * Phi) -
      reduced (V * (Matrix.diagonal alpha * Phi + E))) / 2 ≤ delta := by
  apply Domination.density_domination_distance
    (reduced (V * Phi)) (reduced (V * (Matrix.diagonal alpha * Phi + E)))
  · exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [trace_reduced, hunit]; rfl
  · rw [trace_reduced, hunit']; rfl
  · exact hd
  · exact reduced_errors_domination V Phi E alpha delta hPhi hE halpha

omit [Fintype O] [DecidableEq I] in

/-- Equal row Gram matrices for `A` and `B` give equal reduced operators after multiplication by
the same matrix `V`. -/
theorem reduced_gram_transport (V : Matrix O I ℂ) (A B : Matrix I P ℂ)
    (hAB : A*Aᴴ=B*Bᴴ) : reduced (V*A)=reduced (V*B) := by
  calc
    _ = V*(A*Aᴴ)*Vᴴ := by simp only [reduced,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = V*(B*Bᴴ)*Vᴴ := by rw [hAB]
    _ = _ := by simp only [reduced,Matrix.conjTranspose_mul,Matrix.mul_assoc]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification
