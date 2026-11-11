/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Short-step diagonal and Fourier factorization

This module formalizes the finite-grid kernel factorization used in [Zalka1998]. `stepMatrix`
places the input index in the column and the output index in the row, and
`stepPhase_factorization` splits its phase into an input diagonal term, a Fourier term, and an
output diagonal term.

Under the lattice relation `m * Δx ^ 2 / Δt = A * (2 * Real.pi / N)`, `fourierMatrix` becomes
`twistedDFT`. Invertibility of `A` modulo the nonzero grid size supplies the orthogonality
needed for unitarity of the normalized short-step matrix.

## Main statements

* `stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal` gives the matrix factorization in
  application order.
* `stepMatrix_basis_coefficient` verifies the input-to-output coefficient convention.
* `twistedDFT_mul_star_of_isUnit` proves scaled orthogonality of a unit-twisted Fourier matrix.
* `shortTimeStep_two_diagonal_and_fourier` packages factorization, the Fourier identification,
  diagonal unitarity, and step unitarity.

## References

* [Zalka, 1998][Zalka1998]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QSystemSim96.MainResults

variable (N : ℕ) [NeZero N]

/-- The complex reciprocal of the real square root of the grid size `N`. -/
def stepNormalisation (N : ℕ) : ℂ := ((Real.sqrt (N : ℝ) : ℂ))⁻¹

/-- The exponential phase with exponent `I * (-(m / 2) * (n.val - n'.val) ^ 2 * Δx ^ 2 / Δt + V
n * Δt)`, using `n` as input and `n'` as output. -/
def stepPhase (m Δx Δt : ℝ) (V : ZMod N → ℝ) (n n' : ZMod N) : ℂ :=
  Complex.exp (Complex.I * (((-(m / 2) * ((n.val : ℝ) - (n'.val : ℝ)) ^ 2 * Δx ^ 2 / Δt +
    V n * Δt : ℝ)) : ℂ))

/-- The input-index phase combining the negative quadratic kinetic term at `n` with the
potential term `V n * Δt`. -/
def diagonalLeftPhase (m Δx Δt : ℝ) (V : ZMod N → ℝ) (n : ZMod N) : ℂ :=
  Complex.exp (Complex.I * (((-(m / 2) * (n.val : ℝ) ^ 2 * Δx ^ 2 / Δt +
    V n * Δt : ℝ)) : ℂ))

/-- The bilinear phase `exp (I * (m * n.val * n'.val * Δx ^ 2 / Δt))` on a pair of grid indices. -/
def fourierPhase (m Δx Δt : ℝ) (n n' : ZMod N) : ℂ :=
  Complex.exp (Complex.I * (((m * (n.val : ℝ) * (n'.val : ℝ) * Δx ^ 2 / Δt : ℝ)) : ℂ))

/-- The output-index phase `exp (I * (-(m / 2) * n'.val ^ 2 * Δx ^ 2 / Δt))`. -/
def diagonalRightPhase (m Δx Δt : ℝ) (n' : ZMod N) : ℂ :=
  Complex.exp (Complex.I * (((-(m / 2) * (n'.val : ℝ) ^ 2 * Δx ^ 2 / Δt : ℝ)) : ℂ))

omit [NeZero N] in

/-- The short-step phase factors as the input diagonal phase, bilinear Fourier phase, and output
diagonal phase. -/
theorem stepPhase_factorization (m Δx Δt : ℝ) (V : ZMod N → ℝ) (n n' : ZMod N) :
    stepPhase N m Δx Δt V n n' =
      diagonalLeftPhase N m Δx Δt V n * fourierPhase N m Δx Δt n n' *
        diagonalRightPhase N m Δx Δt n' := by
  unfold stepPhase diagonalLeftPhase fourierPhase diagonalRightPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hreal : (-(m / 2) * ((n.val : ℝ) - (n'.val : ℝ)) ^ 2 * Δx ^ 2 / Δt + V n * Δt : ℝ) =
      (-(m / 2) * (n.val : ℝ) ^ 2 * Δx ^ 2 / Δt + V n * Δt) +
        (m * (n.val : ℝ) * (n'.val : ℝ) * Δx ^ 2 / Δt) +
          (-(m / 2) * (n'.val : ℝ) ^ 2 * Δx ^ 2 / Δt) := by
    ring
  have hcast : (((-(m / 2) * ((n.val : ℝ) - (n'.val : ℝ)) ^ 2 * Δx ^ 2 / Δt +
        V n * Δt : ℝ)) : ℂ) =
      (((-(m / 2) * (n.val : ℝ) ^ 2 * Δx ^ 2 / Δt + V n * Δt : ℝ)) : ℂ) +
        (((m * (n.val : ℝ) * (n'.val : ℝ) * Δx ^ 2 / Δt : ℝ)) : ℂ) +
          (((-(m / 2) * (n'.val : ℝ) ^ 2 * Δx ^ 2 / Δt : ℝ)) : ℂ) := by
    rw [hreal]
    push_cast
    ring
  rw [hcast]
  ring

omit [NeZero N] in

/-- The bilinear Fourier phase is symmetric in its two grid indices. -/
theorem fourierPhase_comm (m Δx Δt : ℝ) (a b : ZMod N) :
    fourierPhase N m Δx Δt a b = fourierPhase N m Δx Δt b a := by
  unfold fourierPhase
  congr 1
  push_cast
  ring

/-- The normalized short-step matrix whose row is the output index and whose column is the input
index. -/
def stepMatrix (m Δx Δt : ℝ) (V : ZMod N → ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun output input => stepNormalisation N * stepPhase N m Δx Δt V input output

/-- The diagonal matrix of input kinetic and potential phases. -/
def diagonalLeft (m Δx Δt : ℝ) (V : ZMod N → ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.diagonal (fun n => diagonalLeftPhase N m Δx Δt V n)

/-- The unnormalized matrix of bilinear Fourier phases on the finite cyclic grid. -/
def fourierMatrix (m Δx Δt : ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun n n' => fourierPhase N m Δx Δt n n'

/-- The diagonal matrix of output kinetic phases. -/
def diagonalRight (m Δx Δt : ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.diagonal (fun n => diagonalRightPhase N m Δx Δt n)

/-- The short-step matrix equals its normalization scalar times the product of the output
diagonal matrix, Fourier matrix, and input diagonal matrix. -/
theorem stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal
    (m Δx Δt : ℝ) (V : ZMod N → ℝ) :
    stepMatrix N m Δx Δt V =
      stepNormalisation N • (diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt *
        diagonalLeft N m Δx Δt V) := by
  ext n n'
  simp only [stepMatrix, diagonalLeft, fourierMatrix, diagonalRight,
    Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [stepPhase_factorization, fourierPhase_comm N m Δx Δt n' n]
  ring

/-- The coefficient from a single input basis vector to an output position is exactly the
normalization times `stepPhase` with input first, fixing the basis-map convention of
[Zalka1998]. -/
theorem stepMatrix_basis_coefficient (m Δx Δt : ℝ) (V : ZMod N → ℝ)
    (input output : ZMod N) :
    (stepMatrix N m Δx Δt V *ᵥ Pi.single input (1 : ℂ)) output =
      stepNormalisation N * stepPhase N m Δx Δt V input output := by
  simp [Matrix.mulVec, dotProduct, stepMatrix, Pi.single_apply]

/-- The unnormalized cyclic Fourier matrix with entries given by the standard additive character
of `u * a * b`. -/
def twistedDFT (u : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun a b => ZMod.stdAddChar (u * a * b)

/-- Under the lattice relation `m * Δx ^ 2 / Δt = A * (2 * Real.pi / N)`, the bilinear phase
matrix equals the Fourier matrix twisted by `A` modulo `N`. -/
theorem fourierMatrix_eq_twistedDFT (m Δx Δt : ℝ) (A : ℕ)
    (hcond : m * Δx ^ 2 / Δt = (A : ℝ) * (2 * Real.pi / (N : ℝ))) :
    fourierMatrix N m Δx Δt = twistedDFT N (A : ZMod N) := by
  ext n n'
  simp only [fourierMatrix, fourierPhase, twistedDFT]
  have harg : m * (n.val : ℝ) * (n'.val : ℝ) * Δx ^ 2 / Δt =
      ((A : ℝ) * (2 * Real.pi / (N : ℝ))) * (n.val : ℝ) * (n'.val : ℝ) := by
    rw [← hcond]
    ring
  rw [harg]
  have hcast : (A : ZMod N) * (n : ZMod N) * (n' : ZMod N) =
      ((A * n.val * n'.val : ℕ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val n, ← ZMod.natCast_zmod_val n']
    push_cast
    ring
  rw [hcast]
  rw [show ((A * n.val * n'.val : ℕ) : ZMod N) =
      (((A * n.val * n'.val : ℕ) : ℤ) : ZMod N) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- The `(a, b)` entry of a twisted Fourier matrix times its conjugate transpose is `N` when `u
* (a - b) = 0`, and zero otherwise. -/
theorem twistedDFT_mul_star_apply (u : ZMod N) (a b : ZMod N) :
    (twistedDFT N u * star (twistedDFT N u)) a b =
      if u * (a - b) = 0 then (N : ℂ) else 0 := by
  rw [Matrix.mul_apply]
  have hR : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  have hterm : ∀ j : ZMod N,
      twistedDFT N u a j * star (twistedDFT N u) j b =
        ZMod.stdAddChar ((u * (a - b)) * j) := by
    intro j
    simp only [twistedDFT, Matrix.star_apply]
    have hs : star (ZMod.stdAddChar (u * b * j)) = ZMod.stdAddChar (-(u * b * j)) := by
      have h := AddChar.starComp_apply (R := ZMod N) (φ := ZMod.stdAddChar) hR (u * b * j)
      rw [AddChar.inv_apply', ← AddChar.map_neg_eq_inv] at h
      simpa only [starRingEnd_apply] using h
    rw [hs, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [show (∑ j : ZMod N, ZMod.stdAddChar ((u * (a - b)) * j)) =
      ∑ j : ZMod N, ZMod.stdAddChar (j * (u * (a - b))) by
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])]
  rw [AddChar.sum_mulShift (u * (a - b)) (ZMod.isPrimitive_stdAddChar N)]
  by_cases h : u * (a - b) = 0
  · rw [if_pos h, if_pos h, ZMod.card]
  · rw [if_neg h, if_neg h]
    simp

/-- If the twist is a unit modulo `N`, its Fourier matrix multiplied by its conjugate transpose
is `N` times the identity. -/
theorem twistedDFT_mul_star_of_isUnit (u : ZMod N) (hu : IsUnit u) :
    twistedDFT N u * star (twistedDFT N u) = (N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
  ext a b
  rw [twistedDFT_mul_star_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    have hzero : u * (a - a) = 0 := by rw [sub_self, mul_zero]
    rw [if_pos hzero, if_pos rfl, smul_eq_mul, mul_one]
  · have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hne : u * (a - b) ≠ 0 := by
      intro h
      exact hsub ((IsUnit.mul_right_eq_zero hu).mp h)
    rw [if_neg hne, if_neg hab, smul_zero]

/-- A diagonal matrix on `ZMod N` is unitary if each diagonal entry multiplied by its complex
conjugate equals one. -/
theorem diagonal_mem_unitaryGroup {d : ZMod N → ℂ} (hd : ∀ i, d i * star (d i) = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with hij
  · subst hij
    exact hd i
  · rfl

/-- For every real angle, `exp (I * θ)` multiplied by its complex conjugate equals one. -/
theorem exp_phase_mul_star (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) * star (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
  have hconj : star (Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.exp (-(Complex.I * (θ : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, ← Complex.exp_add]
  rw [show Complex.I * (θ : ℂ) + -(Complex.I * (θ : ℂ)) = 0 by ring]
  simp

/-- The diagonal matrix of input kinetic and potential phases is unitary. -/
theorem diagonalLeft_mem_unitaryGroup (m Δx Δt : ℝ) (V : ZMod N → ℝ) :
    diagonalLeft N m Δx Δt V ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro n
  exact exp_phase_mul_star _

/-- The diagonal matrix of output kinetic phases is unitary. -/
theorem diagonalRight_mem_unitaryGroup (m Δx Δt : ℝ) :
    diagonalRight N m Δx Δt ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro n
  exact exp_phase_mul_star _

/-- When the lattice coefficient corresponds to a unit `A` modulo `N`, the Fourier phase matrix
times its conjugate transpose equals `N` times the identity. -/
theorem fourierMatrix_mul_star (m Δx Δt : ℝ) (A : ℕ) (hu : IsUnit (A : ZMod N))
    (hcond : m * Δx ^ 2 / Δt = (A : ℝ) * (2 * Real.pi / (N : ℝ))) :
    fourierMatrix N m Δx Δt * star (fourierMatrix N m Δx Δt) =
      (N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
  rw [fourierMatrix_eq_twistedDFT N m Δx Δt A hcond]
  exact twistedDFT_mul_star_of_isUnit N (A : ZMod N) hu

/-- The squared complex modulus of the short-step normalization is the reciprocal of `N`. -/
theorem stepNormalisation_mul_star :
    stepNormalisation N * star (stepNormalisation N) = ((N : ℂ))⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hnorm : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    norm_cast
    rw [← pow_two, Real.sq_sqrt (le_of_lt hNpos)]
  unfold stepNormalisation
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← mul_inv, hnorm]

/-- The normalized short-step matrix is unitary when its lattice coefficient corresponds to an
invertible residue `A` modulo `N`. -/
theorem stepMatrix_mem_unitaryGroup (m Δx Δt : ℝ) (V : ZMod N → ℝ) (A : ℕ)
    (hu : IsUnit (A : ZMod N))
    (hcond : m * Δx ^ 2 / Δt = (A : ℝ) * (2 * Real.pi / (N : ℝ))) :
    stepMatrix N m Δx Δt V ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hD1 : diagonalRight N m Δx Δt * star (diagonalRight N m Δx Δt) = 1 := by
    have h := diagonalRight_mem_unitaryGroup N m Δx Δt
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hD2 : diagonalLeft N m Δx Δt V * star (diagonalLeft N m Δx Δt V) = 1 := by
    have h := diagonalLeft_mem_unitaryGroup N m Δx Δt V
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hF := fourierMatrix_mul_star N m Δx Δt A hu hcond
  rw [Matrix.mem_unitaryGroup_iff]
  rw [stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal]
  rw [star_smul, star_mul, star_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show star (stepNormalisation N) * stepNormalisation N = ((N : ℂ))⁻¹ by
    rw [mul_comm, stepNormalisation_mul_star]]
  have hinner :
      (diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt * diagonalLeft N m Δx Δt V) *
        (star (diagonalLeft N m Δx Δt V) *
          (star (fourierMatrix N m Δx Δt) * star (diagonalRight N m Δx Δt))) =
      (N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
    calc
      (diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt * diagonalLeft N m Δx Δt V) *
          (star (diagonalLeft N m Δx Δt V) *
            (star (fourierMatrix N m Δx Δt) * star (diagonalRight N m Δx Δt))) =
          diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt *
            (diagonalLeft N m Δx Δt V * star (diagonalLeft N m Δx Δt V)) *
              star (fourierMatrix N m Δx Δt) * star (diagonalRight N m Δx Δt) := by
        noncomm_ring
      _ = diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt * 1 *
              star (fourierMatrix N m Δx Δt) * star (diagonalRight N m Δx Δt) := by
        rw [hD2]
      _ = diagonalRight N m Δx Δt *
            (fourierMatrix N m Δx Δt * star (fourierMatrix N m Δx Δt)) *
              star (diagonalRight N m Δx Δt) := by
        noncomm_ring
      _ = diagonalRight N m Δx Δt *
            ((N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ)) *
              star (diagonalRight N m Δx Δt) := by
        rw [hF]
      _ = (N : ℂ) • (diagonalRight N m Δx Δt * star (diagonalRight N m Δx Δt)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
        rw [hD1]
  rw [hinner, smul_smul]
  have hN : ((N : ℂ)) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [show ((N : ℂ))⁻¹ * (N : ℂ) = 1 by field_simp]
  simp

/-- Under the compatible lattice relation with invertible `A`, packages the two-diagonal Fourier
factorization, identification with the `A`-twisted Fourier matrix, the unit-modulus diagonal
criterion, and short-step unitarity for [Zalka1998]. -/
theorem shortTimeStep_two_diagonal_and_fourier (m Δx Δt : ℝ) (V : ZMod N → ℝ) (A : ℕ)
    (hu : IsUnit (A : ZMod N))
    (hcond : m * Δx ^ 2 / Δt = (A : ℝ) * (2 * Real.pi / (N : ℝ))) :
    stepMatrix N m Δx Δt V =
        stepNormalisation N • (diagonalRight N m Δx Δt * fourierMatrix N m Δx Δt *
          diagonalLeft N m Δx Δt V) ∧
      fourierMatrix N m Δx Δt = twistedDFT N (A : ZMod N) ∧
      (∀ (d : ZMod N → ℂ), (∀ i, d i * star (d i) = 1) →
        Matrix.diagonal d ∈ Matrix.unitaryGroup (ZMod N) ℂ) ∧
      stepMatrix N m Δx Δt V ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  exact ⟨stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal N m Δx Δt V,
    fourierMatrix_eq_twistedDFT N m Δx Δt A hcond,
    fun d hd => diagonal_mem_unitaryGroup N hd,
    stepMatrix_mem_unitaryGroup N m Δx Δt V A hu hcond⟩

end Qatlib.Papers.QSystemSim96.MainResults
