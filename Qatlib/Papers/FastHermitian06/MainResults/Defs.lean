/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Two-level PT-symmetric Hamiltonians

`State2` and `Mat2` provide the two-dimensional complex state and matrix types. The module
defines parity, entrywise conjugation, and the Hamiltonian `H2`, then establishes its PT
symmetry, centered square, trace, and determinant. See [BenderEtAl2007].

## Main statements

* `H2_pt_symmetric`: the Hamiltonian is fixed by `PT`.
* `H2_centered_sq`: its centered square is a scalar matrix.
* `omega_sq`: identifies the square of the gap parameter in the unbroken region.

## References

* [Bender et al., 2007][BenderEtAl2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

namespace Qatlib.Papers.FastHermitian06.MainResults.Defs

/-- The space of complex two-coordinate state vectors. -/
abbrev State2 := Fin 2 → ℂ

/-- The algebra of two-by-two complex matrices. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The first standard basis state `(1, 0)`. -/
def ket0 : State2 := ![1, 0]

/-- The second standard basis state `(0, 1)`. -/
def ket1 : State2 := ![0, 1]

/-- The parity matrix that swaps the two coordinates. -/
def parity : Mat2 := !![0, 1; 1, 0]

/-- Entrywise complex conjugation of a two-by-two matrix. -/
def conjT (M : Mat2) : Mat2 := M.map (starRingEnd ℂ)

/-- The transformation obtained by conjugating entries and multiplying by the parity matrix on
both sides. -/
def PT (M : Mat2) : Mat2 := parity * conjT M * parity

/-- The complex phase `exp (I * θ)` for a real angle `θ`. -/
def cis (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

/-- Expresses `cis θ` as `cos θ + I * sin θ`. -/
theorem cis_eq (θ : ℝ) :
    cis θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  unfold cis
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- Expresses `cis (-θ)` as `cos θ - I * sin θ`. -/
theorem cis_neg (θ : ℝ) :
    cis (-θ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [cis_eq]
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- The square of the imaginary unit is negative one. -/
theorem I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

/-- The phases at opposite real angles multiply to one. -/
theorem cis_mul_cis_neg (θ : ℝ) : cis θ * cis (-θ) = 1 := by
  unfold cis
  rw [← Complex.exp_add]
  have h : Complex.I * (θ : ℂ) + Complex.I * ((-θ : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero]

/-- Complex conjugation sends `cis θ` to `cis (-θ)`. -/
theorem conj_cis (θ : ℝ) : starRingEnd ℂ (cis θ) = cis (-θ) := by
  unfold cis
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

/-- The two-level Hamiltonian with diagonal entries `r * cis θ` and `r * cis (-θ)` and
off-diagonal entries `s`. -/
def H2 (r s θ : ℝ) : Mat2 :=
  !![(r : ℂ) * cis θ, (s : ℂ); (s : ℂ), (r : ℂ) * cis (-θ)]

/-- The real expression `4 * s^2 - 4 * r^2 * sin(θ)^2` for the squared gap. -/
def omegaSq (r s θ : ℝ) : ℝ := 4 * s ^ 2 - 4 * r ^ 2 * (Real.sin θ) ^ 2

/-- The nonnegative square root of `omegaSq r s θ`. -/
def omega (r s θ : ℝ) : ℝ := Real.sqrt (omegaSq r s θ)

/-- The condition that the squared gap `omegaSq r s θ` is strictly positive. -/
def unbrokenPT (r s θ : ℝ) : Prop := 0 < omegaSq r s θ

/-- The angle `arcsin ((r / s) * sin θ)`. -/
def alphaAngle (r s θ : ℝ) : ℝ := Real.arcsin ((r / s) * Real.sin θ)

/-- In the unbroken region, the square of `omega` is `omegaSq`. -/
theorem omega_sq (r s θ : ℝ) (h : unbrokenPT r s θ) :
    omega r s θ ^ 2 = omegaSq r s θ :=
  Real.sq_sqrt (le_of_lt h)

/-- The two-level Hamiltonian is fixed by the defined PT transformation. -/
theorem H2_pt_symmetric (r s θ : ℝ) : PT (H2 r s θ) = H2 r s θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PT, parity, conjT, H2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.map_apply, conj_cis, Complex.conj_ofReal]

/-- Subtracting `r * cos θ` times the identity from `H2` gives the displayed traceless matrix. -/
theorem H2_centered (r s θ : ℝ) :
    H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2)
      = !![ (Real.sin θ : ℂ) * (r : ℂ) * Complex.I, (s : ℂ);
            (s : ℂ), -((Real.sin θ : ℂ) * (r : ℂ) * Complex.I) ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, cis_eq, Matrix.smul_apply] <;>
    ring

/-- The square of the centered Hamiltonian is `(s^2 - r^2 * sin(θ)^2)` times the identity. -/
theorem H2_centered_sq (r s θ : ℝ) :
    (H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2)) *
        (H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2))
      = (((s : ℂ) ^ 2 - (r : ℂ) ^ 2 * (Real.sin θ) ^ 2)) • (1 : Mat2) := by
  rw [H2_centered]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  all_goals ring_nf
  all_goals rw [show Complex.I ^ 2 = (-1 : ℂ) from I_sq]
  all_goals ring

/-- The trace of `H2 r s θ` is `2 * r * cos θ`. -/
theorem H2_trace (r s θ : ℝ) :
    (H2 r s θ).trace = ((2 * r * Real.cos θ : ℝ) : ℂ) := by
  simp [H2, Matrix.trace, cis_eq, Fin.sum_univ_two]
  ring

/-- The determinant of `H2 r s θ` is `r^2 - s^2`. -/
theorem H2_det (r s θ : ℝ) : (H2 r s θ).det = ((r : ℂ) ^ 2 - (s : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp only [H2, Matrix.of_apply]
  have h : cis θ * cis (-θ) = 1 := cis_mul_cis_neg θ
  calc (r : ℂ) * cis θ * ((r : ℂ) * cis (-θ)) - (s : ℂ) * (s : ℂ)
      = (r : ℂ) ^ 2 * (cis θ * cis (-θ)) - (s : ℂ) ^ 2 := by ring
    _ = (r : ℂ) ^ 2 - (s : ℂ) ^ 2 := by rw [h]; ring

end Qatlib.Papers.FastHermitian06.MainResults.Defs
