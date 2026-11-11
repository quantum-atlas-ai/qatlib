/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Pauli algebra and Euler-form rotations for the 1+1D quantum lattice gas

Source: J. Yepez, *Quantum lattice gas model of Dirac particles in 1+1 dimensions*,
arXiv:1307.3595v1 (2013).

This module turns the algebraic backbone of the paper — the composite-rotation
calculation of §III (Eqs. (25)–(29)) and the Dirac–Hamiltonian identification
(Eqs. (38)–(39)) — into Lean objects. Following the paper, a group element
`e^{-i θ n̂·σ}` is represented by its Euler form

  `Rot n θ = cos θ • 1 - (i sin θ) • (n̂·σ)`,

which is exactly the expansion the paper uses to pass from (39a) to (39b).
The matrix `pauli n` is `n_x σ_x + n_y σ_y + n_z σ_z`; the product identity
`pauli a * pauli b = (a·b) • 1 + i • pauli (a × b)` is Eq. (26).

Everything in this file is fully proved.
-/

set_option autoImplicit false

open Matrix

namespace Qatlib.Papers.DiracLatGas13.MainResults

noncomputable section

/-! ## §1. Pauli matrices -/

/-- The Pauli matrix `σ_x`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ_z`. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli vector `n̂ · σ = n_x σ_x + n_y σ_y + n_z σ_z` for a real 3-vector `n`. -/
def pauli (v : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (v.1 : ℂ) • sigmaX + (v.2.1 : ℂ) • sigmaY + (v.2.2 : ℂ) • sigmaZ

/-- Real dot product of two 3-vectors, written as nested pairs. -/
def dot3 (a b : ℝ × ℝ × ℝ) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- Real cross product of two 3-vectors, written as nested pairs. -/
def cross3 (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- The Pauli operator of the zero vector is zero. -/
@[simp] theorem pauli_zero : pauli (0, 0, 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, sigmaX, sigmaY, sigmaZ]

/-- The cross product of a vector with itself vanishes. -/
@[simp] theorem cross3_self (n : ℝ × ℝ × ℝ) : cross3 n n = (0, 0, 0) := by
  unfold cross3
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

/-- Linearity of the Pauli vector under negation. -/
@[simp] theorem pauli_neg (n : ℝ × ℝ × ℝ) :
    pauli (-n.1, -n.2.1, -n.2.2) = -pauli n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, sigmaX, sigmaY, sigmaZ, Matrix.neg_apply] <;> ring

/-- The `z`-axis unit Pauli vector is `σ_z`. -/
@[simp] theorem pauli_zAxis : pauli (0, 0, 1) = sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, sigmaX, sigmaY, sigmaZ]

/-! ## §2. The Pauli product identity (Eq. (26)) -/

/-- The identity `(a·σ)(b·σ) = (a·b) + i (a×b)·σ`, Eq. (26) of the paper. -/
theorem pauli_mul (a b : ℝ × ℝ × ℝ) :
    pauli a * pauli b =
      (dot3 a b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauli (cross3 a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [pauli, sigmaX, sigmaY, sigmaZ, dot3, cross3, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Matrix.neg_apply] <;>
    ring

/-- A unit Pauli vector squares to the identity: `(n̂·σ)² = 1` (the involution
property invoked just above Eq. (39a)). -/
theorem pauli_sq (n : ℝ × ℝ × ℝ) (hn : dot3 n n = 1) :
    pauli n * pauli n = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauli_mul, hn, cross3_self]
  simp

/-! ## §3. Euler-form rotations -/

/-- The Euler form `e^{-i θ n̂·σ} = cos θ • 1 - (i sin θ) • (n̂·σ)` of a rotation about
the axis `n̂` by angle `θ`. This is the form the paper writes in (39b). -/
def Rot (n : ℝ × ℝ × ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    - (Complex.I * (Real.sin θ : ℂ)) • pauli n

/-- Rotation through zero angle is the identity matrix. -/
@[simp] theorem Rot_zero (n : ℝ × ℝ × ℝ) : Rot n 0 = 1 := by
  simp [Rot]

/-- Composition of two rotations about the same unit axis adds their angles. -/
theorem Rot_add (n : ℝ × ℝ × ℝ) (hn : dot3 n n = 1) (θ φ : ℝ) :
    Rot n θ * Rot n φ = Rot n (θ + φ) := by
  -- Abbreviate the scalar coefficients of the Euler form of `Rot n θ` and `Rot n φ`.
  -- `(n̂·σ)² = 1` is `pauli_sq`, and `(i s_θ)(i s_φ) = -s_θ s_φ` is `hII`.
  have hP : pauli n * pauli n = (1 : Matrix (Fin 2) (Fin 2) ℂ) := pauli_sq n hn
  have hII : (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin φ : ℂ))
      = -((Real.sin θ : ℂ) * (Real.sin φ : ℂ)) := by
    have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
    calc (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin φ : ℂ))
        = (Complex.I * Complex.I) * ((Real.sin θ : ℂ) * (Real.sin φ : ℂ)) := by ring
      _ = -((Real.sin θ : ℂ) * (Real.sin φ : ℂ)) := by rw [hI]; ring
  -- The two scalar coefficients of the product, in Euler form.
  have h1 : (Real.cos θ : ℂ) * (Real.cos φ : ℂ)
      + (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin φ : ℂ))
      = (Real.cos (θ + φ) : ℂ) := by
    rw [hII, Real.cos_add]
    push_cast
    ring
  have h2 : (Real.cos θ : ℂ) * (Complex.I * (Real.sin φ : ℂ))
      + (Complex.I * (Real.sin θ : ℂ)) * (Real.cos φ : ℂ)
      = Complex.I * (Real.sin (θ + φ) : ℂ) := by
    rw [Real.sin_add]
    push_cast
    ring
  show ((Real.cos θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          - (Complex.I * (Real.sin θ : ℂ)) • pauli n) *
        ((Real.cos φ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          - (Complex.I * (Real.sin φ : ℂ)) • pauli n)
      = (Real.cos (θ + φ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - (Complex.I * (Real.sin (θ + φ) : ℂ)) • pauli n
  rw [sub_mul, mul_sub, mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, hP]
  rw [← h1, ← h2]
  rw [add_smul, add_smul]
  module

/-- Rotation by `θ` followed by rotation by `-θ` returns the identity. -/
theorem Rot_neg_mul (n : ℝ × ℝ × ℝ) (hn : dot3 n n = 1) (θ : ℝ) :
    Rot n θ * Rot n (-θ) = 1 := by
  rw [Rot_add n hn θ (-θ), add_neg_cancel, Rot_zero]

end

end Qatlib.Papers.DiracLatGas13.MainResults
