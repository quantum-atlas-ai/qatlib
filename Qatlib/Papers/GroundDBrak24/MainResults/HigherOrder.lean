/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GroundDBrak24.MainResults.HigherOrder

-- The `linfty` operator norm on square complex matrices, as used for the
-- matrix exponential and for measuring the conjugation defect.
noncomputable local instance instNormedAddCommGroupMatrix (D : ℕ) :
    NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance instNormedRingMatrix (D : ℕ) :
    NormedRing (Matrix (Fin D) (Fin D) ℂ) := Matrix.linftyOpNormedRing
noncomputable local instance instNormedAlgebraMatrix (D : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) := Matrix.linftyOpNormedAlgebra

/-- The golden-ratio conjugate `φ = (√5 − 1)/2` of Eq. (25). -/
def goldPhi : ℝ := (Real.sqrt 5 - 1) / 2

/-- Defining relation of `φ`, the algebraic heart of Eq. (25): `φ² + φ = 1`. -/
theorem goldPhi_sq_add : goldPhi ^ 2 + goldPhi = 1 := by
  unfold goldPhi
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- `φ = (√5 − 1)/2` is positive. -/
theorem goldPhi_pos : 0 < goldPhi := by
  unfold goldPhi
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [h5, h5n]

/-- `φ = (√5 − 1)/2` is less than one. -/
theorem goldPhi_lt_one : goldPhi < 1 := by
  unfold goldPhi
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [h5, h5n]

/-- `r = √s` squares to `s` for `s ≥ 0`, the step-scale relation of Eq. (25). -/
theorem step_scale_sq (s : ℝ) (hs : 0 ≤ s) : (Real.sqrt s) ^ 2 = s :=
  Real.sq_sqrt hs

/-- Operator evolution `e^{ⅈ r A}` as a granted primitive (matrix exponential in
the `linfty` operator norm). -/
def evo {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((Complex.I * r) • A)

/-- Real-exponent matrix exponential `e^{t A}`, used for the conjugation
`e^{s[D,H_k]}` on the right-hand side of Eq. (25). -/
def rexp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (t • A)

/-- The matrix commutator `[A, B] = A·B − B·A`. -/
def commutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- The operator norm `‖·‖` (the `linfty` norm local to this file). -/
def opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖A‖

/-- The higher-order DB-DOI step of Eq. (25),
`U_{k+1} = U_k e^{irφD} e^{irH_k} e^{-ir(φ+1)D} e^{-ir(1-φ)H_k} e^{irD}`,
with `r = √s` and `H_k = U_k† H_0 U_k`. -/
def hoStep {n : ℕ} (Uk H0 D : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let r : ℂ := ((Real.sqrt s : ℝ) : ℂ)
  let Hk : Matrix (Fin n) (Fin n) ℂ := star Uk * H0 * Uk
  let p : ℝ := goldPhi
  Uk * evo D (r * (p : ℂ)) * evo Hk r * evo D (-(r * ((p + 1 : ℝ) : ℂ)))
    * evo Hk (-(r * ((1 - p : ℝ) : ℂ))) * evo D r

/-- The conjugation defect of the higher-order step:
`U_{k+1}† H_0 U_{k+1} − e^{s[D,H_k]} (U_k† H_0 U_k) e^{-s[D,H_k]}`,
whose `O(s²)` norm bound is a separate assertion. -/
def hoDefect {n : ℕ} (H0 D Uk : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let Unext : Matrix (Fin n) (Fin n) ℂ := hoStep Uk H0 D s
  let Hk : Matrix (Fin n) (Fin n) ℂ := star Uk * H0 * Uk
  let C : Matrix (Fin n) (Fin n) ℂ := commutator D Hk
  star Unext * H0 * Unext - rexp C s * Hk * rexp C (-s)

end Qatlib.Papers.GroundDBrak24.MainResults.HigherOrder
