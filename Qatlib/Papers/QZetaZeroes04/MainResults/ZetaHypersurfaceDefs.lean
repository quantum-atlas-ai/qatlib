/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Spectral data for hypersurface zeta functions

This module packages the spectral parameters used for hypersurface zeta-function calculations in
[VanDam2004]. `ZetaHypersurface` stores field-size, degree, and dimension parameters, a positive
bounded root count, nonzero reciprocal-root parameters of prescribed norm, and a real parameter
`traceMean` bounded in absolute value by one.

The definitions `zetaRoot`, `eigenPhase`, and `zetaCircuit` invert and normalize the stored
spectral values to form a diagonal matrix. The affine expressions `firstPointCount` and
`pointCountEstimate` use the same projective-space baseline, and `HasPolynomialCostAnnotation`
records a polynomial bound on a size annotation for a unitary matrix.

## Main statements

* `rootRadius_pos`: positivity of the spectral radius for `q ≥ 2`.
* `ZetaHypersurface`: the input data and bounds for subsequent results.
* `zetaCircuit`: the diagonal matrix of normalized reciprocal roots.
* `HasPolynomialCostAnnotation`: existence of a polynomially bounded unitary size annotation.

## References

* [van Dam, 2004][VanDam2004]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs

open Matrix
open scoped BigOperators

/-- The real quotient `(q ^ (s * n) - 1) / (q ^ s - 1)` used as the projective-space baseline in
the point-count formulas. -/
def planeCount (q n s : ℕ) : ℝ := ((q : ℝ) ^ (s * n) - 1) / ((q : ℝ) ^ s - 1)

/-- The spectral scale `sqrt (q ^ (n - 1))`, with the exponent interpreted as natural-number
subtraction. -/
def rootRadius (q n : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ (n - 1))

/-- The spectral scale `rootRadius q n` is strictly positive whenever `q ≥ 2`. -/
theorem rootRadius_pos {q n : ℕ} (hq : 2 ≤ q) : 0 < rootRadius q n := by
  unfold rootRadius
  apply Real.sqrt_pos.mpr
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  exact pow_pos this _

/-- Spectral input data with `q, m ≥ 2`, `n ≥ 1`, a positive root count bounded by `m ^ n`,
nonzero complex values of norm `rootRadius q n`, and a real `traceMean` bounded by one in
absolute value. The structure stores these data and bounds for the later zeta and
point-count formulas. -/
structure ZetaHypersurface where

  q : ℕ

  q_ge_two : 2 ≤ q

  m : ℕ

  m_ge_two : 2 ≤ m

  n : ℕ

  n_ge_one : 1 ≤ n

  rootCount : ℕ

  rootCount_pos : 0 < rootCount

  rootCount_le : rootCount ≤ m ^ n

  alpha : Fin rootCount → ℂ

  alpha_ne_zero : ∀ j, alpha j ≠ 0

  alpha_norm : ∀ j, ‖alpha j‖ = rootRadius q n

  traceMean : ℝ

  traceMean_bound : |traceMean| ≤ 1

namespace ZetaHypersurface

variable (H : ZetaHypersurface)

/-- The reciprocal of the stored nonzero spectral value `H.alpha j`. -/
def zetaRoot (j : Fin H.rootCount) : ℂ := 1 / H.alpha j

/-- The complex value obtained by dividing `H.zetaRoot j` by its real norm, viewed as a complex
number. -/
def eigenPhase (j : Fin H.rootCount) : ℂ :=
  H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ)

/-- The square diagonal matrix whose diagonal entries are the normalized reciprocal-root values
`H.eigenPhase`. -/
def zetaCircuit : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ :=
  Matrix.diagonal H.eigenPhase

/-- The projective-space baseline `planeCount` specialized to the field-size and dimension
parameters of `H`. -/
def planeCountOf (s : ℕ) : ℝ := planeCount H.q H.n s

/-- The affine point-count expression equal to the projective-space baseline minus `(-1) ^ n`
times the spectral radius, root count, and stored real `traceMean`. -/
def firstPointCount : ℝ :=
  H.planeCountOf 1
    - (-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ) * H.traceMean

/-- The affine point-count estimate obtained by replacing `H.traceMean` with the supplied real
estimate in the formula for `firstPointCount`. -/
def pointCountEstimate (est : ℝ) : ℝ :=
  H.planeCountOf 1
    - (-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ) * est

end ZetaHypersurface

/-- A natural-number size annotation together with a matrix of the prescribed root-count
dimension and a proof that the matrix is unitary. -/
structure ZetaUnitaryCostAnnotation (H : ZetaHypersurface) where

  size : ℕ

  unitary : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ

  isUnitary : unitary ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ

/-- States that `U` has a unitary size annotation bounded by `c * ((Nat.log 2 H.q + 1) * (H.n *
(Nat.log 2 H.m + 1))) ^ k` for some positive natural numbers `c` and `k`. -/
def HasPolynomialCostAnnotation (H : ZetaHypersurface)
    (U : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ) : Prop :=
  ∃ (C : ZetaUnitaryCostAnnotation H) (c k : ℕ), 0 < c ∧ 0 < k ∧ C.unitary = U ∧
    C.size ≤ c * ((Nat.log 2 H.q + 1) * (H.n * (Nat.log 2 H.m + 1))) ^ k

end Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
