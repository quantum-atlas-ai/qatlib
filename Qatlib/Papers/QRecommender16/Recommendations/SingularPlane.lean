/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation.BireflectionFactorization
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The two eigenbranches of the singular-plane walk

In [KerenidisPrakash2017], Lemma 5.3, the two isometry images span a plane.
Take the second isometry image as the first axis, with the first image having
coordinates `(ρ, √(1 - ρ²))`. In this frame the reflection product has conjugate
complex eigenvalues whose real part is `2ρ² - 1`. The clean image basis vector
has a nonzero component on both branches when `0 < ρ < 1`.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open scoped BigOperators

/-- The real part of either singular-plane eigenvalue. -/
def rotationDiagonal (overlap : ℝ) : ℝ := 2 * overlap ^ 2 - 1

/-- The off-diagonal rotation coefficient in the normalized singular plane. -/
noncomputable def rotationOffDiagonal (overlap : ℝ) : ℝ :=
  2 * overlap * Real.sqrt (1 - overlap ^ 2)

/-- The two-dimensional restriction of the reflection product in the singular frame. -/
noncomputable def singularPlaneWalk (overlap : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun row column =>
    if row = column then (rotationDiagonal overlap : ℂ)
    else if row then (rotationOffDiagonal overlap : ℂ) else -(rotationOffDiagonal overlap : ℂ)

/-- A phase branch for a rotation, with the first coordinate fixed to one. -/
noncomputable def phaseBranch (negative : Bool) : Bool → ℂ := fun row =>
  if row then (if negative then Complex.I else -Complex.I) else 1

/-- The eigenvalue of the corresponding phase branch. -/
noncomputable def phaseEigenvalue (overlap : ℝ) (negative : Bool) : ℂ :=
  (rotationDiagonal overlap : ℂ) +
    (rotationOffDiagonal overlap : ℂ) * (if negative then -Complex.I else Complex.I)

/-- The two conjugate branches are eigenvectors of the real singular-plane rotation. -/
theorem singular_plane_eigenbranch (overlap : ℝ) (negative : Bool) :
    singularPlaneWalk overlap *ᵥ phaseBranch negative =
      phaseEigenvalue overlap negative • phaseBranch negative := by
  funext bit
  cases negative <;> cases bit <;>
    simp [singularPlaneWalk, phaseBranch, phaseEigenvalue, Matrix.mulVec, dotProduct] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- The first coordinate axis is the equal sum of the two phase eigenbranches, up to scale. -/
theorem phase_branches_average :
    (fun bit : Bool => (phaseBranch false bit + phaseBranch true bit) / 2) =
      (fun bit => if bit then (0 : ℂ) else 1) := by
  funext bit
  cases bit <;> norm_num [phaseBranch]

/-- Either phase branch gives the same nonnegative half-angle cosine. -/
theorem overlap_from_eigenvalue (overlap : ℝ) (h : 0 ≤ overlap) (negative : Bool) :
    Real.sqrt (((phaseEigenvalue overlap negative).re + 1) / 2) = overlap := by
  have hSquare : ((phaseEigenvalue overlap negative).re + 1) / 2 = overlap ^ 2 := by
    cases negative <;> simp [phaseEigenvalue, rotationDiagonal, Complex.mul_re] <;>
      ring_nf <;> simp [← Complex.ofReal_pow]
  rw [hSquare, Real.sqrt_sq h]

end Qatlib.Papers.QRecommender16.Recommendations
