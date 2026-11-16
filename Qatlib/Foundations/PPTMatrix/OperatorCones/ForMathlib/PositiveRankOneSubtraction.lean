/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Defs

@[expose] public section




/-!
# Positive rank-one subtraction along a range vector

If `A ≥ 0` and `u = A w ≠ 0`, subtracting `u u* / (w* A w)` preserves
positivity and strictly lowers rank. A direct congruence identity avoids any
invertibility assumption or choice of pseudoinverse. This is infrastructure for
finite rank descent in the qubit–qutrit PPT criterion, not that criterion itself.

Reuse: Mathlib's PSD quadratic-form zero criterion, positivity under congruence,
matrix outer-product multiplication, and finite-dimensional rank–nullity.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The residual after subtracting the sharp rank-one component in direction `A w`.
At a kernel vector, the inverse-zero convention leaves `A` unchanged. -/
noncomputable def rangeSubtraction (A : Matrix n n ℂ) (w : n → ℂ) : Matrix n n ℂ :=
  A - (star w ⬝ᵥ (A *ᵥ w))⁻¹ • vecMulVec (A *ᵥ w) (star (A *ᵥ w))

/-- The subtraction is an actual congruence of the positive matrix. -/
theorem rangeSubtraction_eq_congruence {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) :
    rangeSubtraction A w =
      (1 - (star w ⬝ᵥ (A *ᵥ w))⁻¹ • vecMulVec w (star (A *ᵥ w)))ᴴ * A *
        (1 - (star w ⬝ᵥ (A *ᵥ w))⁻¹ • vecMulVec w (star (A *ᵥ w))) := by
  let u := A *ᵥ w
  let q := star w ⬝ᵥ u
  let P := vecMulVec w (star u)
  let R := vecMulVec u (star u)
  have hqstar : star q = q := (hA.dotProduct_mulVec_nonneg w).star_eq
  have huTw : star u ⬝ᵥ w = q := by
    dsimp [u, q]
    rw [Matrix.star_mulVec, hA.isHermitian.eq, ← Matrix.dotProduct_mulVec]
  have hAP : A * P = R := by
    exact Matrix.mul_vecMulVec A w (star u)
  have hPA : Pᴴ * A = R := by
    have h := congrArg Matrix.conjTranspose hAP
    simpa only [Matrix.conjTranspose_mul, hA.isHermitian.eq, R,
      Matrix.conjTranspose_vecMulVec, star_star] using h
  have hPAP : Pᴴ * A * P = q • R := by
    rw [hPA]
    dsimp [R, P]
    rw [Matrix.vecMulVec_mul_vecMulVec, huTw]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRP : R * P = q • R := by
    calc
      R * P = (Pᴴ * A) * P := congrArg (fun M => M * P) hPA.symm
      _ = q • R := hPAP
  have hscalar : q⁻¹ * q⁻¹ * q = q⁻¹ := by
    by_cases hq : q = 0
    · simp [hq]
    · field_simp
  change A - q⁻¹ • R = (1 - q⁻¹ • P)ᴴ * A * (1 - q⁻¹ • P)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    star_inv₀, hqstar]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hAP, hPA, hRP, smul_smul, ← mul_assoc, hscalar]
  module

/-- The residual remains positive semidefinite, even for singular matrices. -/
theorem posSemidef_rangeSubtraction {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) : (rangeSubtraction A w).PosSemidef := by
  rw [rangeSubtraction_eq_congruence hA]
  exact hA.conjTranspose_mul_mul_same _

omit [DecidableEq n] in
/-- The sharp coefficient annihilates the chosen preimage when its image is nonzero. -/
theorem rangeSubtraction_mulVec_self {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (hw : A *ᵥ w ≠ 0) : rangeSubtraction A w *ᵥ w = 0 := by
  have hq : star w ⬝ᵥ (A *ᵥ w) ≠ 0 := by
    intro hq
    exact hw (hA.dotProduct_mulVec_zero_iff.mp hq)
  have huTw : star (A *ᵥ w) ⬝ᵥ w = star w ⬝ᵥ (A *ᵥ w) := by
    rw [Matrix.star_mulVec, hA.isHermitian.eq, ← Matrix.dotProduct_mulVec]
  ext i
  simp only [rangeSubtraction, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    op_smul_eq_smul, huTw]
  field_simp
  simp

omit [DecidableEq n] in
/-- Every old kernel vector stays in the kernel after the subtraction. -/
theorem ker_le_ker_rangeSubtraction {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) : A.mulVecLin.ker ≤ (rangeSubtraction A w).mulVecLin.ker := by
  intro z hz
  change A *ᵥ z = 0 at hz
  change rangeSubtraction A w *ᵥ z = 0
  have hdot : star (A *ᵥ w) ⬝ᵥ z = 0 := by
    rw [Matrix.star_mulVec, hA.isHermitian.eq, ← Matrix.dotProduct_mulVec, hz,
      dotProduct_zero]
  simp only [rangeSubtraction, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hz, hdot, op_smul_eq_smul, zero_smul, smul_zero, sub_zero]

omit [DecidableEq n] in
/-- At a nonzero range direction, subtraction strictly lowers the matrix rank. -/
theorem rank_rangeSubtraction_lt {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (hw : A *ᵥ w ≠ 0) : (rangeSubtraction A w).rank < A.rank := by
  have hker : A.mulVecLin.ker < (rangeSubtraction A w).mulVecLin.ker := by
    refine lt_iff_le_and_ne.mpr ⟨ker_le_ker_rangeSubtraction hA w, ?_⟩
    intro heq
    have hmem : w ∈ (rangeSubtraction A w).mulVecLin.ker :=
      rangeSubtraction_mulVec_self hA w hw
    rw [← heq] at hmem
    exact hw hmem
  have hdim := Submodule.finrank_lt_finrank_of_lt hker
  have hA' := A.mulVecLin.finrank_range_add_finrank_ker
  have hB' := (rangeSubtraction A w).mulVecLin.finrank_range_add_finrank_ker
  change Module.finrank ℂ (LinearMap.range (rangeSubtraction A w).mulVecLin) <
    Module.finrank ℂ (LinearMap.range A.mulVecLin)
  omega

end Qatlib.Foundations.PPTMatrix.OperatorCones
