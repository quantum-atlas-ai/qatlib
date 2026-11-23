module

public import Qatlib.Papers.QCounting98.MainResults.PlaneIsometryEuclidean
public import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

@[expose] public section

/-!
# Concrete consumer for the QCounting98 Euclidean plane isometry

The two-dimensional Fourier preparation `QFTMatrix 2` is unitary, and marking the second basis
state gives the prepared column squared good mass exactly `1 / 2`, so the good/bad angle is
`θ = π / 4`: non-degenerate with both plane generators non-zero. The examples invoke the
top-level Euclidean isometry, operator-norm, two-phase and rotation-exactness theorems on this
concrete instance.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.QCounting98PlaneIsometry

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Papers.QCounting98.MainResults.PlaneIsometryEuclidean

/-- The two-dimensional Fourier preparation. -/
def twoDimA : Matrix (Fin 2) (Fin 2) ℂ := QFTMatrix 2

/-- The Fourier matrix of size two is unitary. -/
theorem twoDimA_unitary : twoDimA * twoDimA.conjTranspose = 1 := by
  have h := qftMatrix_unitary (by norm_num : 0 < 2)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
  exact h

/-- Good mask marking the second basis state only. -/
def g2 : Fin 2 → Bool := fun i => decide (i = 1)

/-- The prepared column has squared good mass exactly one half. -/
theorem goodMass_twoDimA :
    ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i) = 1 / 2 := by
  have h0 : goodPart g2 (fun i => twoDimA i 0) (0 : Fin 2) = 0 := by
    simp [goodPart, g2]
  have h1 : goodPart g2 (fun i => twoDimA i 0) (1 : Fin 2) = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) := by
    simp [goodPart, g2, twoDimA, qftMatrix_apply]
  rw [Fin.sum_univ_two, h0, h1, Complex.normSq_zero, zero_add, Complex.normSq_inv,
    Complex.normSq_ofReal, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

/-- The non-degeneracy window for the good mass. -/
theorem goodMass_twoDimA_pos : 0 < ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i) := by
  rw [goodMass_twoDimA]
  norm_num

/-- The non-degeneracy window for the good mass. -/
theorem goodMass_twoDimA_lt_one :
    ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i) < 1 := by
  rw [goodMass_twoDimA]
  norm_num

/-- The angle identity `sin²(π / 4) = 1 / 2` for the concrete instance. -/
theorem sin_pi_div_four_sq_twoDimA :
    Real.sin (Real.pi / 4) ^ 2 = ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i) := by
  rw [goodMass_twoDimA, Real.sin_pi_div_four, div_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

/-- The sign-phase iterate preserves the Euclidean norm of the good projection. -/
example : ‖toEuclidean_fromVec
      ((iterate twoDimA g2 (-1) (-1)).mulVec (goodPart g2 (fun i => twoDimA i 0)))‖ =
    ‖toEuclidean_fromVec (goodPart g2 (fun i => twoDimA i 0))‖ :=
  signIterate_euclidean_norm twoDimA g2 twoDimA_unitary _

/-- The uniform isometry constant can be instantiated on the concrete plane vector. -/
example : ∃ C > 0, ‖toEuclidean_fromVec
      ((iterate twoDimA g2 (-1) (-1)).mulVec (goodPart g2 (fun i => twoDimA i 0)))‖ =
    C * ‖toEuclidean_fromVec (goodPart g2 (fun i => twoDimA i 0))‖ := by
  obtain ⟨C, hC, hbound⟩ := signIterate_plane_isometry_uniform
  refine ⟨C, hC, ?_⟩
  exact hbound 1 twoDimA g2 twoDimA_unitary _ (Submodule.subset_span (by simp))

open scoped Matrix.Norms.L2Operator in
/-- The `Matrix.Norms.L2Operator` operator norm of the concrete iterate is exactly one. -/
example : ‖(iterate twoDimA g2 (-1) (-1) : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 :=
  signIterate_l2_opNorm twoDimA g2 twoDimA_unitary

/-- The two-phase quadratic holds on the concrete plane with the good/bad angle `π / 4`. -/
example : ∀ w ∈ Submodule.span ℂ
      ({goodPart g2 (fun i => twoDimA i 0), badPart g2 (fun i => twoDimA i 0)} :
        Set (Fin 2 → ℂ)),
    ((iterate twoDimA g2 (-1) (-1)) ^ 2 -
      (2 * Real.cos (2 * (Real.pi / 4)) : ℂ) • iterate twoDimA g2 (-1) (-1) + 1).mulVec w = 0 :=
  signIterate_plane_eigenphase_relation twoDimA g2 twoDimA_unitary (Real.pi / 4)
    sin_pi_div_four_sq_twoDimA (by positivity) (by linarith [Real.pi_pos])
    goodMass_twoDimA_pos goodMass_twoDimA_lt_one

/-- The quadratic factorizes with the two Grover eigenphases at angle `π / 4`. -/
example (z : ℂ) : z ^ 2 - (2 * Real.cos (2 * (Real.pi / 4)) : ℂ) * z + 1 =
    (z - Complex.exp (2 * ((Real.pi / 4) : ℝ) * Complex.I)) *
      (z - Complex.exp (-(2 * ((Real.pi / 4) : ℝ) * Complex.I))) :=
  quadratic_two_phase_roots (Real.pi / 4) z

/-- The rotation formula holds with zero Euclidean error at the first iterate. -/
example : ‖toEuclidean_fromVec (((iterate twoDimA g2 (-1) (-1)) ^ 1).mulVec (fun i => twoDimA i 0)) -
    toEuclidean_fromVec
      ((((Real.sin ((2 * (1 : ℝ) + 1) * (Real.pi / 4)) /
          Real.sqrt (∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i))) : ℝ) : ℂ) •
        goodPart g2 (fun i => twoDimA i 0) +
      (((Real.cos ((2 * (1 : ℝ) + 1) * (Real.pi / 4)) /
          Real.sqrt (1 - ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i))) : ℝ) : ℂ) •
        badPart g2 (fun i => twoDimA i 0))‖ = 0 := by
  simpa using signIterate_rotation_euclidean_exact twoDimA g2 twoDimA_unitary (Real.pi / 4)
    (by positivity) (by linarith [Real.pi_pos]) sin_pi_div_four_sq_twoDimA
    goodMass_twoDimA_pos goodMass_twoDimA_lt_one 1

/-- The rotation error is uniformly bounded on the concrete instance. -/
example : ∃ C > 0, ∀ j : ℕ,
    ‖toEuclidean_fromVec (((iterate twoDimA g2 (-1) (-1)) ^ j).mulVec (fun i => twoDimA i 0)) -
      toEuclidean_fromVec
        ((((Real.sin ((2 * (j : ℝ) + 1) * (Real.pi / 4)) /
            Real.sqrt (∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i))) : ℝ) : ℂ) •
          goodPart g2 (fun i => twoDimA i 0) +
        (((Real.cos ((2 * (j : ℝ) + 1) * (Real.pi / 4)) /
            Real.sqrt (1 - ∑ i, Complex.normSq (goodPart g2 (fun i => twoDimA i 0) i))) : ℝ) : ℂ) •
          badPart g2 (fun i => twoDimA i 0))‖ ≤ C :=
  signIterate_rotation_euclidean_error_uniform twoDimA g2 twoDimA_unitary (Real.pi / 4)
    (by positivity) (by linarith [Real.pi_pos]) sin_pi_div_four_sq_twoDimA
    goodMass_twoDimA_pos goodMass_twoDimA_lt_one

#print axioms signIterate_mem_unitaryGroup
#print axioms signIterate_plane_isometry_uniform
#print axioms signIterate_l2_opNorm
#print axioms signIterate_plane_eigenphase_relation
#print axioms signIterate_rotation_euclidean_exact

end QatlibTests.QCounting98PlaneIsometry
