/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.ResolventBound
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
open Qatlib.Foundations.OpCalculus.ContourCalc

open Qatlib.Concepts.CoherentSim.CoherentOAA

/-!
# Actual matrix resolvents and the inverse-word target

The Euclidean star-algebra equivalence transports the numerical-range inverse
to the matrix representation used by block encodings.  Moore--Penrose
uniqueness then identifies the actual resolvent with the existing inverse
word's pseudoinverse target.  This module does not yet construct that word
or certify its singular-value gap and normalization.
-/
namespace Qatlib.Concepts.MatrixContour.ContourCalc

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false


open scoped Matrix.Norms.L2Operator

/-- A two-sided inverse is the actual Moore--Penrose pseudoinverse. -/
theorem matrixPseudoinverse_eq_of_twoSidedInverse
    {I : Type*} [Fintype I] [DecidableEq I] (A R : Matrix I I ℂ)
    (hAR : A * R = 1) (hRA : R * A = 1) : matrixPseudoinverse A = R := by
  apply Eq.symm
  apply matrixPseudoinverse_unique A R
  · rw [hAR, Matrix.one_mul]
  · rw [hRA, Matrix.one_mul]
  · rw [hAR]; simp
  · rw [hRA]; simp

/-- G13: a genuine numerical-range certificate constructs a matrix resolvent,
including its norm and its equality with the pseudoinverse target. -/
theorem exists_matrix_resolvent_of_numericalRange_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖) :
    ∃ R : Matrix I I ℂ,
      (z • (1 : Matrix I I ℂ) - A) * R = 1 ∧
      R * (z • (1 : Matrix I I ℂ) - A) = 1 ∧
      ‖R‖ ≤ r⁻¹ ∧
      matrixPseudoinverse (z • (1 : Matrix I I ℂ) - A) = R := by
  let e := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  let Z : Matrix I I ℂ := z • 1 - A
  have heZ : e Z = shiftedOperator (e A) z := by
    simp [Z, shiftedOperator, map_sub, map_smul, map_one]
    rfl
  obtain ⟨S, hZS, hSZ, hnorm⟩ :=
    exists_resolvent_of_numericalRange_separation (e A) z r hr hsep
  let R : Matrix I I ℂ := e.symm S
  have heR : e R = S := e.apply_symm_apply S
  have hZR : Z * R = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    change e Z * e R = 1
    rw [heZ, heR]
    exact hZS
  have hRZ : R * Z = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    change e R * e Z = 1
    rw [heZ, heR]
    exact hSZ
  have hRnorm : ‖R‖ ≤ r⁻¹ := by
    change ‖e R‖ ≤ r⁻¹
    rw [heR]
    exact hnorm
  exact ⟨R, hZR, hRZ, hRnorm, matrixPseudoinverse_eq_of_twoSidedInverse Z R hZR hRZ⟩

end Qatlib.Concepts.MatrixContour.ContourCalc
