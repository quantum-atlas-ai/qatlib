/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.GaussianPrimitives
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCoordinateTruncation
import Mathlib.Data.Nat.GCD.Basic

set_option backward.isDefEq.respectTransparency false

/-! The actual LCM point entering homogeneous_value. Integer coordinates are
computed by exact divisibility, never by a general rational truncation. This
input bridge does not assert Python/JSON execution or host runtime charges. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- Common positive denominator used by the actual source. -/
def rootSharedDenominator (c : ℚ×ℚ) : ℕ := Nat.lcm c.1.den c.2.den

/-- The exact integer numerator of x*D when the rational denominator divides D. -/
def rootScaledNumerator (x : ℚ) (D : ℕ) : ℤ := x.num*((D/x.den : ℕ) : ℤ)

/-- Construction for root Shared Numerator in the native root common denominator model. -/
def rootSharedNumerator (c : ℚ×ℚ) : GaussianDyadicScalar :=
  (rootScaledNumerator c.1 (rootSharedDenominator c),
    rootScaledNumerator c.2 (rootSharedDenominator c))

/-- The finite construction in `NativeRootCommonDenominator` satisfies `rootSharedDenominator_pos` under the displayed hypotheses. -/
theorem rootSharedDenominator_pos (c : ℚ×ℚ) : 0<rootSharedDenominator c := by
  apply Nat.pos_of_ne_zero
  simp [rootSharedDenominator]

/-- This is the integrality obligation BEFORE interpreting int(x*D). -/
theorem rootScaledNumerator_exact (x : ℚ) (D : ℕ) (h : x.den∣D) :
    (rootScaledNumerator x D : ℚ)=x*(D : ℚ) := by
  have hd : (x.den : ℚ)≠0 := by exact_mod_cast x.den_nz
  have hx : (x.num : ℚ)=x*(x.den : ℚ) := (div_eq_iff hd).mp x.num_div_den
  have hD : ((D/x.den : ℕ) : ℚ)*(x.den : ℚ)=(D : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel h)
  calc
    _ = (x.num : ℚ)*((D/x.den : ℕ) : ℚ) := by simp only [rootScaledNumerator,Int.cast_mul,Int.cast_natCast]
    _ = x*(((D/x.den : ℕ) : ℚ)*(x.den : ℚ)) := by rw [hx]; ring
    _ = x*(D : ℚ) := by rw [hD]

/-- The finite construction in `NativeRootCommonDenominator` satisfies `rootSharedNumerator_exact` under the displayed hypotheses. -/
theorem rootSharedNumerator_exact (c : ℚ×ℚ) :
    ((rootSharedNumerator c).1 : ℚ)=c.1*(rootSharedDenominator c : ℚ) ∧
    ((rootSharedNumerator c).2 : ℚ)=c.2*(rootSharedDenominator c : ℚ) := by
  exact ⟨rootScaledNumerator_exact _ _ (Nat.dvd_lcm_left _ _),
    rootScaledNumerator_exact _ _ (Nat.dvd_lcm_right _ _)⟩

/-- The SAME rational center, with its actual source common denominator. -/
theorem rootSharedPoint_value (c : ℚ×ℚ) :
    gaussianPointValue ⟨rootSharedNumerator c,rootSharedDenominator c⟩=
      rootRationalCoordinate c := by
  have hD : (rootSharedDenominator c : ℚ)≠0 := by
    exact_mod_cast (rootSharedDenominator_pos c).ne'
  have hre : ((rootSharedNumerator c).1 : ℚ)/(rootSharedDenominator c : ℚ)=c.1 := by
    rw [(rootSharedNumerator_exact c).1,mul_div_cancel_right₀ _ hD]
  have him : ((rootSharedNumerator c).2 : ℚ)/(rootSharedDenominator c : ℚ)=c.2 := by
    rw [(rootSharedNumerator_exact c).2,mul_div_cancel_right₀ _ hD]
  apply Complex.ext
  · have h : ((rootSharedNumerator c).1 : ℝ)/(rootSharedDenominator c : ℝ)=(c.1 : ℝ) := by
      exact_mod_cast hre
    simpa [gaussianPointValue,rootRationalCoordinate] using h
  · have h : ((rootSharedNumerator c).2 : ℝ)/(rootSharedDenominator c : ℝ)=(c.2 : ℝ) := by
      exact_mod_cast him
    simpa [gaussianPointValue,rootRationalCoordinate] using h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
